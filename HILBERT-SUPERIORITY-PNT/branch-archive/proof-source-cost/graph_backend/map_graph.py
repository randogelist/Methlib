#!/usr/bin/env python3
"""Union audited Lean declaration source ranges; never invokes Lean.

Each JSONL row is a declaration emitted by an external Lean graph exporter.
The exporter, not this script, owns discovery of dependencies and ranges.
Missing declarations/ranges/bodies are explicitly tracked; nothing here proves
that the exporter observed the whole proof graph.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

MODULE_RE = re.compile(r"^[\w']+(?:\.[\w']+)*$", re.UNICODE)
INCOMPLETE_BODY = {"missing", "unavailable", "unknown", "hidden", "error", "not_loaded"}


def pair(text: str, label: str) -> tuple[str, str]:
    if '=' not in text:
        raise ValueError(f"{label}: expected KEY=VALUE")
    a, b = text.split('=', 1)
    if not a or not b:
        raise ValueError(f"{label}: empty key or value")
    return a, b


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def module_path(module: str) -> str:
    if not MODULE_RE.fullmatch(module):
        raise ValueError('invalid or missing module')
    return module.replace('.', '/') + '.lean'


def source_candidates(module: str, row: dict, roots: list[tuple[str, Path]], file_cache: dict):
    relstr = row.get('source_path') or module_path(module)
    rel = Path(relstr)
    if rel.is_absolute() or '..' in rel.parts or rel.suffix != '.lean':
        raise ValueError('source path is not a safe relative .lean path')
    # Respect an optional exporter origin tag when available; roots must be
    # explicitly configured. This avoids attributing local files to Mathlib.
    hint = row.get('origin')
    candidates = []
    for category, base in roots:
        if hint and category != hint:
            continue
        p = (base / rel).resolve()
        if not p.is_relative_to(base) or not p.is_file():
            continue
        if p not in file_cache:
            data = p.read_bytes()
            file_cache[p] = (data, sha(data))
        data, digest = file_cache[p]
        candidates.append((category, p, data, digest, rel.as_posix()))
    if not candidates:
        return None, 'source_file_not_found'
    # Even identical bytes at different categories are ambiguous attribution.
    signatures = {(c, h) for c, _, _, h, _ in candidates}
    if len(signatures) != 1:
        return None, 'ambiguous_source'
    return candidates[0], None


def choose_range(row: dict, nlines: int, convention: str):
    if convention == 'auto':
        convention = row.get('_range_convention', 'inclusive')
    a, b = row.get('start_line'), row.get('end_line')
    if type(a) is not int or type(b) is not int:
        return None, 'missing_range'
    if a <= 0 or b <= 0:
        return None, 'missing_range'
    # Lean stores an exclusive end Position; when its zero-based column is 0,
    # the end line itself is not covered by the declaration. The caller may
    # instead export already-inclusive end lines with --range-convention.
    if convention == 'lean-end-exclusive':
        col = row.get('end_col')
        if type(col) is not int or col < 0:
            return None, 'missing_or_invalid_end_col'
        if col == 0:
            b -= 1
    if a < 1 or b < a or b > nlines:
        return None, 'range_out_of_bounds'
    return (a, b), None


def parse_int_or_none(value: str):
    return int(value) if value.isdigit() else None


def load_graph(path: Path, label: str):
    rows, names, summary = [], set(), None
    for lineno, raw in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        if not raw.strip():
            continue
        # External CI logs may prefix stdout with timestamps and interleave
        # controls, warnings, and summaries. Do not count those as constants.
        if 'GRAPH_SUMMARY|' in raw:
            values = raw[raw.index('GRAPH_SUMMARY|'):].split('|')
            if len(values) >= 8 and values[1] == label:
                if summary is not None:
                    raise ValueError(f'{path}:{lineno}: duplicate graph summary')
                fields = ['count', 'missing', 'hidden', 'unknown_module',
                          'missing_range', 'axioms']
                summary = {k: parse_int_or_none(v.strip())
                           for k, v in zip(fields, values[2:8])}
            continue
        if 'GRAPH_MISSING|' in raw:
            values = raw[raw.index('GRAPH_MISSING|'):].split('|')
            if len(values) < 3:
                raise ValueError(f'{path}:{lineno}: truncated GRAPH_MISSING')
            if values[1] != label:
                continue
            row = {'root': values[1], 'name': values[2].strip(), 'module': None,
                   'kind': 'missing_declaration', 'body_status': 'missing'}
        elif 'GRAPH_CONST|' in raw:
            values = raw[raw.index('GRAPH_CONST|'):].split('|')
            if len(values) < 5:
                raise ValueError(f'{path}:{lineno}: truncated GRAPH_CONST')
            if values[1] != label:
                continue
            # Format: root | name | module | kind | startLine | startColumn |
            # endLine | endColumn. End position is Lean's exclusive position.
            values += [''] * max(0, 9 - len(values))
            row = {'root': values[1], 'name': values[2], 'module': values[3],
                   'kind': values[4], 'start_line': parse_int_or_none(values[5]),
                   'start_col': parse_int_or_none(values[6]),
                   'end_line': parse_int_or_none(values[7]),
                   'end_col': parse_int_or_none(values[8].strip()),
                   '_range_convention': 'lean-end-exclusive'}
        elif raw.lstrip().startswith('{'):
            try:
                row = json.loads(raw)
            except json.JSONDecodeError as exc:
                raise ValueError(f'{path}:{lineno}: invalid JSON: {exc}') from exc
            if row.get('root') not in (None, label):
                continue
        else:
            continue
        if not isinstance(row, dict) or not isinstance(row.get('name'), str) or not row['name']:
            raise ValueError(f'{path}:{lineno}: expected object with nonempty name')
        if row['name'] in names:
            raise ValueError(f'{path}:{lineno}: duplicate declaration {row["name"]}')
        names.add(row['name'])
        rows.append(row)
    if not rows:
        raise ValueError(f'{path}: empty graph')
    if summary is not None and summary['count'] is not None and summary['count'] != len(rows):
        raise ValueError(f'{path}: GRAPH_SUMMARY count {summary["count"]} != {len(rows)} rows')
    return rows, summary


def summarize(label: str, declaration: str, graph: Path, roots, convention):
    rows, exporter_summary = load_graph(graph, declaration)
    issues, issues_detail = Counter(), []
    body_counts, kind_counts, categories = Counter(), Counter(), Counter()
    by_file = {}
    resolution_cache, file_cache, lines_cache = {}, {}, {}
    for row in rows:
        name, module = row['name'], row.get('module')
        kind = row.get('kind') or 'unknown'
        body = row.get('body_status') or 'unknown'
        kind_counts[kind] += 1
        body_counts[body] += 1
        if body in INCOMPLETE_BODY and kind not in ('axiom', 'axiomInfo'):
            issues['body_' + body] += 1
        start, end = row.get('start_line'), row.get('end_line')
        if (type(start) is not int or type(end) is not int or start <= 0 or end <= 0):
            issues['missing_range'] += 1
            issues_detail.append({'name': name, 'module': module, 'reason': 'missing_range'})
            if not isinstance(module, str) or not module or module == '_unknown':
                issues['missing_module'] += 1
            continue
        if not isinstance(module, str) or not module or module == '_unknown':
            issues['missing_module'] += 1
            issues_detail.append({'name': name, 'reason': 'missing_module'})
            continue
        try:
            cache_key = (module, row.get('source_path'), row.get('origin'))
            if cache_key not in resolution_cache:
                resolution_cache[cache_key] = source_candidates(module, row, roots, file_cache)
            candidate, problem = resolution_cache[cache_key]
        except (ValueError, TypeError) as exc:
            candidate, problem = None, str(exc)
        if problem:
            issues[problem] += 1
            issues_detail.append({'name': name, 'module': module, 'reason': problem})
            continue
        category, path, data, digest, rel = candidate
        categories[category] += 1
        try:
            if path not in lines_cache:
                lines_cache[path] = data.decode('utf-8').splitlines()
            source_lines = lines_cache[path]
        except UnicodeDecodeError:
            issues['source_not_utf8'] += 1
            issues_detail.append({'name': name, 'module': module, 'reason': 'source_not_utf8'})
            continue
        span, problem = choose_range(row, len(source_lines), convention)
        if problem:
            issues[problem] += 1
            issues_detail.append({'name': name, 'module': module, 'reason': problem})
            continue
        key = (category, rel, digest)
        file = by_file.setdefault(key, {'path': str(path), 'lines': set(), 'nonblank': set(),
                                        'declarations': set()})
        file['declarations'].add(name)
        for no in range(span[0], span[1] + 1):
            file['lines'].add(no)
            if source_lines[no - 1].strip():
                file['nonblank'].add(no)
    per_category = defaultdict(lambda: {'declarations_mapped_to_range': 0,
                                       'unique_lines': 0, 'unique_nonblank_lines': 0,
                                       'source_files': 0})
    files_json = []
    for (cat, rel, digest), f in sorted(by_file.items()):
        c = per_category[cat]
        c['declarations_mapped_to_range'] += len(f['declarations'])
        c['unique_lines'] += len(f['lines'])
        c['unique_nonblank_lines'] += len(f['nonblank'])
        c['source_files'] += 1
        files_json.append({'category': cat, 'relative_path': rel, 'sha256': digest,
                           'path': f['path'], 'unique_lines': len(f['lines']),
                           'unique_nonblank_lines': len(f['nonblank']),
                           'declarations': len(f['declarations'])})
    out = {'root': label, 'declaration': declaration, 'graph_file': str(graph),
           'graph_sha256': sha(graph.read_bytes()),
           'rows': len(rows), 'exporter_summary': exporter_summary,
           'kinds': dict(kind_counts), 'body_status': dict(body_counts),
           'source_category_resolved': dict(categories), 'issues': dict(issues),
           'unmapped_examples': issues_detail[:100], 'categories': dict(per_category),
           'files': files_json,
           'completeness': 'UNVERIFIED: graph exporter coverage and source provenance must be checked independently'}
    return out, by_file


def compare(old, new):
    # A changed file's identical line number is not the same line. Shared and
    # unique figures count only files whose complete bytes/hash agree.
    out = defaultdict(lambda: Counter())
    old_by_path = {(c, p): (h, v) for (c, p, h), v in old.items()}
    new_by_path = {(c, p): (h, v) for (c, p, h), v in new.items()}
    for category, path in sorted(old_by_path.keys() | new_by_path.keys()):
        a, b = old_by_path.get((category, path)), new_by_path.get((category, path))
        report = out[category]
        if a and b and a[0] == b[0]:
            report['shared_unchanged_file_lines'] += len(a[1]['lines'] & b[1]['lines'])
            report['old_only_unchanged_file_lines'] += len(a[1]['lines'] - b[1]['lines'])
            report['new_only_unchanged_file_lines'] += len(b[1]['lines'] - a[1]['lines'])
        elif a and b:
            report['changed_file_count'] += 1
            report['old_lines_in_changed_files'] += len(a[1]['lines'])
            report['new_lines_in_changed_files'] += len(b[1]['lines'])
        elif a:
            report['only_old_file_lines'] += len(a[1]['lines'])
        else:
            report['only_new_file_lines'] += len(b[1]['lines'])
    return {k: dict(v) for k, v in sorted(out.items())}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--graph', action='append', required=True, metavar='LABEL=JSONL')
    ap.add_argument('--root', action='append', default=[], metavar='LABEL=DECLARATION',
                    help='actual exported root name; defaults to LABEL')
    ap.add_argument('--source-root', action='append', required=True,
                    metavar='LABEL:CATEGORY=DIR',
                    help='repeat; category examples: Mathlib, Lean, HVR, Dependency')
    ap.add_argument('--range-convention', choices=['auto', 'inclusive', 'lean-end-exclusive'],
                    default='auto', help='auto: JSON inclusive, GRAPH_CONST uses Lean end position')
    ap.add_argument('--output', type=Path, required=True)
    ns = ap.parse_args()
    roots = defaultdict(list)
    for item in ns.source_root:
        key, path = pair(item, '--source-root')
        if ':' not in key:
            raise ValueError('source-root key must be LABEL:CATEGORY')
        label, category = key.split(':', 1)
        if not label or not category:
            raise ValueError('source-root label/category is empty')
        p = Path(path).resolve(strict=True)
        if not p.is_dir():
            raise ValueError(f'not a directory: {p}')
        roots[label].append((category, p))
    root_declarations = {}
    for arg in ns.root:
        label, declaration = pair(arg, '--root')
        if label in root_declarations:
            raise ValueError(f'duplicate root label: {label}')
        root_declarations[label] = declaration
    summaries, graphs = [], {}
    for arg in ns.graph:
        label, path = pair(arg, '--graph')
        if label in graphs or not roots[label]:
            raise ValueError(f'duplicate graph label or missing source roots: {label}')
        summary, files = summarize(label, root_declarations.get(label, label),
                                   Path(path).resolve(strict=True), roots[label], ns.range_convention)
        summaries.append(summary)
        graphs[label] = files
    result = {'schema': 1, 'range_convention': ns.range_convention, 'roots': summaries,
              'note': 'Counts are source spans of exporter-reached declarations, not proven complete LOC-to-axioms.'}
    if len(summaries) == 2:
        a, b = summaries[0]['root'], summaries[1]['root']
        result['comparison'] = {'old': a, 'new': b, 'per_category': compare(graphs[a], graphs[b])}
    ns.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print('GRAPH_COUNT=' + str(len(summaries)))
    for s in summaries:
        print('ROOT=' + s['root'] + ' DECLARATIONS=' + str(s['rows']) +
              ' MAPPING_ISSUES=' + json.dumps(s['issues'], sort_keys=True))
    print('COVERAGE=UNVERIFIED')
    print('OUTPUT=' + str(ns.output))


if __name__ == '__main__':
    main()
