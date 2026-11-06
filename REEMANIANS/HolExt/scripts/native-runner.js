/* Native Windows WSH JScript; source preparation is not compiler evidence.
 * Only the native execution below can emit PASS or a closure marker.
 * This file exports the pure audit/parser core to Node for non-Lean self-tests.
 */
(function (host) {
  function failure(message) { throw new Error(message); }
  function trim(s) { return String(s).replace(/^\s+|\s+$/g, ""); }
  function own(o, k) { return Object.prototype.hasOwnProperty.call(o, k); }
  function jsonParse(input) {
    var s = String(input).replace(/^\uFEFF/, ""), p = 0;
    function ws() { while (p < s.length && /\s/.test(s.charAt(p))) ++p; }
    function bad() { failure("JSON_PARSE_ERROR_AT=" + p); }
    function str() {
      if (s.charAt(p++) !== '"') bad();
      var out = "";
      while (p < s.length) {
        var c = s.charAt(p++);
        if (c === '"') return out;
        if (c === "\\") {
          c = s.charAt(p++);
          var escapes = {'"':'"', '\\':'\\', '/':'/', b:'\b', f:'\f', n:'\n', r:'\r', t:'\t'};
          if (own(escapes, c)) out += escapes[c];
          else if (c === "u") {
            var h = s.substr(p, 4);
            if (!/^[0-9a-fA-F]{4}$/.test(h)) bad();
            out += String.fromCharCode(parseInt(h, 16)); p += 4;
          } else bad();
        } else { if (c.charCodeAt(0) < 32) bad(); out += c; }
      }
      bad();
    }
    function value() {
      ws(); var c = s.charAt(p), a, k, v, m;
      if (c === '"') return str();
      if (c === "{") {
        ++p; a = {}; ws();
        if (s.charAt(p) === "}") { ++p; return a; }
        while (true) {
          ws(); if (s.charAt(p) !== '"') bad(); k = str();
          if (k === "__proto__" || k === "constructor" || own(a, k)) bad();
          ws(); if (s.charAt(p++) !== ":") bad(); v = value(); a[k] = v; ws();
          c = s.charAt(p++); if (c === "}") return a; if (c !== ",") bad();
        }
      }
      if (c === "[") {
        ++p; a = []; ws();
        if (s.charAt(p) === "]") { ++p; return a; }
        while (true) { a.push(value()); ws(); c = s.charAt(p++); if (c === "]") return a; if (c !== ",") bad(); }
      }
      if (s.substr(p, 4) === "true") { p += 4; return true; }
      if (s.substr(p, 5) === "false") { p += 5; return false; }
      if (s.substr(p, 4) === "null") { p += 4; return null; }
      m = /^-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?/.exec(s.substr(p));
      if (m) { p += m[0].length; v = Number(m[0]); if (!isFinite(v)) bad(); return v; }
      bad();
    }
    var result = value(); ws(); if (p !== s.length) bad(); return result;
  }
  function jsonStringify(v) {
    function str(s) {
      return '"' + String(s).replace(/[\\"\u0000-\u001f]/g, function (c) {
        var esc = {'"':'\\"', '\\':'\\\\', '\b':'\\b', '\f':'\\f', '\n':'\\n', '\r':'\\r', '\t':'\\t'};
        if (own(esc, c)) return esc[c];
        return "\\u" + ("0000" + c.charCodeAt(0).toString(16)).slice(-4);
      }) + '"';
    }
    if (v === null) return "null";
    if (typeof v === "string") return str(v);
    if (typeof v === "number") { if (!isFinite(v)) failure("JSON_NONFINITE_NUMBER"); return String(v); }
    if (typeof v === "boolean") return v ? "true" : "false";
    var a = [], i, keys = [];
    if (Object.prototype.toString.call(v) === "[object Array]") {
      for (i = 0; i < v.length; ++i) a.push(jsonStringify(v[i]));
      return "[" + a.join(",") + "]";
    }
    if (typeof v === "object") {
      for (i in v) if (own(v, i)) keys.push(i);
      keys.sort();
      for (i = 0; i < keys.length; ++i) a.push(str(keys[i]) + ":" + jsonStringify(v[keys[i]]));
      return "{" + a.join(",") + "}";
    }
    failure("JSON_UNSUPPORTED_VALUE");
  }
  function stripLeanCommentsAndStrings(s) {
    var out = [], i = 0, depth = 0, line = false, quoted = false;
    while (i < s.length) {
      var c = s.charAt(i), d = s.charAt(i + 1);
      if (line) {
        if (c === "\n") { line = false; out.push("\n"); } else out.push(" ");
        ++i; continue;
      }
      if (depth) {
        if (c === "/" && d === "-") { ++depth; out.push("  "); i += 2; }
        else if (c === "-" && d === "/") { --depth; out.push("  "); i += 2; }
        else { out.push(c === "\n" ? "\n" : " "); ++i; }
        continue;
      }
      if (quoted) {
        if (c === "\\") { out.push("  "); i += 2; }
        else { if (c === '"') quoted = false; out.push(c === "\n" ? "\n" : " "); ++i; }
        continue;
      }
      if (c === "/" && d === "-") { depth = 1; out.push("  "); i += 2; }
      else if (c === "-" && d === "-") { line = true; out.push("  "); i += 2; }
      else if (c === '"') { quoted = true; out.push(" "); ++i; }
      else { out.push(c); ++i; }
    }
    if (depth || quoted) failure("LEAN_SOURCE_UNTERMINATED_COMMENT_OR_STRING");
    return out.join("");
  }
  function validName(n) { return /^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(n); }
  function leanImports(s) {
    var clean = stripLeanCommentsAndStrings(s), lines = clean.split(/\r?\n/), out = [], seen = {};
    for (var i = 0; i < lines.length; ++i) {
      var m = /^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$/.exec(lines[i]);
      if (!m) continue;
      var ns = m[1].split(/\s+/);
      for (var j = 0; j < ns.length; ++j) {
        if (!validName(ns[j])) failure("UNSUPPORTED_IMPORT_SYNTAX=" + lines[i]);
        if (!own(seen, ns[j])) { out.push(ns[j]); seen[ns[j]] = true; }
      }
    }
    return out;
  }
  function scanEscapes(s, name) {
    var clean = stripLeanCommentsAndStrings(s);
    if (/\b(?:sorry|admit|sorryAx|native_decide)\b/.test(clean)) failure("PROOF_ESCAPE_IN=" + name);
    if (/(?:^|\n)\s*(?:(?:private|protected|public)\s+)*axiom\s/.test(clean)) failure("ADDED_AXIOM_IN=" + name);
  }
  function auditTag(which, index) { return "HXY_AXIOM_" + which + "_" + index + "_ENDMARK"; }
  function taggedAudit(name, index) {
    if (!validName(name)) failure("INVALID_AUDIT_DECLARATION=" + name);
    return '#eval "' + auditTag("BEGIN", index) + '"\n#print axioms ' + name +
      '\n#eval "' + auditTag("END", index) + '"\n';
  }
  function printedAxiomReferences(list, declaration) {
    var raw = [], start = 0, braces = 0;
    if (!trim(list)) return raw;
    function append(end) {
      var atom = trim(list.substring(start, end));
      if (!atom) failure("AXIOM_AUDIT_EMPTY_REFERENCE=" + declaration);
      raw.push(atom);
    }
    for (var i = 0; i < list.length; ++i) {
      var c = list.charAt(i);
      if (c === "{") {
        if (braces) failure("AXIOM_AUDIT_MALFORMED_UNIVERSES=" + declaration);
        braces = 1;
      } else if (c === "}") {
        if (!braces) failure("AXIOM_AUDIT_MALFORMED_UNIVERSES=" + declaration);
        braces = 0;
      } else if (c === "," && !braces) { append(i); start = i + 1; }
    }
    if (braces) failure("AXIOM_AUDIT_MALFORMED_UNIVERSES=" + declaration);
    append(list.length);
    return raw;
  }
  function canonicalPrintedAxiom(reference, declaration) {
    // Native JScript may return "" for a nonparticipating capture. Branch on
    // the complete syntax instead; every capture below is mandatory.
    if (validName(reference)) return reference;
    var m = /^([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\.\{([^{}]+)\}$/.exec(reference);
    if (!m) failure("AXIOM_AUDIT_MALFORMED_REFERENCE=" + reference + " DECL=" + declaration);
    // Lean 4.33 #print axioms uses ofConstName: levels are the declaration's
    // own named parameters (PrettyPrinter.ppConstNameWithInfos), not terms.
    var levels = m[2].split(",");
    for (var i = 0; i < levels.length; ++i) {
      var level = trim(levels[i]);
      if (!validName(level) || /^(?:_|max|imax|Prop|Type|Sort)$/.test(level))
        failure("AXIOM_AUDIT_MALFORMED_UNIVERSES=" + reference + " DECL=" + declaration);
    }
    return m[1];
  }
  function auditCheck(contents, names) {
    if (/\bsorryAx\b/.test(contents)) failure("AXIOM_AUDIT_SORRYAX");
    var cursor = 0, reports = [];
    for (var j = 0; j < names.length; ++j) {
      var begin = auditTag("BEGIN", j), end = auditTag("END", j);
      var a = contents.indexOf(begin);
      if (a < 0) failure("AXIOM_AUDIT_MISSING_BEGIN=" + names[j]);
      if (contents.indexOf(begin, a + begin.length) >= 0) failure("AXIOM_AUDIT_DUPLICATE_BEGIN=" + names[j]);
      if (a < cursor) failure("AXIOM_AUDIT_MARKER_ORDER=" + names[j]);
      var b = contents.indexOf(end);
      if (b < 0) failure("AXIOM_AUDIT_MISSING_END=" + names[j]);
      if (contents.indexOf(end, b + end.length) >= 0) failure("AXIOM_AUDIT_DUPLICATE_END=" + names[j]);
      if (b < a + begin.length) failure("AXIOM_AUDIT_MARKER_ORDER=" + names[j]);
      var section = trim(contents.substring(a + begin.length, b));
      // #eval prints the marker strings in quotes. Remove exactly the two
      // boundary quote fragments; every other character must form one report.
      if (section.charAt(0) === '"' && section.charAt(section.length - 1) === '"')
        section = trim(section.substring(1, section.length - 1));
      var m = /^'([^']+)'\s+depends\s+on\s+axioms\s*:\s*\[([\s\S]*?)\]$/.exec(section);
      var list = "";
      if (m) list = m[2];
      else m = /^'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms$/.exec(section);
      if (!m) failure("AXIOM_AUDIT_REPORT_COUNT=" + names[j]);
      var actual = trim(m[1]).replace(/^_root_\./, "");
      var expected = names[j].replace(/^_root_\./, "");
      if (actual !== expected) failure("AXIOM_AUDIT_WRONG_DECLARATION=" + actual + " EXPECTED=" + expected);
      var atoms = [], raw = printedAxiomReferences(list, expected);
      for (var k = 0; k < raw.length; ++k) {
        var atom = canonicalPrintedAxiom(raw[k], expected);
        if (atom !== "propext" && atom !== "Classical.choice" && atom !== "Quot.sound")
          failure("AXIOM_AUDIT_UNAPPROVED=" + atom + " PRINTED=" + raw[k] + " DECL=" + expected);
        atoms.push(atom);
      }
      reports.push({declaration: expected, axioms: atoms, printedAxioms: raw, rawReport: section});
      cursor = b + end.length;
    }
    return reports;
  }
  function trustedReceiptMatches(prior, expected, artifacts) {
    return !!(prior && prior.compilation === "PASS" && prior.key && prior.artifactMetadata && artifacts &&
      prior.key.schema === "HXY_TRUSTED_TEXT_MODULE_2" &&
      typeof prior.generation === "string" && prior.generation.length > 0 &&
      jsonStringify(prior.key) === jsonStringify(expected) &&
      jsonStringify(prior.artifactMetadata) === jsonStringify(artifacts));
  }
  function legacyReceiptCanMigrate(prior, context) {
    function no(reason) { return {allowed:false,reason:reason}; }
    if (!prior || !prior.key || prior.key.schema !== "HXY_NATIVE_MODULE_1") return no("NOT_LEGACY_SCHEMA");
    if (context.cacheFamily !== "HXY_THREE_SPACES_433") return no("WRONG_CACHE_FAMILY");
    if (prior.compilation !== "PASS" || prior.key.module !== context.module) return no("LEGACY_COMPILE_OR_MODULE_MISMATCH");
    if (!/^[a-f0-9]{64}$/.test(context.packagedSourceSha256Label || "") ||
        prior.key.sourceSha256 !== context.packagedSourceSha256Label) return no("SOURCE_LABEL_MISMATCH");
    if (context.sourceBytes !== context.packagedSourceBytes) return no("SOURCE_SIZE_DIFFERS_FROM_PACKAGE_LABEL");
    if (!context.artifactMetadata || !context.artifactMetadata[".olean"] || !prior.artifacts ||
        !/^[a-f0-9]{64}$/.test(prior.artifacts[".olean"] || "")) return no("MISSING_LEGACY_ARTIFACT");
    for (var suffix in prior.artifacts) if (own(prior.artifacts,suffix) && !context.artifactMetadata[suffix])
      return no("MISSING_LEGACY_COMPANION=" + suffix);
    if (!/^[a-f0-9]{64}$/.test(prior.key.environmentSha256 || "")) return no("MISSING_LEGACY_ENVIRONMENT_LABEL");
    var scopes=[prior,prior.key,prior.environment,prior.key.environment];
    for (var si=0;si<scopes.length;++si) {
      var scope=scopes[si]; if (!scope) continue;
      if (typeof scope.leanVersion !== "undefined" &&
          !/(?:^|version )4\.33\.0(?:$|,|\s)/.test(String(scope.leanVersion))) return no("EXPLICIT_LEGACY_VERSION_CONFLICT");
      if (typeof scope.leanToolchain !== "undefined" && scope.leanToolchain!=="leanprover/lean4:v4.33.0")
        return no("EXPLICIT_LEGACY_TOOLCHAIN_CONFLICT");
      if (typeof scope.toolchain !== "undefined" && scope.toolchain!=="leanprover/lean4:v4.33.0")
        return no("EXPLICIT_LEGACY_TOOLCHAIN_CONFLICT");
      if (typeof scope.mathlibRev !== "undefined" && scope.mathlibRev!==context.mathlibRev)
        return no("EXPLICIT_LEGACY_MATHLIB_CONFLICT");
    }
    var oldDeps=prior.key.dependencies;
    if (!oldDeps || oldDeps.length!==context.dependencies.length) return no("DEPENDENCY_LIST_CHANGED");
    for (var i=0;i<oldDeps.length;++i) {
      var old=oldDeps[i], cur=context.dependencies[i];
      if (!old || old.module!==cur.module) return no("DEPENDENCY_ORDER_CHANGED");
      if (cur.kind==="project") {
        if (cur.compiledFresh) return no("DEPENDENCY_COMPILED_FRESH=" + cur.module);
        if (old.sourceSha256!==cur.packagedSourceSha256Label) return no("DEPENDENCY_SOURCE_LABEL_CHANGED=" + cur.module);
        if (!old.artifacts || !cur.legacyOrigin || !cur.legacyOrigin.artifactSha256Labels ||
            cur.legacyOrigin.environmentSha256Label!==prior.key.environmentSha256 ||
            jsonStringify(old.artifacts)!==jsonStringify(cur.legacyOrigin.artifactSha256Labels))
          return no("DEPENDENCY_LEGACY_ARTIFACT_IDENTITY_UNAVAILABLE=" + cur.module);
      } else if (cur.kind==="external") {
        if (typeof old.base!=="string" || old.base.toLowerCase()!==cur.base.toLowerCase())
          return no("EXTERNAL_CACHE_LOCATION_CHANGED=" + cur.module);
        if (!old.artifacts || !old.artifacts[".olean"]) return no("EXTERNAL_LEGACY_ARTIFACT_LABEL_MISSING=" + cur.module);
      } else return no("UNKNOWN_DEPENDENCY_KIND");
    }
    return {allowed:true,reason:"USER_TRUSTED_LEGACY_433_SOURCE_LABELS"};
  }
  var core = {jsonParse: jsonParse, jsonStringify: jsonStringify, leanImports: leanImports,
    stripLeanCommentsAndStrings: stripLeanCommentsAndStrings, scanEscapes: scanEscapes,
    validName: validName, auditTag: auditTag, taggedAudit: taggedAudit, auditCheck: auditCheck,
    trustedReceiptMatches:trustedReceiptMatches,legacyReceiptCanMigrate:legacyReceiptCanMigrate};
  if (typeof module !== "undefined" && module.exports) module.exports = core;
  host.HXYRunnerCore = core;
}(this));

if (typeof WScript !== "undefined") (function () {
  var C = HXYRunnerCore;
  var fso = new ActiveXObject("Scripting.FileSystemObject");
  var shell = new ActiveXObject("WScript.Shell");
  var env = shell.Environment("PROCESS");
  var packageDir = fso.GetParentFolderName(fso.GetParentFolderName(WScript.ScriptFullName));
  shell.CurrentDirectory = packageDir;
  var evidence="",buildLog="",auditLog="",runId="",cacheDir="",importsDir="",receiptDir="";
  var cacheLock="",lockHeld=false,lean="",sysroot="",jobCount="16",force=false,selection="all";
  var config=null,environmentIdentity=null,packageLabels={},sourceInputs={},observedFiles={};
  var moduleState={},moduleRecords={},moduleReceipts={},moduleFresh={},externalRecords={},externalRoots=[];
  var compiled=0,reused=0,migrated=0;
  var results={schema:"HXY_THREE_SPACES_TRUSTED_EVIDENCE_2",environmentPolicy:"TRUSTED_FAST_V2",
    runtimeHashing:"NONE",status:"STARTED",candidates:[]};
  function fail(s) { throw new Error(s); }
  function errorText(e) { return e.description || e.message || String(e); }
  function getenv(n) { return String(env(n)) || ""; }
  function exists(p) { return fso.FileExists(p); }
  function dirExists(p) { return fso.FolderExists(p); }
  function full(p) { return fso.GetAbsolutePathName(p); }
  function same(a,b) { return C.jsonStringify(a)===C.jsonStringify(b); }
  function mkdirs(p) {
    if (!p || dirExists(p)) return;
    var parent=fso.GetParentFolderName(p); if (parent && parent!==p) mkdirs(parent);
    fso.CreateFolder(p);
  }
  function remove(p) { if (exists(p)) fso.DeleteFile(p,true); }
  function metadata(p) {
    var f=fso.GetFile(p);
    return {size:Number(f.Size),modified:String(f.DateLastModified)};
  }
  function observe(p) {
    var record={path:full(p),metadata:metadata(p)};
    observedFiles[record.path.toLowerCase()]=record; return record.metadata;
  }
  function readUtf8(p) {
    var stream=new ActiveXObject("ADODB.Stream"); stream.Type=2; stream.Charset="utf-8";
    stream.Open(); stream.LoadFromFile(p); var s=stream.ReadText(); stream.Close();
    return s.replace(/^\uFEFF/,"");
  }
  function readObserved(p) { var s=readUtf8(p); observe(p); return s; }
  function writeUtf8(p,text) {
    mkdirs(fso.GetParentFolderName(p));
    var input=new ActiveXObject("ADODB.Stream"); input.Type=2; input.Charset="utf-8";
    input.Open(); input.WriteText(text); input.Position=0; input.Type=1;
    if (input.Size>=3) input.Position=3;
    var output=new ActiveXObject("ADODB.Stream"); output.Type=1; output.Open(); input.CopyTo(output);
    output.SaveToFile(p,2); output.Close(); input.Close();
  }
  function writeJson(p,data) { writeUtf8(p,C.jsonStringify(data)+"\n"); }
  function readJson(p) { return C.jsonParse(readUtf8(p)); }
  function readObservedJson(p) { return C.jsonParse(readObserved(p)); }
  function say(s) {
    if (buildLog) writeUtf8(buildLog,(exists(buildLog)?readUtf8(buildLog):"")+s+"\r\n");
    WScript.Echo(s);
  }
  function quote(s) {
    s=String(s); if (/["\r\n%]/.test(s)) fail("UNSUPPORTED_COMMAND_PATH="+s);
    return '"'+s+'"';
  }
  function execute(command,logPath) {
    mkdirs(fso.GetParentFolderName(logPath)); remove(logPath);
    var comspec=getenv("COMSPEC") || (getenv("SystemRoot")+"\\System32\\cmd.exe");
    return shell.Run(quote(comspec)+' /d /v:off /s /c "'+command+' > '+quote(logPath)+' 2>&1"',0,true);
  }
  function safeRel(p) {
    if (!/^[A-Za-z0-9_./'-]+$/.test(p) || /(^|\/)\.\.(\/|$)/.test(p) || /^[/.]/.test(p))
      fail("INVALID_PACKAGE_RELATIVE_PATH="+p);
    return p.replace(/\//g,"\\");
  }
  function moduleRel(name) { if (!C.validName(name)) fail("INVALID_MODULE="+name); return name.replace(/\./g,"/")+".lean"; }
  function sourcePath(name) { return packageDir+"\\"+safeRel(moduleRel(name)); }
  function artifactBase(name) { return importsDir+"\\"+name.replace(/\./g,"\\"); }
  function artifactFiles(base) {
    var suffixes=[".olean",".olean.private",".olean.server",".ilean",".ir"], out=[];
    for (var i=0;i<suffixes.length;++i) if (exists(base+suffixes[i])) out.push(base+suffixes[i]);
    return out;
  }
  function artifactMetadata(base,recordObservation) {
    if (!exists(base+".olean")) fail("MISSING_OLEAN="+base);
    var files=artifactFiles(base), out={};
    for (var i=0;i<files.length;++i) out[files[i].substring(base.length)]=
      recordObservation?observe(files[i]):metadata(files[i]);
    return out;
  }
  function clearArtifacts(base) {
    var files=artifactFiles(base);
    for (var i=0;i<files.length;++i) { delete observedFiles[full(files[i]).toLowerCase()]; remove(files[i]); }
  }
  function addSourceLabels(entries,kind) {
    for (var i=0;i<entries.length;++i) {
      var item=entries[i], rel=String(item.path).replace(/\\/g,"/"); safeRel(rel);
      if (packageLabels[rel] || !/^[a-f0-9]{64}$/.test(item.sha256) || typeof item.bytes!=="number")
        fail("INVALID_PACKAGE_SOURCE_LABEL="+rel);
      packageLabels[rel]={kind:kind,packagedSha256Label:item.sha256,packagedBytes:item.bytes};
    }
  }
  function loadConfig() {
    config=readObservedJson(packageDir+"\\runner-manifest.json");
    if (config.schema!=="HXY_THREE_SPACES_NATIVE_TRUSTED_2" || config.environmentPolicy!=="TRUSTED_FAST_V2" ||
        config.cacheFamily!=="HXY_THREE_SPACES_433" || config.leanVersion!=="4.33.0" ||
        config.leanToolchain!=="leanprover/lean4:v4.33.0" ||
        config.mathlibRev!=="db584cd6d46c92f209a44c0f1c829460d327499d" ||
        config.frozenCommit!=="c6b95fd9e3d792270026da083bddddbc72bacb22") fail("FROZEN_RUNNER_CONFIGURATION_MISMATCH");
    var fixed=["HXYThreeSpaces.BanachExt","HXYThreeSpaces.HilbertRep","HXYThreeSpaces.HolExt"];
    if (!config.candidates || config.candidates.length!==3) fail("FROZEN_CANDIDATE_COUNT_MISMATCH");
    for (var i=0;i<3;++i) {
      var c=config.candidates[i]; c.forwardModule=c.forwardModule || c.module;
      c.equivalenceModule=c.equivalenceModule || c.module;
      if (c.id!=="C"+(i+1) || c.predicate!==fixed[i] || !C.validName(c.forwardModule) ||
          !C.validName(c.equivalenceModule) || !C.validName(c.forward) || !C.validName(c.equivalence))
        fail("FROZEN_CANDIDATE_SCOPE_MISMATCH="+i);
    }
    var frozen=readObservedJson(packageDir+"\\"+safeRel(config.frozenManifest));
    if (frozen.commit!==config.frozenCommit || !frozen.sources || !frozen.sources.length) fail("FROZEN_SOURCE_MANIFEST_MISMATCH");
    addSourceLabels(frozen.sources,"frozen");
    var next=readObservedJson(packageDir+"\\provenance\\new-sources.json");
    if (!next.sources || next.sources.length!==9) fail("NEW_SOURCE_MANIFEST_EXPECTS_NINE_FILES");
    var expectedNew={"HXYThreeSpaces/BanachForward.lean":true,"HXYThreeSpaces/Banach.lean":true,
      "HXYThreeSpaces/HilbertForward.lean":true,"HXYThreeSpaces/Hilbert.lean":true,
      "HXYThreeSpaces/HolomorphicForward.lean":true,"HXYThreeSpaces/Holomorphic.lean":true,
      "HXYThreeSpaces/HXY.lean":true,"HXYThreeSpaces/Main.lean":true,
      "HXY_THREE_FUNCTION_SPACE_EQUIVALENCES.lean":true};
    for (i=0;i<next.sources.length;++i) if (!expectedNew[next.sources[i].path]) fail("UNEXPECTED_NEW_SOURCE="+next.sources[i].path);
    addSourceLabels(next.sources,"new");
    observe(WScript.ScriptFullName);
    results.package=config.package; results.frozenCommit=config.frozenCommit;
    results.sourceManifestPolicy="PACKAGED_LABELS_TRUSTED_NOT_REHASHED";
    say("SOURCE_MANIFEST_LABELS=LOADED|FROZEN="+frozen.sources.length+"|NEW="+next.sources.length);
    say("SOURCE_RECEIPT_IDENTITY=EXACT_UTF8_TEXT");
  }
  function checkPackageRevisions(cacheRoot) {
    var actual=readObservedJson(cacheRoot+"\\lake-manifest.json"), packages={}, a=actual.packages || [];
    for (var i=0;i<a.length;++i) packages[a[i].name]=a[i].rev;
    var pinned=readObservedJson(packageDir+"\\provenance\\ci\\dependency-pins.json"), pins=pinned.packages;
    if (pinned.toolchain!==config.leanToolchain || !pins || pins.mathlib!==config.mathlibRev) fail("DEPENDENCY_PINS_MANIFEST_MISMATCH");
    for (var n in pins) if (Object.prototype.hasOwnProperty.call(pins,n) && packages[n]!==pins[n])
      fail("CACHED_DEPENDENCY_REVISION_MISMATCH="+n);
    return pins;
  }
  function selectEnvironment() {
    lean=getenv("HXY_LEAN_EXE") || getenv("LEAN_EXE") || getenv("AWPIRH_LEAN_EXE");
    if (!lean) lean=(getenv("ELAN_HOME") || (getenv("USERPROFILE")+"\\.elan"))+
      "\\toolchains\\leanprover--lean4---v4.33.0\\bin\\lean.exe";
    lean=full(lean.replace(/^"|"$/g,"")); if (!exists(lean)) fail("LEAN_4_33_NATIVE_COMPILER_MISSING="+lean);
    sysroot=fso.GetParentFolderName(fso.GetParentFolderName(lean));
    env("LEAN_PATH")=""; env("LEAN_SRC_PATH")=""; env("LEAN_SYSROOT")=sysroot;
    jobCount=getenv("LEAN_THREADS") || getenv("LEAN_JOBS") || "16";
    if (!/^[1-9][0-9]*$/.test(jobCount)) fail("INVALID_THREAD_COUNT="+jobCount);
    var versionLog=evidence+"\\lean-version.log";
    if (execute(quote(lean)+" --version",versionLog)!==0) fail("LEAN_VERSION_COMMAND_FAILED");
    var version=readUtf8(versionLog).replace(/\s+$/,"");
    if (!/version 4\.33\.0(?:,|\s)/.test(version) || version.indexOf("x86_64-w64-windows")<0)
      fail("NATIVE_WINDOWS_LEAN_4_33_REQUIRED="+version.replace(/\s+/g," "));
    say(version);
    var cacheRoot=getenv("MATHLIB_CACHE_ROOT") || getenv("RH_MATHLIB_ROOT") ||
      (getenv("USERPROFILE")+"\\lean-native\\awpi_phi_rh_lean_sieved_v0_1_1");
    cacheRoot=full(cacheRoot.replace(/^"|"$/g,""));
    var packagesDir=cacheRoot+"\\.lake\\packages";
    if (!dirExists(packagesDir)) fail("CACHED_PACKAGES_DIRECTORY_MISSING="+packagesDir);
    if (!exists(packagesDir+"\\mathlib\\.lake\\build\\lib\\lean\\Mathlib.olean")) fail("PRECOMPILED_MATHLIB_MISSING");
    var pins=checkPackageRevisions(cacheRoot);
    var subs=new Enumerator(fso.GetFolder(packagesDir).SubFolders), paths=[];
    for (;!subs.atEnd();subs.moveNext()) {
      var p=String(subs.item().Path)+"\\.lake\\build\\lib\\lean";
      if (dirExists(p)) paths.push(p);
    }
    paths.sort(); externalRoots=paths; externalRoots.push(sysroot+"\\lib\\lean");
    env("LEAN_PATH")=[importsDir].concat(externalRoots).join(";"); env("LEAN_NUM_THREADS")=jobCount;
    environmentIdentity={schema:"HXY_TRUSTED_FAST_ENV_2",leanExecutable:lean,leanVersion:version,
      leanToolchain:config.leanToolchain,mathlibCacheRoot:cacheRoot,mathlibRev:config.mathlibRev,
      packageRevisions:pins,externalImportRoots:externalRoots,compilerOptions:{maxHeartbeats:4000000,maxRecDepth:4096}};
    results.environment=environmentIdentity;
    writeJson(evidence+"\\environment.json",environmentIdentity);
    say("ENVIRONMENT=TRUSTED_FAST_V2"); say("RUNTIME_HASHING=NONE");
    say("RECURSIVE_EXTERNAL_CACHE_SCAN=NONE"); say("MATHLIB_CACHE="+cacheRoot);
    say("DEPENDENCY_DOWNLOAD=DISABLED"); say("MATHLIB_REBUILD=DISABLED");
  }
  function resolveExternal(name) {
    if (externalRecords[name]) return externalRecords[name];
    var rel=name.replace(/\./g,"\\"), found=[];
    for (var i=0;i<externalRoots.length;++i) {
      var base=externalRoots[i]+"\\"+rel;
      if (exists(base+".olean")) found.push(base);
    }
    if (found.length!==1) fail("EXTERNAL_IMPORT_RESOLUTION="+name+"|MATCHES="+found.length);
    var record={kind:"external",module:name,base:found[0],artifactMetadata:artifactMetadata(found[0],true)};
    externalRecords[name]=record; return record;
  }
  function readSource(name) {
    if (sourceInputs[name]) return sourceInputs[name];
    var rel=moduleRel(name), label=packageLabels[rel];
    if (!label) fail("UNMANIFESTED_PROJECT_SOURCE="+rel);
    var p=sourcePath(name), text=readObserved(p), meta=metadata(p);
    C.scanEscapes(text,rel);
    var input={module:name,path:rel,text:text,metadata:meta,packagedSha256Label:label.packagedSha256Label,
      packagedBytes:label.packagedBytes,imports:C.leanImports(text)};
    sourceInputs[name]=input; return input;
  }
  function runLean(args,logPath) {
    var rc=execute(quote(lean)+" -j"+jobCount+" -DmaxHeartbeats=4000000 -DmaxRecDepth=4096 "+args,logPath);
    if (rc!==0) {
      say("LEAN_EXIT="+rc+"|LOG="+logPath); if (exists(logPath)) say(readUtf8(logPath).slice(-16000));
      fail("LEAN_COMPILATION_FAILED="+logPath);
    }
    if (!exists(logPath)) fail("LEAN_LOG_MISSING="+logPath); return readUtf8(logPath);
  }
  function legacyContext(name,input,deps,artifacts) {
    var context={module:name,cacheFamily:config.cacheFamily,mathlibRev:config.mathlibRev,
      packagedSourceSha256Label:input.packagedSha256Label,sourceBytes:input.metadata.size,
      packagedSourceBytes:input.packagedBytes,artifactMetadata:artifacts,dependencies:[]};
    for (var i=0;i<deps.length;++i) {
      var d=deps[i], item={module:d.module,kind:d.kind};
      if (d.kind==="project") {
        item.packagedSourceSha256Label=sourceInputs[d.module].packagedSha256Label;
        item.compiledFresh=!!moduleFresh[d.module]; item.legacyOrigin=moduleReceipts[d.module].legacyOrigin || null;
      } else item.base=d.base;
      context.dependencies.push(item);
    }
    return context;
  }
  function buildModule(name) {
    if (moduleState[name]==="PASS") return moduleRecords[name];
    if (moduleState[name]==="FAIL") fail("DEPENDENCY_PREVIOUSLY_FAILED="+name);
    if (moduleState[name]==="ACTIVE") fail("CYCLIC_PROJECT_IMPORT="+name);
    var src=sourcePath(name);
    if (!exists(src)) {
      if (packageLabels[moduleRel(name)]) fail("PACKAGED_SOURCE_MISSING="+name);
      return resolveExternal(name);
    }
    moduleState[name]="ACTIVE";
    try {
      var input=readSource(name), deps=[];
      for (var i=0;i<input.imports.length;++i) deps.push(buildModule(input.imports[i]));
      var base=artifactBase(name), rpath=receiptDir+"\\"+name.replace(/\./g,"\\")+".json";
      var expected={schema:"HXY_TRUSTED_TEXT_MODULE_2",module:name,sourceText:input.text,
        environment:environmentIdentity,dependencies:deps};
      var prior=null, current=null;
      if (exists(rpath)) { try { prior=readJson(rpath); } catch (_) {} }
      if (exists(base+".olean")) current=artifactMetadata(base,false);
      var matched=!force && current && C.trustedReceiptMatches(prior,expected,current);
      if (matched) { ++reused; moduleFresh[name]=false; say("MODULE_CACHE_HIT="+name); }
      else {
        var migration=!force && current ? C.legacyReceiptCanMigrate(prior,legacyContext(name,input,deps,current)) :
          {allowed:false,reason:"NO_REUSABLE_ARTIFACT_OR_FORCE"};
        if (migration.allowed) {
          var origin={schema:"HXY_NATIVE_MODULE_1",sourceSha256Label:prior.key.sourceSha256,
            environmentSha256Label:prior.key.environmentSha256,artifactSha256Labels:prior.artifacts};
          prior={key:expected,compilation:"PASS",compilationOrigin:"LEGACY_NATIVE_COMPILE_TRUSTED_MIGRATION",
            artifactMetadata:current,generation:runId+"|migration|"+name,legacyOrigin:origin,
            migrationAssumption:"User-trusted original HXY_NATIVE_MODULE_1 native Lean4.33 environment and packaged source-label correspondence; labels not rehashed."};
          writeJson(rpath,prior); ++migrated; moduleFresh[name]=false;
          say("MODULE_CACHE_MIGRATED="+name+"|TRUSTED_LEGACY_433");
        } else {
          if (prior && prior.key && prior.key.schema==="HXY_NATIVE_MODULE_1")
            say("LEGACY_RECOMPILE_REQUIRED="+name+"|"+migration.reason);
          remove(rpath); clearArtifacts(base); mkdirs(fso.GetParentFolderName(base));
          say("COMPILE="+name);
          var log=evidence+"\\compile\\"+name+".log";
          runLean("-o "+quote(base+".olean")+" "+quote(safeRel(input.path)),log);
          if (!same(metadata(src),input.metadata)) fail("SOURCE_CHANGED_DURING_COMPILATION="+name);
          prior={key:expected,compilation:"PASS",compilationOrigin:"FRESH_NATIVE_COMPILATION",
            artifactMetadata:artifactMetadata(base,false),generation:runId+"|compile|"+name,
            compilerLog:log,compilerLogMetadata:metadata(log)};
          writeJson(rpath,prior); ++compiled; moduleFresh[name]=true; say("COMPILE_PASS="+name);
        }
      }
      var observed=artifactMetadata(base,true);
      var record={kind:"project",module:name,generation:prior.generation,artifactMetadata:observed};
      moduleState[name]="PASS"; moduleRecords[name]=record; moduleReceipts[name]=prior; return record;
    } catch (e) { moduleState[name]="FAIL"; throw e; }
  }
  function auditEndpoint(candidate,kind) {
    var theorem=kind==="forward"?candidate.forward:candidate.equivalence;
    var mod=kind==="forward"?candidate.forwardModule:candidate.equivalenceModule;
    var type=kind==="forward"?"(_root_.RiemannHypothesis -> "+candidate.predicate+")":
      "(Iff _root_.RiemannHypothesis "+candidate.predicate+")";
    return auditExact(candidate.id,kind,mod,theorem,type);
  }
  function auditExact(id,kind,mod,provided,expectedType) {
    var wrapper="HXYThreeSpacesAudit."+id+"_"+kind+"_exact";
    var source="import "+mod+"\n\nset_option autoImplicit false\nset_option pp.universes true\n\n"+
      "theorem "+wrapper+" : "+expectedType+" :=\n  "+provided+"\n\n"+
      "#check "+wrapper+"\n#check "+provided+"\n"+C.taggedAudit(provided,0)+C.taggedAudit(wrapper,1);
    var stem=id+"_"+kind, src=evidence+"\\audit\\"+stem+".lean";
    var out=evidence+"\\audit\\"+stem+".log", obj=evidence+"\\audit\\"+stem+".olean";
    writeUtf8(src,source);
    var log=runLean("-o "+quote(obj)+" "+quote(src),out);
    var reports=C.auditCheck(log,[provided,wrapper]);
    if (!exists(obj)) fail("EXACT_TYPE_AUDIT_OLEAN_MISSING="+stem);
    writeUtf8(auditLog,(exists(auditLog)?readUtf8(auditLog):"")+"\n"+stem+"\n"+log);
    var receipt={schema:"HXY_TRUSTED_ENDPOINT_RECEIPT_2",environmentPolicy:"TRUSTED_FAST_V2",runtimeHashing:"NONE",
      candidate:id,kind:kind,module:mod,theorem:provided,exactType:expectedType,wrapper:wrapper,
      compilation:"PASS_FRESH_EXACT_TYPE_WRAPPER",axiomAudit:"PASS_FRESH_STANDARD_ONLY",axioms:reports,
      environment:environmentIdentity,moduleRecord:moduleRecords[mod],moduleSourceText:sourceInputs[mod].text,
      auditSourceText:source,auditLog:out,auditLogMetadata:metadata(out),auditArtifactMetadata:metadata(obj)};
    writeJson(evidence+"\\audit\\"+stem+".receipt.json",receipt);
    say("EXACT_TYPE_CHECK=PASS|"+provided); say("AXIOM_AUDIT_STANDARD_ONLY="+provided);
    say(id+"_"+kind.toUpperCase()+"=PASS"); return receipt;
  }
  function assertObservedInputsUnchanged() {
    for (var p in observedFiles) if (Object.prototype.hasOwnProperty.call(observedFiles,p)) {
      var input=observedFiles[p];
      if (!exists(input.path) || !same(metadata(input.path),input.metadata)) fail("DIRECT_INPUT_METADATA_CHANGED_DURING_RUN="+input.path);
    }
  }
  function processCandidate(c) {
    var r={id:c.id,predicate:c.predicate,forwardModule:c.forwardModule,equivalenceModule:c.equivalenceModule,
      forward:"PENDING",equivalence:"PENDING",marker:"NONE"}; results.candidates.push(r);
    try { buildModule(c.forwardModule); r.forwardReceipt=auditEndpoint(c,"forward"); r.forward="PASS"; }
    catch (e) { r.forward="FAIL"; r.forwardError=errorText(e); say(c.id+"_FORWARD=FAIL|"+r.forwardError); }
    try { buildModule(c.equivalenceModule); r.equivalenceReceipt=auditEndpoint(c,"equivalence"); r.equivalence="PASS"; }
    catch (e) { r.equivalence="FAIL"; r.equivalenceError=errorText(e); say(c.id+"_EQUIVALENCE=FAIL|"+r.equivalenceError); }
  }
  function auditAggregate() {
    buildModule(config.aggregateModule);
    var rh="_root_.RiemannHypothesis",b="HXYThreeSpaces.BanachExt",h="HXYThreeSpaces.HilbertRep",o="HXYThreeSpaces.HolExt";
    var exact="(And (\u2200 X Y : Nat, Iff (HXYThreeSpaces.HXY X Y) "+rh+") "+
      "(And (Iff "+rh+" "+b+") (And (Iff "+rh+" "+h+") (Iff "+rh+" "+o+"))))";
    results.rootReceipt=auditExact("ROOT","equivalences",config.aggregateModule,"HXY_THREE_FUNCTION_SPACE_EQUIVALENCES",exact);
    results.allThreeReceipt=auditExact("ROOT","rh_constructions",config.aggregateModule,"HXYThreeSpaces.all_three_of_nativeRH",
      "("+rh+" -> And "+b+" (And "+h+" "+o+"))");
  }
  var fatal=false;
  try {
    for (var ai=0;ai<WScript.Arguments.length;++ai) {
      var arg=String(WScript.Arguments(ai));
      if (/^(all|C1|C2|C3)$/i.test(arg)) selection=arg.toUpperCase();
      else if (/^\/force$/i.test(arg)) force=true;
      else if (/^\/rehash$/i.test(arg)) fail("REHASH_UNSUPPORTED_IN_TRUSTED_FAST");
      else fail("USAGE=run.cmd [all|C1|C2|C3] [/force]");
    }
    runId="r-"+(new Date()).getTime()+"-"+Math.floor(Math.random()*1000000);
    evidence=packageDir+"\\evidence\\"+runId; mkdirs(evidence);
    buildLog=evidence+"\\run-build.log"; auditLog=evidence+"\\run-audit.log";
    writeUtf8(buildLog,""); writeUtf8(auditLog,""); results.runId=runId; results.evidence=evidence;
    say("EVIDENCE="+evidence); say("RUNNER=HXY_NATIVE_WINDOWS_TRUSTED_FAST_V2");
    say("SOURCE_PREPARATION_IS_NOT_A_TIER=TRUE"); loadConfig();
    var cacheHome=getenv("LEAN_ANCHORINGS_HOME") || (getenv("LOCALAPPDATA")+"\\LEAN_ANCHORINGS");
    if (!cacheHome || /^\\LEAN_ANCHORINGS$/.test(cacheHome)) fail("LEAN_ANCHORINGS_HOME_REQUIRED");
    cacheDir=cacheHome+"\\"+config.cacheFamily; mkdirs(cacheDir); cacheLock=cacheDir+"\\writer-lock";
    if (dirExists(cacheLock)) fail("ACTIVE_OR_STALE_CACHE_LOCK="+cacheLock);
    fso.CreateFolder(cacheLock); lockHeld=true; importsDir=cacheDir+"\\oleans"; receiptDir=cacheDir+"\\receipts";
    mkdirs(importsDir); mkdirs(receiptDir); say("PROJECT_CACHE="+cacheDir); selectEnvironment();
    for (var ci=0;ci<config.candidates.length;++ci) {
      var c=config.candidates[ci]; if (selection==="all" || selection==="ALL" || selection===c.id) processCandidate(c);
    }
    var allPass=true;
    for (ci=0;ci<results.candidates.length;++ci) if (results.candidates[ci].forward!=="PASS" || results.candidates[ci].equivalence!=="PASS") allPass=false;
    if ((selection==="all" || selection==="ALL") && allPass && config.aggregateModule) {
      try { auditAggregate(); results.aggregate="PASS"; }
      catch (e) { results.aggregate="FAIL"; results.aggregateError=errorText(e); allPass=false; say("AGGREGATE=FAIL|"+results.aggregateError); }
    } else results.aggregate="NOT_REQUESTED_OR_BRANCH_INCOMPLETE";
    assertObservedInputsUnchanged();
    var inventory={};
    for (var name in sourceInputs) if (Object.prototype.hasOwnProperty.call(sourceInputs,name)) {
      var si=sourceInputs[name]; inventory[si.path]={sourceText:si.text,metadata:si.metadata,
        packagedSha256Label:si.packagedSha256Label,labelVerification:"TRUSTED_NOT_REHASHED"};
    }
    writeJson(evidence+"\\source-inputs.json",inventory);
    results.sourceInputs=evidence+"\\source-inputs.json";
    results.status=allPass?"PASS":"PARTIAL_OR_FAILED"; results.compiledModules=compiled;
    results.reusedModules=reused; results.migratedModules=migrated;
    for (ci=0;ci<results.candidates.length;++ci) if (results.candidates[ci].forward==="PASS")
      results.candidates[ci].marker="!!!!(cond on RH)";
    writeJson(evidence+"\\RESULTS.json",results);
    for (ci=0;ci<results.candidates.length;++ci) {
      var cr=results.candidates[ci]; say(cr.id+"_CLOSURE="+(cr.marker==="NONE"?"PENDING":cr.marker));
      if (cr.equivalence==="PASS") say(cr.id+"_EQUIVALENCE_A_TIER=!!");
    }
    say("CACHE_REUSED_MODULES="+reused); say("CACHE_MIGRATED_MODULES="+migrated); say("CACHE_COMPILED_MODULES="+compiled);
    say("PREMISE_FREE_RH=NOT_CLAIMED"); say("RUN="+results.status); if (!allPass) fatal=true;
  } catch (e) {
    fatal=true; results.status="FAIL"; results.error=errorText(e);
    for (var j=0;j<results.candidates.length;++j) results.candidates[j].marker="NONE";
    say("ERROR="+results.error); say("RUN=FAIL");
    if (evidence) { try { writeJson(evidence+"\\RESULTS.json",results); } catch (_) {} }
  } finally {
    if (lockHeld && dirExists(cacheLock)) { try { fso.DeleteFolder(cacheLock,true); } catch (_) {} }
  }
  WScript.Quit(fatal?1:0);
}());
