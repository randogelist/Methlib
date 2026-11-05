param([string]$MathlibProject, [switch]$FullRehash, [switch]$Rebuild)
# Windows PowerShell 5.1; this runner uses installed Lean and existing Mathlib objects only.
$ErrorActionPreference = 'Stop'
$pkg = Split-Path -Parent $PSScriptRoot
$utf8 = New-Object Text.UTF8Encoding($false)
$ev = Join-Path $pkg ('evidence\r-' + [guid]::NewGuid().ToString('N'))
$work = Join-Path $ev 'modules'
[void][IO.Directory]::CreateDirectory($work)
function Save($path, $lines) { [IO.File]::WriteAllLines($path, [string[]]@($lines), $utf8) }
function Digest($bytes) {
    $sha = [Security.Cryptography.SHA256]::Create()
    try { [BitConverter]::ToString($sha.ComputeHash($bytes)).Replace('-','').ToLowerInvariant() }
    finally { $sha.Dispose() }
}
function HashText([string]$s) { Digest ($utf8.GetBytes($s)) }
function HashFile([string]$path) {
    $stream = [IO.File]::OpenRead($path)
    try { Digest $stream } finally { $stream.Dispose() }
}
function Native($cli, $dir, $log) {
    Push-Location -LiteralPath $dir
    try {
        $ErrorActionPreference = 'Continue'  # Native stderr is data in Windows PowerShell.
        $lines = @(& $script:lean @cli 2>&1 | ForEach-Object { $_.ToString() })
        $rc = $LASTEXITCODE
    } finally { Pop-Location }
    Save $log $lines
    if ($rc -ne 0) {
        $lines | Where-Object { $_ -notmatch "^'[^']+' (depends on axioms|does not depend on)" } | Select-Object -First 100 | ForEach-Object { Write-Host $_ }
        throw "Lean exit $rc. Log: $log"
    }
    if (($lines -join "`n") -match "(?im)warning:.*declaration uses 'sorry'") { throw "Incomplete proof. Log: $log" }
}
function Family($root, $module) {
    $stem = Join-Path $root ($module.Replace('.', '\'))
    if (!(Test-Path -LiteralPath ($stem + '.olean') -PathType Leaf) -or (Get-Item -LiteralPath ($stem + '.olean')).Length -eq 0) {
        throw "Missing compiled object: $stem.olean"
    }
    $leaf = [IO.Path]::GetFileName($stem)
    Get-ChildItem -LiteralPath (Split-Path -Parent $stem) -File -Filter ($leaf + '.*') | Where-Object {
        $_.Name -cmatch ('^' + [regex]::Escape($leaf) + '\.(olean|ir|ilean)(\..*)?$')
    } | Sort-Object Name
}
function FamilyHash($root, $module) {
    $entries = @(Family $root $module | ForEach-Object { $_.Name + ' ' + (HashFile $_.FullName) })
    HashText ($entries -join "`n")
}
function CopyFamily($from, $to, $module) {
    $dir = Split-Path -Parent (Join-Path $to ($module.Replace('.', '\')))
    [void][IO.Directory]::CreateDirectory($dir)
    foreach ($f in @(Family $from $module)) { Copy-Item -LiteralPath $f.FullName -Destination (Join-Path $dir $f.Name) }
}
function Sealed($dir, $name, $key) {
    try {
        $seal = @(Get-Content -LiteralPath (Join-Path $dir 'seal') -Encoding UTF8)
        return ($seal.Count -eq 2 -and $seal[0] -ceq $key -and $seal[1] -ceq (FamilyHash $dir $name))
    } catch { return $false }
}
function Build($name, $src, $deps) {
    $rel = $name.Replace('.', '\')
    $localSrc = Join-Path $work ($rel + '.lean')
    [void][IO.Directory]::CreateDirectory((Split-Path -Parent $localSrc))
    Copy-Item -LiteralPath $src -Destination $localSrc
    $srcHash = HashFile $localSrc
    if ($pins.ContainsKey($name) -and $srcHash -cne $pins[$name]) { throw "Frozen source hash mismatch: $name" }
    $dependencyHashes = @(foreach ($d in $deps) { $d + ':' + (FamilyHash $work $d) })
    $key = HashText ((@('positive-time-433-v1',$name,$srcHash,$compilerKey,$mathKey) + $dependencyHashes) -join "`n")
    $bucket = Join-Path $cache ($key.Substring(0,28))
    [void][IO.Directory]::CreateDirectory($bucket)
    foreach ($entry in @(Get-ChildItem -LiteralPath $bucket -Directory)) {
        if (!$Rebuild -and $env:FEF_REBUILD -ne '1' -and (Sealed $entry.FullName $name $key)) {
            CopyFamily $entry.FullName $work $name
            if ((FamilyHash $work $name) -cne (FamilyHash $entry.FullName $name)) { throw "Cache copy mismatch: $name" }
            Write-Host "CACHE_HIT=$name"
            Add-Content -LiteralPath $inputs -Value "$name=$srcHash $key CACHE_HIT" -Encoding UTF8
            return
        }
    }
    Write-Host "BUILD=$name"
    Native @('-j4','-o',($rel + '.olean'),($rel + '.lean')) $work (Join-Path $ev ($name + '.log'))
    $familyHash = FamilyHash $work $name
    # Only sealed, complete per-attempt directories are reused by concurrent runs.
    $entry = Join-Path $bucket ([guid]::NewGuid().ToString('N').Substring(0,12))
    [void][IO.Directory]::CreateDirectory($entry)
    CopyFamily $work $entry $name
    if ((FamilyHash $entry $name) -cne $familyHash) { throw "Cache write mismatch: $name" }
    Save (Join-Path $entry 'seal.tmp') @($key,$familyHash)
    [IO.File]::Move((Join-Path $entry 'seal.tmp'),(Join-Path $entry 'seal'))
    Add-Content -LiteralPath $inputs -Value "$name=$srcHash $key BUILD" -Encoding UTF8
}
function MathRoots([string]$project) {
    if (!$project -or !(Test-Path -LiteralPath $project -PathType Container)) { return }
    $choices = @($project, (Join-Path $project '.lake\packages\mathlib\.lake\build\lib\lean'), (Join-Path $project '.lake\build\lib\lean'))
    $primary = $choices | Where-Object { Test-Path -LiteralPath (Join-Path $_ 'Mathlib.olean') -PathType Leaf } | Select-Object -First 1
    if (!$primary) { return }
    $libDir = Get-Item -LiteralPath $primary
    $libDir.FullName
    if ($libDir.Name -eq 'lean' -and $libDir.Parent.Name -eq 'lib' -and $libDir.Parent.Parent.Name -eq 'build' -and $libDir.Parent.Parent.Parent.Name -eq '.lake') {
        $repo = $libDir.Parent.Parent.Parent.Parent
        $packages = @(Join-Path $repo.FullName '.lake\packages')
        if ($repo.Parent -and $repo.Parent.Name -eq 'packages') { $packages += $repo.Parent.FullName }
        foreach ($p in $packages) {
            if (!(Test-Path -LiteralPath $p -PathType Container)) { continue }
            foreach ($d in @(Get-ChildItem -LiteralPath $p -Directory | Sort-Object Name)) {
                $lib = Join-Path $d.FullName '.lake\build\lib\lean'
                if (Test-Path -LiteralPath $lib -PathType Container) { $lib }
            }
        }
    }
}
# NTFS identity and high-resolution file-change time detect same-size replacements and
# modifications even when a source timestamp is restored. Unavailable identities force SHA256.
function InstallStampReader {
    if ('FeffermanCache433' -as [type]) { return }
    Add-Type -TypeDefinition @'
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Win32.SafeHandles;

public static class FeffermanCache433 {
    [StructLayout(LayoutKind.Sequential)]
    struct FileInfo {
        public uint attributes;
        public System.Runtime.InteropServices.ComTypes.FILETIME creation, access, write;
        public uint volume, sizeHigh, sizeLow, links, indexHigh, indexLow;
    }
    [StructLayout(LayoutKind.Sequential)]
    struct BasicInfo {
        public long creation, access, write, change;
        public uint attributes;
    }
    [DllImport("kernel32.dll", SetLastError=true)]
    static extern bool GetFileInformationByHandle(SafeFileHandle h, out FileInfo info);
    [DllImport("kernel32.dll", SetLastError=true)]
    static extern bool GetFileInformationByHandleEx(SafeFileHandle h, int infoClass, out BasicInfo info, uint size);
    static readonly UTF8Encoding Utf8 = new UTF8Encoding(false);
    static string Hex(byte[] bytes) { return BitConverter.ToString(bytes).Replace("-","").ToLowerInvariant(); }
    static string TextHash(string text) {
        using (var sha = SHA256.Create()) { return Hex(sha.ComputeHash(Utf8.GetBytes(text))); }
    }
    static string Identity(FileStream file) {
        FileInfo f;
        BasicInfo b;
        if (!GetFileInformationByHandle(file.SafeFileHandle,out f) ||
            !GetFileInformationByHandleEx(file.SafeFileHandle,0,out b,(uint)Marshal.SizeOf(typeof(BasicInfo))) ||
            (f.indexHigh == 0 && f.indexLow == 0) || b.change <= 0 || b.write <= 0) { return null; }
        return String.Format(CultureInfo.InvariantCulture,"{0:x}:{1:x}:{2:x}:{3:x}:{4:x}:{5:x}:{6:x}:{7:x}",
            f.volume,f.indexHigh,f.indexLow,f.sizeHigh,f.sizeLow,b.creation,b.write,b.change);
    }
    static bool ValidDigest(string value) {
        if (value.Length != 64) { return false; }
        foreach (char c in value) { if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) { return false; } }
        return true;
    }
    static Dictionary<string,string[]> Previous(string file) {
        var rows = new Dictionary<string,string[]>(StringComparer.Ordinal);
        if (!File.Exists(file)) { return rows; }
        try {
            string text = File.ReadAllText(file,Utf8);
            int split = text.IndexOf('\n');
            if (split != 64) { return rows; }
            string body = text.Substring(split+1);
            if (TextHash(body) != text.Substring(0,split)) { return rows; }
            foreach (string line in body.Split(new char[] {'\n'},StringSplitOptions.RemoveEmptyEntries)) {
                string[] fields = line.Split('\t');
                if (fields.Length == 3 && ValidDigest(fields[2])) { rows[fields[0]] = fields; }
            }
        } catch (IOException) { rows.Clear(); }
        return rows;
    }
    static bool IsObject(string path) {
        string n = Path.GetFileName(path).ToLowerInvariant();
        return n.EndsWith(".olean") || n.Contains(".olean.") || n.EndsWith(".ir") || n.Contains(".ir.") ||
               n.EndsWith(".dll") || n.EndsWith(".so") || n.EndsWith(".dylib");
    }
    public static string RootDigest(string root,string index,bool force) {
        bool ntfs = false;
        try { ntfs = String.Equals(new DriveInfo(Path.GetPathRoot(root)).DriveFormat,"NTFS",StringComparison.OrdinalIgnoreCase); }
        catch (IOException) { }
        catch (ArgumentException) { }
        catch (UnauthorizedAccessException) { }
        var previous = force || !ntfs ? new Dictionary<string,string[]>(StringComparer.Ordinal) : Previous(index);
        var files = new List<string>();
        foreach (string path in Directory.EnumerateFiles(root,"*",SearchOption.AllDirectories)) {
            if (IsObject(path)) { files.Add(path); }
        }
        files.Sort(StringComparer.Ordinal);
        var next = new StringBuilder();
        var contents = new StringBuilder();
        DateTime last = DateTime.UtcNow;
        int reused = 0, reads = 0;
        foreach (string path in files) {
            string rel = path.Substring(root.Length+1);
            string stamp, hash;
            using (var stream = new FileStream(path,FileMode.Open,FileAccess.Read,FileShare.Read)) {
                stamp = ntfs ? Identity(stream) : null;
                string[] old;
                if (stamp != null && previous.TryGetValue(rel,out old) && old[1] == stamp) {
                    hash = old[2]; reused++;
                } else {
                    using (var sha = SHA256.Create()) { hash = Hex(sha.ComputeHash(stream)); }
                    reads++;
                }
            }
            if (stamp != null) { next.Append(rel).Append('\t').Append(stamp).Append('\t').Append(hash).Append('\n'); }
            contents.Append(rel).Append('\t').Append(hash).Append('\n');
            if ((DateTime.UtcNow-last).TotalSeconds >= 10) {
                Console.WriteLine("CACHE_SCAN_FILES={0}/{1} HASH_REUSED={2} REHASHED={3}",reused+reads,files.Count,reused,reads);
                last = DateTime.UtcNow;
            }
        }
        string body = next.ToString();
        string tmp = index + "." + Guid.NewGuid().ToString("N") + ".tmp";
        File.WriteAllText(tmp,TextHash(body)+"\n"+body,Utf8);
        try {
            if (File.Exists(index)) { File.Replace(tmp,index,null); } else { File.Move(tmp,index); }
        } catch (IOException) {
            // A concurrent publisher may win. Our content key was computed independently.
        } finally { if (File.Exists(tmp)) { File.Delete(tmp); } }
        Console.WriteLine("DEPENDENCY_OBJECTS={0} HASH_REUSED={1} REHASHED={2}",files.Count,reused,reads);
        return TextHash(contents.ToString());
    }
}
'@
}
function ExternalKey($dirs) {
    $force = $FullRehash -or $env:FEF_FULL_REHASH -eq '1'
    try { InstallStampReader } catch { Write-Host 'NTFS_STAMP_INDEX=UNAVAILABLE' }
    if ('FeffermanCache433' -as [type]) {
        $index = Join-Path $cache 'native-fingerprints'
        [void][IO.Directory]::CreateDirectory($index)
        $parts = @(foreach ($dir in $dirs) {
            $full = [IO.Path]::GetFullPath($dir).TrimEnd([IO.Path]::DirectorySeparatorChar)
            $key = HashText ($full.ToUpperInvariant())
            $stampFile = Join-Path $index ($key + '.tsv')
            $full + ' ' + [FeffermanCache433]::RootDigest($full,$stampFile,[bool]$force)
        })
        return (HashText ($parts -join "`n"))
    }
    Write-Host 'DEPENDENCY_DIGEST=FULL_CONTENT'

    $inventory = New-Object Text.StringBuilder
    $count = 0
    foreach ($dir in $dirs) {
        [void]$inventory.AppendLine("ROOT $dir")
        # Hash loaded module families, not timestamps or just the umbrella Mathlib.olean.
        foreach ($file in @(Get-ChildItem -LiteralPath $dir -File -Recurse | Where-Object {
            $_.Name -match '\.(olean|ir)(\..*)?$|\.(dll|so|dylib)$'
        } | Sort-Object FullName)) {
            [void]$inventory.AppendLine($file.FullName.Substring($dir.Length) + ' ' + (HashFile $file.FullName))
            $count++
            if (($count % 5000) -eq 0) { Write-Host "CACHE_SCAN_FILES=$count" }
        }
    }
    Write-Host "FINGERPRINTED_DEPENDENCY_FILES=$count"
    HashText ($inventory.ToString())
}
function AuditReports($log, $names) {
    $raw = [IO.File]::ReadAllText($log, $utf8)
    $reported = @{}
    $allowed = @('propext','Classical.choice','Quot.sound')
    $space = '[ \t\r\n]*'
    $token = '[A-Za-z][A-Za-z0-9_.]*'
    $list = "\A'(?<name>[A-Za-z0-9_.]+)' depends on axioms:${space}\[(?<items>${space}${token}(?:${space},${space}${token})*${space})\]\z"
    $none = "\A'(?<name>[A-Za-z0-9_.]+)' does not depend on any axioms\z"
    foreach ($chunk in [regex]::Split($raw, "(?m)(?=^[ \t]*')")) {
        $report = $chunk.Trim()
        if ($report.Length -eq 0) { continue }
        if ($report -cmatch $list) {
            $name = $Matches['name']
            foreach ($ax in ($Matches['items'] -split ',')) {
                if ($allowed -cnotcontains $ax.Trim()) { throw "Unapproved axiom $ax in $name" }
            }
        } elseif ($report -cmatch $none) { $name = $Matches['name'] }
        else { throw "Malformed audit report: $report" }
        if ($names -cnotcontains $name -or $reported.ContainsKey($name)) { throw "Unexpected or duplicate audit: $name" }
        $reported[$name] = $true
    }
    foreach ($name in $names) { if (!$reported.ContainsKey($name)) { throw "Missing axiom report: $name" } }
}
try {
    Write-Host "EVIDENCE=$ev"
    $elan = if ($env:ELAN_HOME) { $env:ELAN_HOME } else { Join-Path $env:USERPROFILE '.elan' }
    $bin = Join-Path $elan 'toolchains\leanprover--lean4---v4.33.0\bin'
    $lean = Join-Path $bin 'lean.exe'
    if (!(Test-Path -LiteralPath $lean -PathType Leaf)) { throw "Missing Windows Lean 4.33.0: $lean" }
    $env:PATH = "$bin;$env:PATH"
    Native @('--version') $ev (Join-Path $ev 'version.txt')
    $version = [IO.File]::ReadAllText((Join-Path $ev 'version.txt')).Trim()
    if ($version -cnotmatch '^Lean \(version 4\.33\.0, x86_64-w64-windows-gnu,') { throw "Unexpected compiler: $version" }
    Write-Host $version
    $runtime = @(Get-ChildItem -LiteralPath $bin -File | Where-Object { $_.Name -eq 'lean.exe' -or $_.Extension -eq '.dll' } | Sort-Object Name | ForEach-Object { $_.Name + ' ' + (HashFile $_.FullName) })
    $compilerKey = HashText ((@($version) + $runtime) -join "`n")
    $cache = if ($env:FEF_CACHE_DIR) { [IO.Path]::GetFullPath($env:FEF_CACHE_DIR) } else { Join-Path $env:LOCALAPPDATA 'Fefferman\positive-time-433' }
    [void][IO.Directory]::CreateDirectory($cache)
    $override = if ($MathlibProject) { $MathlibProject } else { $env:FEF_MATHLIB }
    $candidates = @()
    if ($override) { $candidates += $override }
    else {
        $native = Join-Path $env:USERPROFILE 'lean-native'
        $candidates += $env:MATHLIB_PROJECT
        $candidates += $env:MATHLIB_DIR
        $candidates += Join-Path $native 'awpi_phi_rh_lean_sieved_v0_1_1'
        $candidates += $native
        if (Test-Path -LiteralPath $native -PathType Container) {
            $candidates += @(Get-ChildItem -LiteralPath $native -Directory | Sort-Object Name | ForEach-Object { $_.FullName })
        }
        if ($env:LEAN_PATH) { $candidates += @($env:LEAN_PATH -split ';') }
    }
    Save (Join-Path $ev 'CacheProbe.lean') @('import Mathlib')
    $math = @()
    $i = 0
    foreach ($cand in @($candidates | Where-Object { $_ } | Select-Object -Unique)) {
        $dirs = @(MathRoots $cand)
        if (!$dirs.Count) { continue }
        if ($env:FEF_EXTRA_LEAN_PATH) {
            foreach ($extra in @($env:FEF_EXTRA_LEAN_PATH -split ';' | Where-Object { $_ })) { $dirs += (Get-Item -LiteralPath $extra).FullName }
        }
        $dirs = @($dirs | Select-Object -Unique)
        $env:LEAN_PATH = $dirs -join ';'
        $i++
        try {
            Native @('-j4','CacheProbe.lean') $ev (Join-Path $ev "cache-probe-$i.log")
            $math = $dirs
            break
        } catch { Write-Host "REJECTED_CACHE=$cand" }
    }
    if (!$math.Count) { throw 'No compatible cached Mathlib. Set FEF_MATHLIB to the Mathlib project or directory containing Mathlib.olean.' }
    Write-Host "CACHED_MATHLIB=$($math[0])"
    Write-Host 'HASHING_DEPENDENCY_CACHE=START'
    $standard = Join-Path (Split-Path -Parent $bin) 'lib\lean'
    if (!(Test-Path -LiteralPath (Join-Path $standard 'Init.olean') -PathType Leaf)) { throw "Missing standard library under $standard" }
    $mathKey = ExternalKey (@($standard) + $math)
    $env:LEAN_PATH = (@($work) + $math) -join ';'
    $inputs = Join-Path $ev 'inputs.txt'
    Save $inputs @("LEAN_PATH=$env:LEAN_PATH","COMPILER_SHA256=$compilerKey","STANDARD_AND_MATHLIB_SHA256=$mathKey","MODULE_CACHE=$cache")
    $pins = @{
        'Fefferman.Analysis' = 'd70620b1e3035563a983351d193241b7dccdfc579af283487e811eabeaa60c24'
        'Fefferman.Statements' = 'e026d1b26e3e4b6fccb6d338bbfb5c1f3c6c6fb75b15750616923e80c3da287f'
        'ConcreteABCDUnifiedClosure' = 'b50becc18ace6fb2596fe2b98398363983727163bb573a5aedf6c76e6df6b706'
    }
    $modules = @('Fefferman.Analysis','Fefferman.Statements','ConcreteABCDUnifiedClosure','ShiftAnalytic','ShiftCore','FEF_B_POSITIVE_TIME')
    $prior = @()
    foreach ($name in $modules) {
        $relative = $name.Replace('.', '\') + '.lean'
        $source = if ($pins.ContainsKey($name)) { Join-Path (Join-Path $pkg 'base') $relative } elseif ($name -in @('ShiftAnalytic','ShiftCore')) { Join-Path $PSScriptRoot $relative } else { Join-Path $pkg $relative }
        Build $name $source $prior
        $prior += $name
    }
    # Run the released type checks, then request only actual kernel reports in a clean independent log.
    $auditSource = Join-Path $PSScriptRoot 'AuditB.lean'
    $auditSrcWork = Join-Path $work 'AuditB.lean'
    Copy-Item -LiteralPath $auditSource -Destination $auditSrcWork
    $names = @([regex]::Matches([IO.File]::ReadAllText($auditSrcWork,$utf8),'(?m)^\s*#print\s+axioms\s+([A-Za-z][A-Za-z0-9_.]*)[ \t]*\r?$') | ForEach-Object { $_.Groups[1].Value })
    if (!$names.Count -or @($names | Select-Object -Unique).Count -ne $names.Count) { throw 'Missing or duplicate theorem declarations in AuditB.lean' }
    $required = @(
        'Fefferman.ConcreteReal.AdjustedA.smoothClosedHalfSpaceReal_shift'
        'Fefferman.ConcreteReal.shift_clause01'
        'Fefferman.ConcreteReal.shift_clause02'
        'Fefferman.ConcreteReal.shift_clause03'
        'Fefferman.ConcreteReal.AdjustedB.shift_clause10'
        'Fefferman.ConcreteReal.AdjustedB.shift_periodic_pressure'
        'Fefferman.ConcreteReal.AdjustedB.shifted_global_solution'
        'Fefferman.ConcreteReal.AdjustedB.FEF_B_POSITIVE_TIME'
        'Fefferman.ConcreteReal.AdjustedB.regularity_of_seed_extension'
        'Fefferman.ConcreteReal.AdjustedB.ZeroSeed.admissible_zero'
        'Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_small'
        'Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_global'
        'Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_hasGlobalSolution'
        'Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_positive_flow'
        'Fefferman.ConcreteReal.AdjustedB.zero_is_positive_time_state'
        'Fefferman.ConcreteReal.AdjustedB.ConstantSeed.exists_nonzero_positive_time_state'
    )
    if ($required.Count -ne $names.Count) { throw 'Incorrect periodic audit count' }
    foreach ($n in $required) { if ($names -cnotcontains $n) { throw "Missing required theorem audit: $n" } }
    Add-Content -LiteralPath $inputs -Value ('Audit=' + (HashFile $auditSrcWork)) -Encoding UTF8
    Native @('-j4','-o','AuditB.olean','AuditB.lean') $work (Join-Path $ev 'AuditB.log')
    Save (Join-Path $work 'ConfirmAxioms.lean') (@('import AuditB','set_option format.width 100000') + @($names | ForEach-Object { '#print axioms ' + $_ }))
    $axiomLog = Join-Path $ev 'axioms.log'
    Native @('-j4','ConfirmAxioms.lean') $work $axiomLog
    AuditReports $axiomLog $names
    Get-Content -LiteralPath $axiomLog -Encoding UTF8 | ForEach-Object { Write-Host $_ }
    $result = @(
        'PACKAGE=FEF_B_POSITIVE_TIME_433'
        ('EVIDENCE_RUN_ID=' + (Split-Path -Leaf $ev))
        'PROJECT_BUILD=PASS'
        "THEOREM_AXIOM_AUDITS=$($names.Count)"
        'AXIOMS=STANDARD_ONLY'
        'WITNESSED_PERIODIC_POSITIVE_TIME_STATE_TO_GLOBAL_SOLUTION=PASS'
        'PERIODIC_SMALL_SEED_EXTENSION_IN_LEAN=OPEN'
        'RUN=PASS'
    )
    Save (Join-Path $ev 'result.txt') $result
    $result | ForEach-Object { Write-Host $_ }
    exit 0
} catch {
    $result = @('RUN=FAIL',('REASON=' + $_.Exception.Message))
    Save (Join-Path $ev 'result.txt') $result
    $result | ForEach-Object { Write-Host $_ }
    exit 1
}
