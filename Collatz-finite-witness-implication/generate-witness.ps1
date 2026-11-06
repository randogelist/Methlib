param(
  [Parameter(Mandatory=$true)][string]$InputPath,
  [Parameter(Mandatory=$true)][string]$OutputPath
)
$ErrorActionPreference = 'Stop'
try {
  $fi = Get-Item -LiteralPath $InputPath
  if ($fi.PSIsContainer -or $fi.Length -gt 67108864) { throw 'Input must be a file of at most 64 MiB.' }
  $utf8 = [System.Text.UTF8Encoding]::new($false, $true)
  $raw = [IO.File]::ReadAllBytes($fi.FullName)
  $data = $utf8.GetString($raw)
  if ($data.Length -eq 0) { throw 'Empty input.' }
  $tokens = [regex]::Split($data.Trim(), '\s+')
  $script:position = 0
  function Next-Token {
    if ($script:position -ge $tokens.Length) { throw 'Unexpected end of witness input.' }
    $tok = $tokens[$script:position]
    $script:position++
    return $tok
  }
  function Expect-Token([string]$expected) {
    $tok = Next-Token
    if ($tok -cne $expected) { throw "Expected label '$expected'." }
  }
  function Next-Integer {
    $tok = Next-Token
    if ($tok.Length -gt 100000 -or $tok -cnotmatch '^(0|[1-9][0-9]*|-[1-9][0-9]*)$') {
      throw 'Invalid canonical integer token or integer exceeds 100000 characters.'
    }
    if ($tok.StartsWith('-')) { return '(' + $tok + ')' }
    return $tok
  }
  function Next-Vector([int]$count) {
    $entries = [Collections.Generic.List[string]]::new()
    for ($i = 0; $i -lt $count; $i++) { $entries.Add((Next-Integer)) }
    return '![' + ($entries -join ', ') + ']'
  }
  function Next-Matrix([int]$count) {
    $rows = [Collections.Generic.List[string]]::new()
    for ($i = 0; $i -lt $count; $i++) { $rows.Add((Next-Vector $count)) }
    return '![' + ($rows -join ', ') + ']'
  }
  Expect-Token 'COLLATZ_AFFINE_INTEGER_V1'
  Expect-Token 'dimension'
  $dToken = Next-Token
  $d = 0
  if ($dToken -cnotmatch '^[1-9][0-9]*$' -or -not [int]::TryParse($dToken, [ref]$d) -or $d -gt 256) {
    throw 'Dimension must be a canonical integer between 1 and 256.'
  }
  Expect-Token 'denominator'
  $den = Next-Integer
  $lines = [Collections.Generic.List[string]]::new()
  $lines.Add('import major_lean_collatz')
  $lines.Add('open CollatzIntegerBridge PoincareSecond')
  $lines.Add('namespace CollatzWitness')
  $lines.Add('set_option maxRecDepth 1000000')
  $lines.Add('set_option maxHeartbeats 0')
  $lines.Add("def witness : Encoding $d where")
  $lines.Add("  den := $den")
  foreach ($name in @('B0','B1','G0','G1','G2')) {
    Expect-Token $name
    Expect-Token 'matrix'
    $mat = Next-Matrix $d
    Expect-Token 'offset'
    $offset = Next-Vector $d
    $lines.Add("  $name := { mat := $mat, offset := $offset }")
  }
  Expect-Token 'seed'
  $seed = Next-Vector $d
  Expect-Token 'weight'
  $weight = Next-Vector $d
  Expect-Token 'END'
  if ($script:position -ne $tokens.Length) { throw 'Unexpected tokens after END.' }
  $lines.Add("  seed := $seed")
  $lines.Add("  weight := $weight")
  $lines.Add('theorem witness_valid : IntegerValid witness := by')
  $lines.Add('  decide')
  $lines.Add('theorem collatz : forall n : Nat, 0 < n -> OrdinaryReachesOne n :=')
  $lines.Add('  integerValid_implies_collatz witness witness_valid')
  $lines.Add('end CollatzWitness')
  $outputFull = [IO.Path]::GetFullPath($OutputPath)
  if ($outputFull -ieq $fi.FullName) { throw 'Output path must differ from input path.' }
  [IO.File]::WriteAllText($outputFull, (($lines -join "`n") + "`n"), $utf8)
  Write-Host 'WITNESS_FORMAT=PARSED'
  Write-Host "WITNESS_DIMENSION=$d"
  Write-Host 'LEAN_WITNESS_SOURCE=GENERATED_NOT_YET_VERIFIED'
  exit 0
} catch {
  Write-Host ('WITNESS_GENERATION_ERROR=' + $_.Exception.Message)
  exit 1
}
