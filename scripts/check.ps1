param([switch]$ShowLog)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$lakeScript = Join-Path $PSScriptRoot 'lake.ps1'
$logDirectory = Join-Path $projectRoot 'tmp\check'

function Invoke-LeanCheck {
    param([string]$Label, [string]$LogName, [string[]]$Arguments, [switch]$Audit)
    $logPath = Join-Path $logDirectory $LogName
    $timer = [Diagnostics.Stopwatch]::StartNew()
    & $lakeScript @Arguments *> $logPath
    $checkExitCode = $LASTEXITCODE
    $timer.Stop()
    $output = @(Get-Content -LiteralPath $logPath)
    if ($ShowLog -or $checkExitCode -ne 0) { $output | Write-Output }
    if ($checkExitCode -ne 0) { throw "$Label failed (exit $checkExitCode). Log: $logPath" }
    if (($output -join "`n") -match '\bsorryAx\b') {
        throw "$Label reports a dependency on sorryAx. Log: $logPath"
    }
    $detail = ''
    if ($Audit) {
        $reports = @($output | Select-String -Pattern '^Axiom audit passed: (.+)$')
        if ($reports.Count -ne 1) {
            throw "$Label did not emit exactly one successful audit report. Log: $logPath"
        }
        $detail = ' ' + $reports[0].Matches[0].Groups[1].Value
    }
    Write-Output ("{0}: passed ({1:N1}s).{2}" -f $Label, $timer.Elapsed.TotalSeconds, $detail)
    if (-not $ShowLog) {
        $output | Where-Object { $_ -match '^warning: Parafree(?:[\\/]|\.lean:)' } | Select-Object -Unique | Write-Output
    }
}

Push-Location $projectRoot
try {
    New-Item -ItemType Directory -Path $logDirectory -Force | Out-Null
    # Include the public entry point as well as all project modules.
    $sourceFiles = @((Get-Item -LiteralPath (Join-Path $projectRoot 'Parafree.lean'))) +
        @(Get-ChildItem -LiteralPath (Join-Path $projectRoot 'Parafree') -Filter '*.lean' -Recurse)
    $placeholders = $sourceFiles | Select-String -Pattern '\b(sorry|admit)\b|^\s*(axiom|constant)\s'
    if ($placeholders) {
        $placeholders | Write-Output
        throw 'Proof placeholders or additional axiom declarations found in project sources.'
    }
    # Every source must be checked, even if a future file is omitted from the public import.
    $modules = @{}
    foreach ($file in $sourceFiles) {
        $relative = [IO.Path]::GetRelativePath($projectRoot, $file.FullName)
        $moduleName = $relative.Substring(0, $relative.Length - 5).Replace('\', '.').Replace('/', '.')
        $modules[$moduleName] = $file.FullName
    }
    $pending = [Collections.Generic.Stack[string]]::new()
    $pending.Push('Parafree.Audit.Main')
    $pending.Push('Parafree.Audit.Upstream')
    $covered = [Collections.Generic.HashSet[string]]::new()
    while ($pending.Count -gt 0) {
        $moduleName = $pending.Pop()
        if (-not $covered.Add($moduleName)) { continue }
        $contents = [IO.File]::ReadAllText($modules[$moduleName])
        $imports = [regex]::Matches($contents, '(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\r\n]+)')
        foreach ($import in $imports) {
            $importLine = ($import.Groups[1].Value -split '--', 2)[0]
            foreach ($dependency in ($importLine.Trim() -split '\s+')) {
                if ($dependency.StartsWith('Parafree.') -and -not $modules.ContainsKey($dependency)) {
                    throw "Missing project source imported by ${moduleName}: $dependency"
                }
                if ($modules.ContainsKey($dependency)) { $pending.Push($dependency) }
            }
        }
    }
    $uncovered = @($modules.Keys | Where-Object { -not $covered.Contains($_) } | Sort-Object)
    if ($uncovered.Count -gt 0) {
        throw "Project modules outside the checked import closure: $($uncovered -join ', ')"
    }
    Write-Output "Source scan and import coverage: passed ($($sourceFiles.Count) files)."

    Invoke-LeanCheck 'Build' 'build.log' @('build', 'Parafree', 'Parafree.Audit.Main', 'Parafree.Audit.Upstream')
    # Fresh Lean processes also run the guards when Lake reuses cached audit modules.
    Invoke-LeanCheck 'Public axiom audit' 'main.log' @('env', 'lean', 'Parafree/Audit/Main.lean') -Audit
    Invoke-LeanCheck 'Upstream axiom audit' 'upstream.log' @('env', 'lean', 'Parafree/Audit/Upstream.lean') -Audit
    Write-Output "All checks passed. Full logs: $logDirectory"
}
finally {
    Pop-Location
}
