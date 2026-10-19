param(
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$LakeArguments = @('build')
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$localElan = Join-Path $projectRoot '.tools\elan'
$previousElan = $env:ELAN_HOME
$previousPath = $env:PATH
$previousLocale = $env:LC_ALL
$previousGitCount = $env:GIT_CONFIG_COUNT
$gitCount = if ($previousGitCount) { [int]$previousGitCount } else { 0 }
$addedGitVariables = @()
Push-Location $projectRoot
try {
    if (Test-Path -LiteralPath $localElan) {
        $env:ELAN_HOME = $localElan
    }
    # Windows' system tar can emit locale-encoded verbose output that Lake cannot decode.
    $gitUtilities = 'C:\Program Files\Git\usr\bin'
    if (Test-Path -LiteralPath (Join-Path $gitUtilities 'tar.exe')) {
        $env:PATH = $gitUtilities + ';' + $env:PATH
        $env:LC_ALL = 'C'
    }
    # Trust only this workspace's dependency checkouts, for this process tree only.
    # Sandboxed and ordinary Windows processes may have created them under different accounts.
    $packageRoot = Join-Path $projectRoot '.lake\packages'
    if (Test-Path -LiteralPath $packageRoot) {
        foreach ($package in Get-ChildItem -LiteralPath $packageRoot -Directory) {
            if (Test-Path -LiteralPath (Join-Path $package.FullName '.git')) {
                $keyName = "GIT_CONFIG_KEY_$gitCount"
                $valueName = "GIT_CONFIG_VALUE_$gitCount"
                [Environment]::SetEnvironmentVariable($keyName, 'safe.directory', 'Process')
                [Environment]::SetEnvironmentVariable($valueName, $package.FullName.Replace('\','/'), 'Process')
                $addedGitVariables += $keyName, $valueName
                $gitCount++
            }
        }
        $env:GIT_CONFIG_COUNT = [string]$gitCount
    }
    & elan run leanprover/lean4:v4.29.0 lake @LakeArguments
    $lakeExitCode = $LASTEXITCODE
}
finally {
    $env:ELAN_HOME = $previousElan
    $env:PATH = $previousPath
    $env:LC_ALL = $previousLocale
    foreach ($variable in $addedGitVariables) {
        [Environment]::SetEnvironmentVariable($variable, $null, 'Process')
    }
    $env:GIT_CONFIG_COUNT = $previousGitCount
    Pop-Location
}
exit $lakeExitCode
