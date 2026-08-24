$ErrorActionPreference = 'Stop'

$projectRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$outputDir = Join-Path $projectRoot 'output\pdf'
New-Item -ItemType Directory -Force -Path $outputDir | Out-Null
$env:SOURCE_DATE_EPOCH = '1787356800'
$env:FORCE_SOURCE_DATE = '1'

Push-Location $projectRoot
try {
    $outputArgument = "-output-directory=$outputDir"
    pdflatex -interaction=nonstopmode -halt-on-error $outputArgument benzel_problem6.tex
    if ($LASTEXITCODE -ne 0) { throw 'first pdflatex pass failed' }
    bibtex (Join-Path $outputDir 'benzel_problem6')
    if ($LASTEXITCODE -ne 0) { throw 'bibtex pass failed' }
    pdflatex -interaction=nonstopmode -halt-on-error $outputArgument benzel_problem6.tex
    if ($LASTEXITCODE -ne 0) { throw 'second pdflatex pass failed' }
    pdflatex -interaction=nonstopmode -halt-on-error $outputArgument benzel_problem6.tex
    if ($LASTEXITCODE -ne 0) { throw 'final pdflatex pass failed' }
} finally {
    Pop-Location
}

$logPath = Join-Path $outputDir 'benzel_problem6.log'
$badLog = Select-String -Path $logPath -Pattern 'undefined|Overfull|Underfull|LaTeX Warning' -CaseSensitive:$false
if ($badLog) {
    $badLog | ForEach-Object { Write-Error $_.Line }
    throw 'paper log contains unresolved warnings'
}

Write-Host "Built $outputDir\benzel_problem6.pdf"
