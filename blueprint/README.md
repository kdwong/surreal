# Surreal-number blueprint

This directory contains the `leanblueprint` source for the mathematical dependency graph of
the project. The generated HTML and PDF are intentionally ignored by Git.

The current published version is available at
<https://kdwong.github.io/surreal/blueprint/>.

## Local web build on PowerShell

From the repository root:

```powershell
python -m venv blueprint\.venv
blueprint\.venv\Scripts\python -m pip install -r blueprint\requirements.txt
$blueprintScripts = (Resolve-Path blueprint\.venv\Scripts).Path
$env:PATH = "$blueprintScripts;$env:PATH"
$env:PYTHONUTF8 = "1"
lake build Surreal
leanblueprint web
leanblueprint checkdecls
leanblueprint serve
```

The server prints the local URL, normally `http://0.0.0.0:8000/`. The dependency graph is at
`http://localhost:8000/dep_graph_document.html`.

## Printable build

If `latexmk`, Perl, and XeLaTeX are available:

```powershell
leanblueprint pdf
```

On a Windows installation with XeLaTeX but no Perl, the equivalent direct build is:

```powershell
New-Item -ItemType Directory -Force blueprint\print | Out-Null
Push-Location blueprint\src
xelatex -interaction=nonstopmode -output-directory=..\print print.tex
xelatex -interaction=nonstopmode -output-directory=..\print print.tex
Pop-Location
```

Generated outputs:

- `blueprint/web/index.html`: local web blueprint;
- `blueprint/web/dep_graph_document.html`: interactive dependency graph;
- `blueprint/print/print.pdf`: printable blueprint;
- `blueprint/lean_decls`: declaration names collected from `\lean{...}` annotations.
