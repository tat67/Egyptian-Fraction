#!/bin/bash
# Build the arXiv source package arxiv/arxiv_source.tar.gz and test-compile it the way arXiv does
# (pdfLaTeX only, no BibTeX: the bibliography comes from main.bbl).
set -e
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex > /dev/null
rm -rf arxiv/src && mkdir -p arxiv/src/tables
cp main.tex paper.sty main.bbl arxiv/src/
cp tables/*.tex arxiv/src/tables/
( cd arxiv/src && tar czf ../arxiv_source.tar.gz main.tex paper.sty main.bbl tables )
rm -rf arxiv/src
# test compile in a clean directory
T=$(mktemp -d)
tar xzf arxiv/arxiv_source.tar.gz -C "$T"
( cd "$T" && for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error main.tex > /dev/null; done )
if grep -q "undefined\|Overfull\|Underfull\|^!" "$T/main.log"; then
  grep -n "undefined\|Overfull\|Underfull\|^!" "$T/main.log"; echo "TEST COMPILE: PROBLEMS"; exit 1
fi
python3 - "$T/main.pdf" <<'PY'
import sys
data = open(sys.argv[1], 'rb').read()
print('test compile OK:', data.count(b'/Type /Page\n') + data.count(b'/Type/Page\n') or 'pages: see PDF', 'bytes', len(data))
PY
tar tzf arxiv/arxiv_source.tar.gz
rm -rf "$T"
