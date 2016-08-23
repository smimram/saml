SOURCES = stdlib.ml common.ml config.ml type.ml lang.ml builtin.ml parser.mly lexer.mll pa.ml saml.ml
RESULT = saml
ANNOTATE = true
PACKS = pulseaudio

all: dnc
	./saml test.saml

ci:
	git ci . -m "Progress on SAML."
	git push

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

include OCamlMakefile
