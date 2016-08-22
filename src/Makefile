SOURCES = stdlib.ml common.ml config.ml type.ml lang.ml builtin.ml parser.mly lexer.mll saml.ml
RESULT = saml
ANNOTATE = true

all: dnc
	./saml test.saml

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

include OCamlMakefile
