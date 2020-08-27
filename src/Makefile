SOURCES = extlib.ml common.ml config.ml type.ml lang.ml builtin.ml parser.mly lexer.mll preproc.ml pa.ml saml.ml
RESULT = saml
OCAMLYACC = menhir
PACKS = pulseaudio
ANNOTATE = true

all: dnc
	./saml test.saml

install: dnc
	install saml $(PREFIX)/bin

ci:
	git ci . -m "Progress on SAML."
	git push

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

include OCamlMakefile
