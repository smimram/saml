all: build
	dune exec ./saml.exe test.saml

build:
	@dune build

install:
	@dune install

ci:
	git ci . -m "Progress on SAML."
	git push

conflicts:
	@rm -f parser.conflicts
	@menhir --explain parser.mly
	@rm -f parser.ml parser.mli
	@less parser.conflicts
	@rm -f parser.conflicts
