SOURCES = stdlib.ml saml_dssi.ml common.ml config.ml \
	backend.ml lang.ml builtin.ml \
	parser.mly lexer.mll saml.ml
RESULT = saml
#PACKS = llvm-2_8 llvm-2_8.analysis llvm-2_8.bitwriter
ANNOTATE = yes
DOC_FILES = lang.ml
OCAMLOPT = ocamlopt.opt
OCAMLFLAGS = -w -8-23
INCDIRS = +pulseaudio backends/ocaml
LIBS = pulseaudio samlib

OCAMLC = ocamlc.opt
OCAMLOPT = ocamlopt.opt

test: all
	OCAMLRUNPARAM=b ./saml test.saml
	$(MAKE) dssi

dssi: dssi_out.so
analyze: dssi
	DSSI_PATH="." dssi_analyse_plugin dssi_out.so
liq: dssi
	LIQ_DSSI_PATH="`pwd`" /home/smimram/prog/savonet/liquidsoap/src/liquidsoap -v m.liq

%.so: %.c
	gcc -fPIC -shared -Wall -Wno-unused-variable -g -lm $^ -o $@

all: backends saml_dssi.ml nc

backends:
	$(MAKE) -C backends

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

ci:
	svn ci -m ""

saml_dssi.ml: saml_dssi.c
	echo 'let c = "' > $@
	cat $^ | sed 's/\\n/\\\\n/g' | sed 's/"/\\"/g' >> $@
	echo '"' >> $@

# include Makefile.defs
# include Makefile.rules
include OCamlMakefile