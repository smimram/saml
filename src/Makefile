BACKEND = backend_types.ml backend_values.ml backend.ml backend_interp.ml backend_ocaml.ml backend_c.ml
SOURCES = stdlib.ml saml_dssi.ml common.ml config.ml $(BACKEND) \
	lang_types.ml lang.ml builtin.ml parser.mly lexer.mll saml.mli saml.ml
RESULT = saml
#PACKS = llvm-2_8 llvm-2_8.analysis llvm-2_8.bitwriter
ANNOTATE = yes
DOC_FILES = lang.ml
OCAMLOPT = ocamlopt.opt
OCAMLFLAGS = -w -8-23
INCDIRS = +pulseaudio runtime/ocaml
LIBS = pulseaudio samlrun

OCAMLDOCFLAGS = -sort -stars
DOC_FILES = $(filter %.ml, $(SOURCES))

OCAMLC = ocamlc.opt
OCAMLOPT = ocamlopt.opt
OCAMLDOC = ocamldoc.opt

test: all
	OCAMLRUNPARAM=b ./saml test.saml
	# OCAMLRUNPARAM=b ./saml mini_test.saml

dssi: dssi_out.so
analyze: dssi
	DSSI_PATH="." dssi_analyse_plugin dssi_out.so
liq: dssi
	LIQ_DSSI_PATH="`pwd`" /home/smimram/prog/savonet/liquidsoap/src/liquidsoap -v m.liq

%.so: %.c
	gcc -fPIC -shared -Wall -Wno-unused-variable -g -lm $^ -o $@

all: runtime saml_dssi.ml dnc

runtime:
	$(MAKE) -C $@

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

saml_dssi.ml: saml_dssi.c
	echo '(** Functions for emitting DSSI plugins. *)\n' > $@
	echo '(** C code common to all DSSI plugins. *)' >> $@
	echo 'let c = "' >> $@
	cat $^ | sed 's/\\n/\\\\n/g' | sed 's/"/\\"/g' >> $@
	echo '"' >> $@

doc_html: htdoc

.PHONY: runtime

include OCamlMakefile
