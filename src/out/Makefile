OCAML-MM = /home/smimram/prog/savonet/ocaml-mm/src
OCAML-PULSEAUDIO = +pulseaudio

ml:
	ocamlopt.opt -annot unix.cmxa bigarray.cmxa -I +pulseaudio pulseaudio.cmxa -I $(OCAML-MM) mm.cmxa -I ../runtime/ocaml samlrun.cmxa output.ml -o output
	./output
