FLAGS = -pkgs 'zarith' -use-menhir -yaccflag "--explain" -ocamlc "ocamlc -w +a-4-29"
OPTFLAGS = -classic-display -ocamlopt "ocamlopt -O3"

default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild $(FLAGS) hurricane.native

release:
	ocamlbuild $(FLAGS) hurricane.native $(OPTFLAGS)

byte:
	ocamlbuild $(FLAGS) hurricane.byte -tag 'debug'
