all: dev

deps:
	opam install \
		dune utop ocamlformat

dev:
	dune build @src/fmt --auto-promote || true
	dune build src --profile dev

repl:
	dune utop src

clean:
	dune clean

.PHONY: all repl clean
