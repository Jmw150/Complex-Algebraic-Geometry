# Build / install the CAG toolchain.
#
# Targets:
#   make ocaml          — build all OCaml binaries (preferred)
#   make ocaml-search   — build just cag-search
#   make clean          — remove _build/
#   make status         — show what's built
#
# The wrappers under tools/bin prefer OCaml binaries if present and fall
# back to Python prototypes. Both work standalone.

PROJECT_ROOT := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))/..
DUNE_ROOT    := $(PROJECT_ROOT)
OCAML_OUT    := $(DUNE_ROOT)/_build/default/tools/ocaml

OPAM_ENV := eval $$(opam env --switch=rocq-9.0 --set-switch) &&

.PHONY: ocaml ocaml-search clean status

ocaml:
	cd $(DUNE_ROOT) && $(OPAM_ENV) dune build tools/ocaml

ocaml-search:
	cd $(DUNE_ROOT) && $(OPAM_ENV) dune build tools/ocaml/cag_search/cag_search.exe

clean:
	cd $(DUNE_ROOT) && $(OPAM_ENV) dune clean

status:
	@echo "OCaml binaries built:"
	@ls $(OCAML_OUT) 2>/dev/null | sed 's/^/  /' || echo "  (none — run 'make ocaml')"
	@echo
	@echo "Tools available via tools/bin/:"
	@ls $(PROJECT_ROOT)/tools/bin | sed 's/^/  /'
