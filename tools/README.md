# CAG Toolchain

Local utilities for the Complex-Algebraic-Geometry Rocq project.

## Status (as of 2026-04-30)

| Tool        | Python prototype | OCaml port | Wrapper prefers |
|-------------|:----------------:|:----------:|:---------------:|
| cag-search  | ✅               | ✅         | OCaml           |
| cag-audit   | ✅               | —          | Python          |
| cag-tactic  | ✅               | —          | Python          |
| cag-extract | ✅               | —          | Python          |
| cag-gap     | ✅               | —          | Python          |
| cag-hammer  | ✅ (shell)       | —          | shell           |

All wrappers under `bin/` work whether or not the OCaml binary is built. They fall back to Python automatically.

## Build

```sh
cd tools
make ocaml          # build all OCaml binaries
make status         # show what's built
make clean
```

OCaml build requires the `rocq-9.0` opam switch with `cmdliner`, `sqlite3`, `re`, `fmt`, `logs`. The system needs `libsqlite3-dev`. All already installed.

## Usage

```sh
tools/bin/cag-search --rebuild              # build the index
tools/bin/cag-search "core free" -n 5
tools/bin/cag-search --kind axiom "CReal" -n 10
tools/bin/cag-search --stats

tools/bin/cag-audit list -s                 # axiom/parameter summary
tools/bin/cag-audit snapshot                # save baseline
tools/bin/cag-audit diff                    # what changed since snapshot
tools/bin/cag-audit suspect                 # placeholder/vacuous axioms
tools/bin/cag-audit check NAME              # Print Assumptions on NAME

tools/bin/cag-tactic --goal "forall ..."    # local-LLM tactic suggester
tools/bin/cag-tactic --show-retrieved --goal "..."   # retrieval only

tools/bin/cag-extract NAME                  # extract Definition to OCaml

tools/bin/cag-gap eval "Size(SymmetricGroup(5))"
tools/bin/cag-gap q15 --max-order 30        # KLMRS Q1.5 candidate scan

# CoqHammer: try sauto / hammer on an isolated goal
tools/bin/cag-hammer --tactic sauto 'forall A B : Prop, A /\ B -> B /\ A'
tools/bin/cag-hammer --tactic hammer --timeout 20 \
    --import CAG.Group \
    'forall G (sg : Group.StrictGroup G) a, smul G sg a (se G sg) = a'
```

### CoqHammer notes (post-2026-04-30 install)

CoqHammer 1.3.2+9.0 is installed in the `rocq-9.0` switch with Z3, CVC5,
and eprover backends. Use any of:

* `sauto`           — pure search-based reconstruction (no ATPs)
* `sauto use: ...`  — search with hint lemmas
* `hauto`, `qauto`, `lauto` — finer-grained reconstruction tactics
* `hammer`          — full pipeline: ATPs + reconstruction (slow + RAM-hungry)

⚠️ **OOM risk on this VM**: the `hammer` tactic by default fires Z3 + CVC5
+ eprover in parallel. With 11 GB RAM and no swap, complex goals will
trigger the OOM killer and report ATP failure. Mitigations:

1. Use `sauto use: <hint>` instead of `hammer` when you know the relevant
   lemma — drastically lower memory.
2. Add swap: `sudo fallocate -l 4G /swap && sudo mkswap /swap && sudo swapon /swap` (4 GB).
3. Disable some ATPs: `Set Hammer Vampire ""`, `Set Hammer Eprover ""`.
4. Lower `Set Hammer ATPLimit 10` and `Set Hammer Predictions 256` (defaults
   are 20 and 1024).

## Architecture

* `cag_lib/`  shared Rocq parser (Python and OCaml versions both present).
* `bin/`      shell wrappers that select OCaml/Python.
* `cag_search/`, `cag_audit/`, `cag_tactic/`, `cag_extract/`, `cag_gap/` Python modules.
* `ocaml/`    dune-based OCaml port; subdirs `cag_lib/`, `cag_search/` so far.

## Where to resume

The OCaml port has cag-search done; cag-audit, cag-tactic, cag-extract, cag-gap are still Python only. The Python implementations all work as-is — porting is for type safety and native speed, not feature parity.

To pick up the port:
1. Pattern is set in `ocaml/cag_search/cag_search.ml` — flat single-file executable using cmdliner + sqlite3 + cag_lib.
2. Each new tool gets a subdir under `ocaml/`, a `dune` file (executable stanza, no `public_name`), and a single `.ml` entry point.
3. Add to `tools/Makefile` if you want a Make target.

The blocking constraint is that this VM has 11 GB RAM and 2 vCPU, no GPU. Anything LLM-touching (cag-tactic) will be slow. Add VM resources before attempting heavy LLM work.
