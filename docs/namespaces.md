# Module namespaces and imports

A module imports another module with `include`. The compiler records each
include as an edge in a graph of modules, and the linker uses that graph to
decide, for every name a module mentions, which definitions it can dispatch
to. This file describes what an include provides, how import clauses reshape
it, and how inner (closure) definitions fall through to it.

## What an include provides

Each module has its own view of every name: its own definitions first, then
whatever its includes provide, in the order the includes appear in the file,
and finally the standard prelude (`std/base.ti`), which every module includes
implicitly. Two modules can hold definitions for the same name; their cases
are searched in that order.

Within the view there is one refinement. A run of unguarded cases at the end
of a module, such as `def (foo x) ...` with no pattern and no `when`, is a
trailing default. Defaults from all modules are placed behind everyone's
guarded cases, so a specific case in one module wins over a catch-all in
another no matter how the includes are ordered.

```
;; a.ti                          ;; b.ti
def (foo 1) 101                  def (foo 2) 102
def (foo x) 999

;; main module
include "a.ti"
include "b.ti"

(foo 1)    ;; 101, from a.ti
(foo 2)    ;; 102, from b.ti; a.ti's catch-all does not swallow it
(foo 77)   ;; 999, the nearest trailing default
```

This example is the test `test/view_tests/views0`. Every behavior described
here is pinned by a test in that directory, and the tests are the most
precise documentation of the semantics.

## Import clauses

An include may carry bracketed clauses. Each clause is a transformation of
the set of names the include provides, and clauses apply left to right.

| clause         | effect on the set of provided names                          |
|----------------|--------------------------------------------------------------|
| `[rename x y]` | the definition known as `x` is now spelled `y`; `x` is gone  |
| `[only a b]`   | keep `a` and `b`, drop everything else                       |
| `[except a]`   | drop `a`                                                     |
| `[as M]`       | every remaining name `n` becomes `M.n`; none stay unqualified |

Order matters because each clause sees the result of the previous one:

```
include "lib.ti" [rename f g] [only keep g]
```

renames `f` to `g` and then keeps `keep` and `g`. With the clauses reversed,
`[only keep]` would drop `f` before the rename, and `g` would name nothing.
For the same reason, exchanging two names takes three renames through a
temporary spelling (`views6`).

`[as M]` makes an import qualified only. To import a module both openly and
under a namespace, write two include lines; their contributions are merged:

```
include "list.ti"
include "list.ti" [as l]
```

A qualified call `(l.map f xs)` means exactly what `(map f xs)` means inside
`list.ti` itself, including anything `list.ti` gets from its own includes.
Qualified names travel like ordinary names: if `mid.ti` contains
`include "deep.ti" [as D]`, then a module that includes `mid.ti` openly can
call `D.g`, and one that includes it `[as M]` can call `M.D.g` (`views19`).
Clauses can mention dotted names, so a namespace member can be pulled back
out as an unqualified name: `[as M] [rename M.f f_direct]` (`views16`). Each
include line carries at most one `[as]`.

## Warnings and errors

Malformed clauses, an empty `[only]` or `[except]`, and a second `[as]` on
one include are link errors with messages that say what to write instead.
Renaming onto a spelling the module still provides is legal but produces a
warning, since the original becomes unreachable:

```
include "lib.ti" [rename fast_sort sort]
  ;; warning: shadows an existing 'sort'; add [except sort] before
  ;; the rename if intentional
```

Writing `[except sort] [rename fast_sort sort]` states the intent and also
silences the warning, because after the `except` the spelling is free
(`views22`). A name that no include provides is a link warning, and calling
it stops the program with `Dispatch failed on method '...'`.

## Inner definitions fall through to the view

A `def` inside a function body creates a local dispatch. When no local case
matches, the call falls through: first to any enclosing scope that binds the
same name, and finally to the module's top-level view of that name, so an
inner definition can extend an imported one. If the name is visible nowhere,
the fall-through is a runtime dispatch failure rather than a compile error,
and no warning is issued, since a purely local name is ordinary code.

```
include "lib.ti"        ;; lib.ti: def (g 5) 505

def (main)
  def (g 1) 101
  {
    (debug_print (write (g 1)))   ;; 101, the local case
    (debug_print (write (g 5)))   ;; 505, fell through to lib.ti
  }
```

For anyone working in the desugar pass, the place to read is
`desugar-and-link-defs` in `rkt/desugar.rkt`. Sibling inner defs are chained
together there, and a final synthesized case re-calls the same name in the
enclosing scope; the head of that call is the core form `(fallback-ref f)`.
The alphatizer (`alphatize` in `rkt/simplify.rkt`) treats `fallback-ref` as
an ordinary reference when an enclosing binding exists, and otherwise records
the name in `soft-globals`, which reaches the linker as the `.soft` sidecar
and turns a missing name into the runtime failure described above. The
trailing-default split for top-level chains sits nearby in `desugar-defs`;
see `default-def?` and `split-trailing-defaults`.

## Where the pieces live

- `rkt/parser.rkt`, `parse-include-clauses`: reads the bracketed clauses as
  raw tokens and folds dotted names into single symbols.
- `rkt/build.rkt`, `setup-build-workspace`: writes `graph.rktd`, the include
  graph with clauses, into the build directory.
- `rkt/compile.rkt`, `qualify-mod`: rewrites each free name in a module to
  `mv_<module>__<name>` and records the sidecars `.globals`, `.used`, `.soft`.
- `rkt/link.rkt`, `resolve-spelling` and `compute-view`: the clause pipeline
  (evaluated in reverse, one name at a time) and the per-module view; the
  linker emits one small dispatcher per module and name into `link/link.cpp`.
- `test/view_tests/`: one directory per example.

To observe a build, run `racket test/test.rkt <file>` and look in
`/tmp/ti/build/<root>/` for `graph.rktd` and `link/link.cpp`, and in
`/tmp/ti/files/<module>/` for each pass's output (`.core`, `.core_alpha`,
`.bl`, `.cpp`) and the sidecar files next to them.
