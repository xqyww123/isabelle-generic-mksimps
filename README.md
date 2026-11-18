# generic_mksimps

A simpset can carry a table of *mksimps handlers*, indexed by pattern. Whenever the simplifier
turns a theorem into rewrite rules (a rule given by `simp add:`, `[simp]` or `add_simps`, or a
premise it assumes while simplifying `A ⟹ B`), it first looks the theorem up in the table. A
handler that takes the theorem gives all its rewrite rules and may update the context, for
example to register the premise for its own simprocs. Theorems no handler takes go to the
simpset's mksimps function, as before.

Handlers live in the simpset, separately from the mksimps function: `set_mksimps` does not
remove them, each simpset has its own table, and merging two simpsets keeps the handlers of both.

HOL registers four handlers in `HOL_basic_ss`, for `∧`, `∀`, `⟶` and `If`: each splits the
theorem one step, as HOL's mksimps function does, and dispatches each part again. So a handler for
`group x` also sees the `group G` inside a premise `group G ∧ x ∈ carrier G`. The rules HOL
produces are the same as without this package.

This package changes Isabelle2026 only. It has no Isar syntax.

## The interface

```ML
type Simplifier.mksimps_handler
Simplifier.make_mksimps_handler :
  {patterns: term list, priority: int, kept_by_clear_simpset: bool,
   handler: Proof.context -> thm -> (thm list * Proof.context) option} -> mksimps_handler
Simplifier.add_mksimps_handler : string * mksimps_handler -> Proof.context -> Proof.context
Simplifier.del_mksimps_handler : string -> Proof.context -> Proof.context
Simplifier.mksimps_context : thm -> Proof.context -> thm list * Proof.context
Simplifier.simproc_can_use_thm : Proof.context -> thm -> bool
```

The same names are in `Raw_Simplifier`. `print_simpset` lists the handlers, and
`Simplifier.dest_ss` has a field `mksimps_handlers`.

## How a theorem is dispatched

`mksimps_context thm ctxt` does this:

1. If the table is empty, it calls the mksimps function, exactly as without this package.
2. It matches the conclusion of `Variable.gen_all ctxt thm` against the patterns. Only the
   conclusion counts: `A ⟹ B` is matched by its `B`.
3. It calls the matching handlers by decreasing priority, equal priorities by name, each with
   that theorem (premises included, `maxidx` exact). The first that returns `SOME (rules, ctxt')`
   gives the result; `NONE` passes to the next.
4. If no handler matches, or all return `NONE`, the mksimps function gets the original theorem.

A handler's rules are final. To split a theorem, a handler calls `mksimps_context` on each part;
to keep the default rules, it calls `Simplifier.get_mksimps_context ctxt th ctxt`.

Patterns are propositions, written like simproc patterns with free variables
(`\<^prop>‹group x›`); `add_mksimps_handler` turns the variables not fixed in its context into
schematic ones, as `Simplifier.make_simproc` does. Inside a proof body it leaves them alone, so
register handlers from a theory or local theory context. Priorities are arbitrary integers;
HOL's handlers have priority 0. A handler is identified by its name: adding a handler under an
existing name replaces it, and merging two simpsets keeps the first simpset's handler of a name.
`clear_simpset` (`simp only:`, the `simplified` attribute with theorems) keeps only the handlers
with `kept_by_clear_simpset`; `empty_simpset` removes all.

## Pitfalls

The comments of `add_mksimps_handler` and `simproc_can_use_thm` in `Pure/raw_simplifier.ML` state
them all. The main one: what a handler writes into the context while the simplifier assumes a
premise `P` stays visible in the whole implication, but in the default mode of `simp`, `auto` and
`clarsimp` it must not be used while `P` itself is simplified, after `P` has been rewritten, or
when `P ⟹ C` is rebuilt. Code that takes theorems from such data checks them with
`simproc_can_use_thm ctxt th`: every hypothesis of `th` is assumed by a premise the simplifier
currently holds (a proved fact with the same statement, put there by `Simplifier.add_prems`, does
not count). A nested simplification with another simpset has its own premises; add the outer ones with
`Simplifier.add_prems` to keep them usable there.

## Sources

The Isabelle sources a version of this package was made from, with this feature and the ones it is
built on, are a tag of [isabelle-patched](https://github.com/xqyww123/isabelle-patched) named
`<Isabelle release>/generic_mksimps/<m>`, where `<m>` is the last number of the package's
version: version `2026.0.1` was made from `Isabelle2026/generic_mksimps/1`.
