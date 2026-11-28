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

The package also carries two independent facilities for ML code: a bound on the number of
simplifier steps (structure `Simp_Steps`) and `Simplifier.reset_simp_depth`, each described in its
own section below.

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
Simplifier.assumed_prems : Proof.context -> thm list
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
not count). `assumed_prems ctxt` gives those premises, the ones that assume their own statement, as
theorems in the order of `Simplifier.prems_of ctxt`. A nested simplification with another simpset
has its own premises; add the outer ones with `Simplifier.add_prems` to keep them usable there.

## A bound on the number of simplifier steps

```ML
exception Simp_Steps.EXCEEDED
Simp_Steps.limited : int -> (Proof.context -> 'a) -> Proof.context -> 'a option
Simp_Steps.step : Proof.context -> unit
Simp_Steps.charge : int -> Proof.context -> unit
Simp_Steps.count : Proof.context -> int option
Simp_Steps.inherit : Proof.context -> Proof.context -> Proof.context
```

`limited N f ctxt` (`N ≥ 0`) runs `f` with at most `N` simplifier steps. It gives `f` a context
that carries a new *step counter* with bound `N`, in front of the counters that `ctxt` carries
already (those of the enclosing `limited` calls). The simplifier counts each step on every counter
of its context. There is no option and no Isar syntax: the bound comes from the caller, and on a
context without a counter the simplifier works exactly as before.

```ML
(*ct simplified, or left as it is when that takes more than 10000 steps*)
fun bounded_rewrite ctxt ct =
  (case Simp_Steps.limited 10000 (fn ctxt' => Simplifier.rewrite ctxt' ct) ctxt of
    SOME eq => eq
  | NONE => Thm.reflexive ct);

(*a tactic: its first result is taken inside f*)
val result: thm option option =
  Simp_Steps.limited 10000 (fn ctxt' => SINGLE (asm_full_simp_tac ctxt' 1) st) ctxt;
(*NONE: the bound was reached; SOME NONE: the tactic failed; SOME (SOME st'): it succeeded*)
```

### What a step is

A step is one change of the term that the simplifier has made:

- an instance of a rewrite rule applied, whether the rule was given or made by a simproc; a
  conditional rule once its conditions are proved;
- a congruence rule or congruence procedure applied that changed the term.

Changes made while a condition or a premise of a congruence rule is proved count where they are
made, and the congruence rule they change counts one step more: one rewrite under `d` nested
congruence rules counts `d + 1` steps. What changes nothing is no step: a conditional rule whose conditions fail, a simproc that
gives nothing, a congruence rule that leaves the term as it is, the start of a run. A beta step is
not counted either; beta reduction alone always ends. So a bound ends every simplification that
keeps changing the term; what it does not end is listed under "What is not bounded".

### How steps are counted and refused

A counter that has counted `N` steps *refuses* the next step: `EXCEEDED` is raised. The refused
step is counted as well, once, on every counter of the context. A counter that holds `N + 1`
after that *has reached its bound*: from then on, until its `limited` ends, every step on a
context that carries it is refused and not counted any more. All counters of one context always
change by the same amount.

When `f` ends, `limited` looks at the counters only, whatever `f` did:

1. An interrupt passes through.
2. A counter of an enclosing `limited` has reached its bound: `EXCEEDED` is raised, for that
   `limited` to handle.
3. Otherwise, its own counter has reached its bound: the result is `NONE`, also when `f` caught
   `EXCEEDED` and returned a value or raised another exception.
4. Otherwise the result is that of `f`: `SOME x`, or the exception `f` raised.

So code that catches `EXCEEDED` (`try`, `can`) cannot turn a run that reached its bound into a
result. Nested runs each have their own bound: when `limited 100` reaches its bound inside
`limited 10000`, the inner one returns `NONE` and the outer one goes on, with 101 more steps on
its counter. With the same `N` everywhere, a nested `limited N` never returns `NONE` itself:
`EXCEEDED` passes through it, and the outermost one returns `NONE`.

- `count ctxt` is the count of the innermost counter, or `NONE` outside every `limited`. Read at
  the end of `f` on the context `f` received, it is what this run counted.
- `step ctxt` counts one step, as the simplifier does.
- `charge k ctxt` (`k ≥ 0`) counts `k` steps at once, up to the first refused one. If a counter has
  already reached its bound it raises `EXCEEDED` and counts nothing, also for `k = 0`.
- `inherit from to` puts the counters of `from` on `to`.

### Rules for callers

- **Only the work done before `f` returns is bounded.** The result sequence of a tactic, a closure
  or a `Lazy` value that simplifies after `f` has returned is neither counted nor bounded. Take
  the first result of a tactic inside `f`, with `SINGLE`. A `Lazy` value whose evaluation raises
  `EXCEEDED` keeps that as its result: every later `Lazy.force` raises `EXCEEDED` again, also
  outside every `limited`.
- **Simplify on a context that carries the counter**: the context `f` receives, a context derived
  from it, or, for a context made afresh, `Simp_Steps.inherit ctxt' (Proof_Context.init_global thy)`
  where `ctxt'` is the context `f` received. Steps on any other context (one made afresh without
  `inherit`, one obtained before the call, for example in a tactic built beforehand) are not
  counted by this run.
- **A context that outlives its `limited`** (in a result, a closure, a reference) no longer carries
  that counter: simplification on it is neither counted nor refused by it.
- **To learn whether your own work finished within a bound, put it in a `limited`**, nested or
  not. `count` does not tell whether a step was refused.
- **A cache shared between calls.** Filling it takes steps and a hit takes none, so near the bound
  the result would depend on what the cache holds. To avoid that, run each filling in a `limited`,
  store its result together with the `count` read at the end, and on a hit `charge` the stored
  count inside a `limited` with the same bound, on the same context. Compute the key and look it
  up outside both. Then a hit leaves on every counter what a miss leaves, and ends as the miss
  ends.

  ```ML
  (case lookup key of
    SOME (x, k) => Simp_Steps.limited bound (fn ctxt' => (Simp_Steps.charge k ctxt'; x)) ctxt
  | NONE =>
      (case
        Simp_Steps.limited bound (fn ctxt' => (fill ctxt', the (Simp_Steps.count ctxt'))) ctxt
       of
        SOME (x, k) => (store key (x, k); SOME x)
      | NONE => NONE))
  ```
- **Do not fork tasks that simplify inside a bounded run.** The counters are unsynchronized
  references.
- **Do not use it in a proof of a goal stated beforehand** (`Goal.prove`): reaching the bound
  there is a failed proof. Compute first, state afterwards.
- **Code that catches `EXCEEDED` must not retry forever.**

### What is not bounded

- Work that changes nothing: conditional rules whose conditions fail, again and again down to
  `simp_depth_limit`; simprocs that fail, each call at its own cost; a looper that keeps making
  subgoals on which nothing is changed, which nothing ends, as without this package.
- A single ML procedure that does not return: the body of a simproc or congruence procedure, a
  solver, a looper, a mksimps function or handler, a term order, and the prover of conditions and
  congruence premises (in the simp tactics, the subgoaler), apart from the changes made in the
  runs it starts.
- The cost of one step: terms may grow, so `N` steps are not a bound on time or memory.
- Rewriting outside the simplifier (`Pattern.rewrite_term`, loops of `Conv` combinators).

## A simplification that starts at depth 0 again

```ML
Simplifier.reset_simp_depth : Proof.context -> Proof.context
```

A simpset carries the depth of the simplification that it is taken from. A simplification started
inside another one (by a simproc, a solver or a mksimps handler, with the context that it is
given) goes on from that depth, so `simp_depth_limit` leaves it fewer nested conditional rules,
and under a lowered limit possibly none, than the same simplification started outside.
`reset_simp_depth ctxt` is `ctxt` with its simpset at depth 0 and a new flag for the tracing of
`simp_trace_depth_limit`: `simp_depth_limit` treats a simplification with it as one started
outside (open `Simp_Steps` counters still count its steps). `simp_depth_limit` no longer cuts a
recursion through it; code that starts it again from inside must end by itself.

## Sources

The Isabelle sources a version of this package was made from, with this feature and the ones it is
built on, are a tag of [isabelle-patched](https://github.com/xqyww123/isabelle-patched) named
`<Isabelle release>/generic_mksimps/<m>`, where `<m>` is the last number of the package's
version: version `2026.0.1` was made from `Isabelle2026/generic_mksimps/1`.
