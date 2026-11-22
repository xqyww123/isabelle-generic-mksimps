(* Checks of the bound on simplifier steps (structure Simp_Steps).  The numbers are those of
   section 8 of ai-artifacts/SIMP_STEP_LIMIT_PLAN.md.  Any failing check fails the build. *)

theory Simp_Steps_Test
  imports Generic_Mksimps_Test_Base
begin

section \<open>Rules for rewriting that does not end\<close>

text \<open>\<open>ping\<close> and \<open>pong\<close> are constant functions, so the equations below are lemmas; as rewrite
  rules \<open>ping_pong\<close> and \<open>pong_ping\<close> undo each other forever.\<close>

definition ping :: "nat \<Rightarrow> nat" where "ping x = 0"
definition pong :: "nat \<Rightarrow> nat" where "pong x = 0"
definition ok :: "nat \<Rightarrow> bool" where "ok x \<longleftrightarrow> True"
consts never :: "nat \<Rightarrow> bool"

lemma ping_pong: "ping x = pong x" by (simp add: ping_def pong_def)
lemma pong_ping: "pong x = ping x" by (simp add: ping_def pong_def)
lemma ping_grow: "ping x = ping (Suc x)" by (simp add: ping_def)
lemma ok: "ok x" by (simp add: ok_def)
lemma ok_ping_grow: "ok x \<Longrightarrow> ping x = ping (Suc x)" by (simp add: ping_def)
lemma never_ping_pong: "never x \<Longrightarrow> ping x = pong x" by (simp add: ping_def pong_def)


section \<open>The events the simplifier reports\<close>

text \<open>The trace operations of this theory log each event into a variable carried by the context.
  A refused step is not logged: \<open>Simp_Steps.step\<close> raises before the trace operation runs.\<close>

ML \<open>
structure Events = Proof_Data
(
  type T = string list Synchronized.var option;
  fun init _ = NONE;
);

fun log_event event ctxt =
  (case Events.get ctxt of
    SOME var => Synchronized.change var (cons event)
  | NONE => ());

(*the result of f on ctxt with a fresh log, and the events logged meanwhile, in order*)
fun logged f ctxt =
  let
    val var = Synchronized.var "events" [];
    val x = f (Events.put (SOME var) ctxt);
  in (x, rev (Synchronized.value var)) end;
\<close>

setup \<open>
  Raw_Simplifier.set_trace_ops
   {trace_invoke = fn _ => fn ctxt => (log_event "run" ctxt; ctxt),
    trace_rrule = fn {unconditional, ...} => fn ctxt => fn cont =>
      (log_event (if unconditional then "rule" else "conditional rule") ctxt; cont ctxt),
    trace_simproc = fn {name, ...} => fn ctxt => fn cont =>
      (log_event ("procedure " ^ name) ctxt; cont ctxt)}
\<close>


section \<open>Helpers\<close>

ML \<open>
(*the result of f under a bound that is not reached, and the steps counted meanwhile*)
fun counted f ctxt =
  the (Simp_Steps.limited 1000000
    (fn ctxt' => let val x = f ctxt' in (x, the (Simp_Steps.count ctxt')) end) ctxt);

(*how a bounded run ends, as the code around it sees it: Reached is the result NONE,
  Exceeded the exception EXCEEDED*)
datatype 'a ending = Returned of 'a | Reached | Exceeded;

fun ending bound f ctxt =
  (case Simp_Steps.limited bound f ctxt of
    SOME x => Returned x
  | NONE => Reached)
  handle Simp_Steps.EXCEEDED => Exceeded;

(*the same, also stored in seen: for a run whose enclosing run does not return a value*)
fun nested seen bound f ctxt =
  let val e = ending bound f ctxt
  in seen := SOME e; e end;

fun string_of_ending (Returned _) = "Returned"
  | string_of_ending Reached = "Reached"
  | string_of_ending Exceeded = "Exceeded";

fun is_reached Reached = true
  | is_reached _ = false;

fun steps n ctxt = if n <= 0 then () else (Simp_Steps.step ctxt; steps (n - 1) ctxt);

(*HOL_basic_ss with these rules*)
fun basic_ss ths ctxt = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps ths;

(*rewriting that does not end: the rules ping_pong and pong_ping*)
fun spin ctxt =
  ignore (Simplifier.rewrite (basic_ss @{thms ping_pong pong_ping} ctxt) \<^cterm>\<open>ping n\<close>);

(*rewriting that ends, with the simpset of the theory*)
fun finite ctxt =
  ignore (Simplifier.rewrite ctxt \<^cterm>\<open>rev (rev [a, b, c, d::nat]) @ [e] = [a, b] @ us\<close>);

(*the cache of section 5 of the plan, with one entry: a miss runs fill in a bounded run and
  stores its result with the steps it counted; a hit charges them in a bounded run like it*)
fun cached cache bound fill ctxt =
  (case ! cache of
    SOME (x, k) => Simp_Steps.limited bound (fn ctxt' => (Simp_Steps.charge k ctxt'; x)) ctxt
  | NONE =>
      (case
        Simp_Steps.limited bound
          (fn ctxt' => (fill ctxt', the (Simp_Steps.count ctxt'))) ctxt
       of
        SOME (x, k) => (cache := SOME (x, k); SOME x)
      | NONE => NONE));
\<close>


section \<open>0. Without a bound\<close>

ML \<open>
local
  val ctxt = \<^context>;
in
  val _ = check "0: no counter outside a bounded run" (Simp_Steps.count ctxt = NONE);
  val _ = steps 1000 ctxt;
  val _ = Simp_Steps.charge 1000 ctxt;
  val _ = check "0: steps without a counter leave none" (Simp_Steps.count ctxt = NONE);

  val _ = check "0: bound 0, no step" (Simp_Steps.limited 0 (K 1) ctxt = SOME 1);
  val _ = check "0: bound 0, one step" (Simp_Steps.limited 0 Simp_Steps.step ctxt = NONE);
  val _ =
    check "0: the count starts at 0"
      (Simp_Steps.limited 5 Simp_Steps.count ctxt = SOME (SOME 0));
  val _ =
    check "0: the count of a run that ends" (#2 (counted finite ctxt) > 1);
end;
\<close>


section \<open>1. Each kind of step is refused at step N + 1\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val ct = \<^cterm>\<open>ping n\<close>;

  (*a run that does not end: under bound 20 it gives NONE, the counter outside holds 21 (the
    refused step counts once), 20 events were reported, kind among them*)
  fun check_refused name kind f =
    let val ((e, n), events) = logged (counted (ending 20 f)) ctxt in
      check_showing ("1: " ^ name)
        (fn () => string_of_ending e ^ ", " ^ string_of_int n ^ " steps, events: " ^ commas events)
        (is_reached e andalso n = 21 andalso length events = 20 andalso
          member (op =) events kind)
    end;

  val grow =
    Simplifier.make_simproc ctxt
     {name = "grow", kind = Simplifier.Simproc, lhss = [\<^term>\<open>ping x\<close>],
      proc = fn _ => fn _ => fn ct =>
        SOME (Thm.instantiate' [] [SOME (Thm.dest_arg ct)] @{thm ping_grow [THEN eq_reflection]}),
      identifier = []};

  (*a congruence procedure that keeps the simplifier out of the argument of ping*)
  val ping_cong =
    Simplifier.make_simproc ctxt
     {name = "ping_cong", kind = Simplifier.Congproc false, lhss = [\<^term>\<open>ping x\<close>],
      proc = fn _ => fn _ => fn ct => SOME (Thm.reflexive ct), identifier = []};

  fun rewrite_in ctxt' = ignore (Simplifier.rewrite ctxt' ct);
in
  (*the premises a = b and b = a, as rules for the conclusion*)
  val _ =
    check_refused "rules from premises, in a tactic" "rule" (fn ctxt' =>
      SINGLE (asm_full_simp_tac (put_simpset HOL_basic_ss ctxt') 1)
        (Goal.init \<^cprop>\<open>a = b \<and> b = a \<Longrightarrow> never a\<close>));

  val _ = check_refused "unconditional rules" "rule" spin;

  val _ =
    check_refused "a simproc that always gives an equation" "procedure grow"
      (rewrite_in o Simplifier.add_proc grow o basic_ss []);

  val _ =
    check_refused "a conditional rule, its condition proved by simplification"
      "conditional rule" (rewrite_in o basic_ss @{thms ok ok_ping_grow});

  val _ =
    check_refused "a congruence procedure" "procedure ping_cong"
      (rewrite_in o Simplifier.add_proc ping_cong o basic_ss @{thms ping_pong pong_ping});

  (*a looper that makes a subgoal on which no step is made: only the starts of runs count*)
  val _ =
    let
      fun f ctxt' =
        SINGLE
          (simp_tac (put_simpset HOL_basic_ss ctxt' |> Simplifier.set_loop (fn _ => K all_tac)) 1)
          (Goal.init \<^cprop>\<open>never a\<close>);
      val ((e, n), events) = logged (counted (ending 20 f)) ctxt;
    in
      check_showing "1: a looper, stopped by the starts of runs alone"
        (fn () => string_of_ending e ^ ", " ^ string_of_int n ^ " steps, events: " ^ commas events)
        (is_reached e andalso n = 21 andalso events = replicate 20 "run")
    end;

  (*a conditional rule counts when its condition is not proved, too*)
  val _ =
    let
      val ((eq, n), events) =
        logged (counted (fn ctxt' =>
          Simplifier.rewrite (basic_ss @{thms never_ping_pong} ctxt') ct)) ctxt;
    in
      check_showing "1: a conditional rule whose condition fails"
        (fn () => string_of_int n ^ " steps, events: " ^ commas events)
        (Thm.is_reflexive eq andalso n = length events andalso
          member (op =) events "conditional rule")
    end;

  (*a run that ends within its bound, and one step short of it*)
  val _ =
    let val m = #2 (counted finite ctxt) in
      check "1: exactly the steps of the run suffice" (ending m finite ctxt = Returned ());
      check "1: one step less does not" (ending (m - 1) finite ctxt = Reached)
    end;

  (*a tactic gives its first result inside the bounded run*)
  val _ =
    let
      val st = Goal.init \<^cprop>\<open>rev (rev xs) = xs\<close>;
      fun result i =
        Simp_Steps.limited 10000 (fn ctxt' => SINGLE (asm_full_simp_tac ctxt' i) st) ctxt;
    in
      check "1: a tactic that succeeds"
        (case result 1 of SOME (SOME st') => Thm.no_prems st' | _ => false);
      check "1: a tactic that fails" (case result 2 of SOME NONE => true | _ => false)
    end;
end;
\<close>


section \<open>2. The steps of a simplification started by a simproc count on the caller's counter\<close>

ML \<open>
local
  val ctxt = \<^context>;

  (*only the simplification that the simproc starts does not end*)
  val nested_run =
    Simplifier.make_simproc ctxt
     {name = "nested_run", kind = Simplifier.Simproc, lhss = [\<^term>\<open>ping x\<close>],
      proc = fn _ => fn ctxt' => fn _ => (spin ctxt'; NONE), identifier = []};

  fun f ctxt' =
    ignore (Simplifier.rewrite (basic_ss [] ctxt' |> Simplifier.add_proc nested_run) \<^cterm>\<open>ping n\<close>);

  val ((e, n), events) = logged (counted (ending 20 f)) ctxt;
in
  val _ =
    check_showing "2: the nested simplification reaches the caller's bound"
      (fn () => string_of_ending e ^ ", " ^ string_of_int n ^ " steps, events: " ^ commas events)
      (e = Reached andalso n = 21 andalso
        take 3 events = ["run", "procedure nested_run", "run"] andalso
        drop 3 events = replicate 17 "rule");
end;
\<close>


section \<open>3. Nested bounded runs\<close>

ML \<open>
local
  val ctxt = \<^context>;
  fun seen () = Unsynchronized.ref (NONE: unit ending option);
in
  (*the inner bound is smaller: the inner run gives NONE, the outer run goes on; its count
    holds the inner steps and the refused one*)
  val _ =
    check "3: the inner bound is reached" (counted (ending 10 spin) ctxt = (Reached, 11));

  (*the outer bound is reached first*)
  val _ =
    let val inner = seen () in
      check "3: the outer bound is reached first"
        (counted (ending 10 (ignore o nested inner 1000 spin)) ctxt = (Reached, 11) andalso
          ! inner = SOME Exceeded)
    end;

  (*both bounds are the same, the inner run starts before the outer one makes a step*)
  val _ =
    let val inner = seen () in
      check "3: equal bounds"
        (counted (ending 10 (ignore o nested inner 10 spin)) ctxt = (Reached, 11) andalso
          ! inner = SOME Exceeded)
    end;

  (*the outer run has swallowed its EXCEEDED before the inner run starts*)
  val _ =
    let val inner = seen () in
      check "3: an inner run started after the outer bound was reached"
        (counted (ending 10 (fn ctxt' =>
            (ignore (try spin ctxt'); ignore (nested inner 1000 (K ()) ctxt')))) ctxt =
          (Reached, 11) andalso ! inner = SOME Exceeded)
    end;

  (*three runs, the middle and the innermost reach their bounds at the same step*)
  val _ =
    let val middle = seen () and innermost = seen () in
      check "3: three runs"
        (counted (ending 1000 (ignore o nested middle 10 (ignore o nested innermost 10 spin)))
            ctxt = (Returned (), 11) andalso
          ! middle = SOME Reached andalso ! innermost = SOME Exceeded)
    end;

  (*the step that the inner run is refused fills the outer counter exactly*)
  val _ =
    let val inner = seen () in
      check "3: the refused inner step fills the outer counter"
        (counted (ending 100 (fn ctxt' =>
            (steps 89 ctxt'; ignore (nested inner 10 spin ctxt'); Simp_Steps.count ctxt'))) ctxt =
          (Returned (SOME 100), 100) andalso ! inner = SOME Reached);
      check "3: one more step on the filled outer counter"
        (counted (ending 100 (fn ctxt' =>
            (steps 89 ctxt'; ignore (nested inner 10 spin ctxt'); Simp_Steps.step ctxt'))) ctxt =
          (Reached, 101) andalso ! inner = SOME Reached)
    end;

  (*a context that leaves the inner run: afterwards it carries the outer counter only*)
  val _ =
    let
      val m = #2 (counted finite ctxt);
      val escaped = Unsynchronized.ref NONE;
      fun f ctxt' =
        let
          val e = ending 10 (fn ctxt'' => (escaped := SOME ctxt''; spin ctxt'')) ctxt';
          val ctxt'' = the (! escaped);
          val n = Simp_Steps.count ctxt'';
          val _ = steps 20 ctxt'';
          val _ = finite ctxt'';
        in (e, n, Simp_Steps.count ctxt'') end;
    in
      check "3: a context that leaves the inner run"
        (counted f ctxt = ((Reached, SOME 11, SOME (31 + m)), 31 + m))
    end;
end;
\<close>


section \<open>4. and 5. The result depends on the counters only\<close>

ML \<open>
local
  val ctxt = \<^context>;
in
  val _ =
    check "4: EXCEEDED swallowed by try"
      (Simp_Steps.limited 10 (fn ctxt' => (ignore (try spin ctxt'); "half done")) ctxt = NONE);

  val _ =
    let val inner = Unsynchronized.ref NONE in
      check "4: EXCEEDED of the outer run swallowed inside the inner run"
        (counted (ending 10 (ignore o nested inner 1000 (ignore o try spin))) ctxt =
          (Reached, 11) andalso ! inner = SOME Exceeded)
    end;

  val _ =
    check "5: EXCEEDED turned into another exception"
      (Simp_Steps.limited 10 (fn ctxt' => spin ctxt' handle Simp_Steps.EXCEEDED => error "other")
        ctxt = NONE);

  val _ =
    check "5: an exception of a run within its bound passes"
      ((ignore (Simp_Steps.limited 10 (fn _ => error "boom") ctxt); false)
        handle ERROR "boom" => true);
end;
\<close>


section \<open>6. A context that outlives its bounded run\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val kept = Unsynchronized.ref NONE;

  fun check_closed name =
    let val ctxt' = the (! kept) in
      check ("6: " ^ name ^ ": no counter") (Simp_Steps.count ctxt' = NONE);
      steps 100 ctxt';
      finite ctxt';
      check ("6: " ^ name ^ ": steps do not count") (Simp_Steps.count ctxt' = NONE);
      check ("6: " ^ name ^ ": a new run counts from 0")
        (Simp_Steps.limited 10 (fn ctxt'' => (steps 2 ctxt''; Simp_Steps.count ctxt'')) ctxt' =
          SOME (SOME 2))
    end;
in
  val _ =
    check "6: a run within its bound"
      (Simp_Steps.limited 10 (fn ctxt' => kept := SOME ctxt') ctxt = SOME ());
  val _ = check_closed "after a run within its bound";

  val _ =
    check "6: a run that reaches its bound"
      (Simp_Steps.limited 10 (fn ctxt' => (kept := SOME ctxt'; spin ctxt')) ctxt = NONE);
  val _ = check_closed "after a run that reached its bound";
end;
\<close>


section \<open>7. \<open>count\<close> and \<open>charge\<close>\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val thy = \<^theory>;
in
  (*what is counted is what the simplifier reports, for the simpset of the theory*)
  val _ =
    let val (((), n), events) = logged (counted finite) ctxt in
      check_showing "7: the count is the number of reported events"
        (fn () => string_of_int n ^ " steps, events: " ^ commas events) (n = length events)
    end;

  val _ =
    check "7: charge counts on every open counter"
      (counted (ending 50 (fn ctxt' => (Simp_Steps.charge 7 ctxt'; Simp_Steps.count ctxt'))) ctxt =
        (Returned (SOME 7), 7));

  (*a charge that does not fit counts up to the refused step: 90 + 10 + 1*)
  val _ =
    let val raised = Unsynchronized.ref false in
      check "7: a charge that does not fit"
        (counted (ending 100 (fn ctxt' =>
            (steps 90 ctxt';
             Simp_Steps.charge 30 ctxt' handle Simp_Steps.EXCEEDED => raised := true))) ctxt =
          (Reached, 101) andalso ! raised)
    end;

  (*only the first refused step counts*)
  val _ =
    check "7: refused steps after the bound was reached do not count"
      (counted (ending 10 (fn ctxt' => ignore (map (fn _ => try spin ctxt') (1 upto 50)))) ctxt =
        (Reached, 11));

  (*a cache hit leaves what a miss leaves.  The filling ends with a nested run that reaches its
    own bound, which the filling accepts; it counts 6 steps.*)
  val _ =
    let
      fun fill ctxt' = ignore (ending 5 spin ctxt');
      val k = #2 (counted fill ctxt);

      (*a lookup in a run that has room for r more steps*)
      fun lookup cache r =
        counted (ending 100 (fn ctxt' =>
          (steps (100 - r) ctxt'; cached cache 1000 fill ctxt'))) ctxt;

      fun check_room r expected =
        let
          val cold = Unsynchronized.ref NONE;
          val warm = Unsynchronized.ref (SOME ((), k));
          val miss = lookup cold r;
          val hit = lookup warm r;
        in
          check ("7: a miss with room " ^ string_of_int r) (miss = expected);
          check ("7: a hit with room " ^ string_of_int r) (hit = expected);
          check ("7: what a miss with room " ^ string_of_int r ^ " stores")
            (! cold = (if r < k then NONE else SOME ((), k)))
        end;
    in
      check "7: the count of the filling" (k = 6);
      check_room (k - 1) (Reached, 101);
      check_room k (Returned (SOME ()), 100);
      check_room (k + 1) (Returned (SOME ()), 99)
    end;

  (*one key under two bounds: filled under 1000 with 60 steps, looked up under 50*)
  val _ =
    let
      val fill = steps 60;
      val warm = Unsynchronized.ref NONE;
      val cold = Unsynchronized.ref NONE;
    in
      check "7: a filling of 60 steps" (cached warm 1000 fill ctxt = SOME ());
      check "7: its entry" (! warm = SOME ((), 60));
      check "7: a miss under a smaller bound" (counted (cached cold 50 fill) ctxt = (NONE, 51));
      check "7: a miss under a smaller bound stores nothing" (! cold = NONE);
      check "7: a hit under a smaller bound" (counted (cached warm 50 fill) ctxt = (NONE, 51))
    end;

  (*the filling runs on a new context that does not inherit*)
  val _ =
    let
      val fill = steps 60;
      val cache = Unsynchronized.ref NONE;
      fun lookup _ = cached cache 1000 fill (Proof_Context.init_global thy);
    in
      check "7: a miss on a new context" (counted lookup ctxt = (SOME (), 0));
      check "7: a hit on a new context" (counted lookup ctxt = (SOME (), 0))
    end;

  (*charge 0 raises once a counter has reached its bound, and counts nothing*)
  val _ =
    let
      val inner = Unsynchronized.ref NONE;
      val raised = Unsynchronized.ref false;
      fun f ctxt' =
       (steps 50 ctxt';
        ignore (nested inner 10 (fn ctxt'' =>
         (ignore (try spin ctxt'');
          steps 39 ctxt';
          Simp_Steps.charge 0 ctxt'' handle Simp_Steps.EXCEEDED => raised := true)) ctxt');
        Simp_Steps.count ctxt');
    in
      check "7: charge 0 after a counter has reached its bound"
        (ending 100 f ctxt = Returned (SOME 100) andalso ! inner = SOME Reached andalso ! raised);
      check "7: charge 0 on a full counter"
        (Simp_Steps.limited 5 (fn ctxt' =>
            (steps 5 ctxt'; Simp_Steps.charge 0 ctxt'; Simp_Steps.count ctxt')) ctxt =
          SOME (SOME 5))
    end;
end;
\<close>


section \<open>8. \<open>inherit\<close>\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val thy = \<^theory>;
  val m = #2 (counted finite ctxt);

  (*steps on a new context made from the theory by make, inside a nested run: the count of the
    nested run, and that of the run around it*)
  fun on_new_context make =
    counted (ending 100000 (fn ctxt'' =>
      let val new = make ctxt'' (Proof_Context.init_global thy)
      in steps 7 new; finite new; Simp_Steps.count ctxt'' end));
in
  val _ =
    check "8: steps on a context that inherits count on both counters"
      (on_new_context Simp_Steps.inherit ctxt = (Returned (SOME (7 + m)), 7 + m));

  val _ =
    check "8: steps on a context that does not inherit count on neither"
      (on_new_context (K I) ctxt = (Returned (SOME 0), 0));

  (*inheriting from the context given to limited misses the counter of that run*)
  val _ =
    check "8: inheriting from the context given to the run"
      (counted (fn ctxt' =>
          ending 100 (fn ctxt'' =>
            let val new = Simp_Steps.inherit ctxt' (Proof_Context.init_global thy)
            in steps 7 new; Simp_Steps.count ctxt'' end) ctxt') ctxt =
        (Returned (SOME 0), 7));
end;
\<close>


section \<open>9. and 10. Without a counter, and under a bound that is not reached\<close>

text \<open>The results were recorded on Isabelle2026 without the feature, with the simpset of \<open>Main\<close>;
  each is the right-hand side that \<open>Simplifier.asm_full_rewrite\<close> gives, printed.\<close>

ML \<open>
val baseline =
 [("(x::nat) + 0 = x", "True"),
  ("rev (rev xs) = xs", "True"),
  ("length (xs @ ys)", "length xs + length ys"),
  ("if True then a else (b::nat)", "a"),
  ("(a::nat) < b \<longrightarrow> a \<le> b", "True"),
  ("map k (xs @ [x])", "map k xs @ [k x]"),
  ("x \<in> A \<union> B", "x \<in> A \<or> x \<in> B"),
  ("Suc n * m", "m + n * m"),
  ("set (x # xs)", "insert x (set xs)"),
  ("fst (a, b) = c", "a = c"),
  ("case Some x of None \<Rightarrow> a | Some y \<Rightarrow> k y", "k x"),
  ("A \<and> (A \<longrightarrow> B)", "A \<and> (A \<longrightarrow> B)"),
  ("\<exists>y. y = a \<and> p y", "p a"),
  ("(2::nat) + 3 * 4", "14"),
  ("xs \<noteq> [] \<longrightarrow> hd xs # tl xs = xs", "True"),
  ("(a::int) * (b + c)", "a * (b + c)"),
  ("length xs < length (x # xs)", "True"),
  ("\<forall>y. y = a \<longrightarrow> p y", "p a"),
  ("(if x = y then (1::nat) else 2) = 1", "(if x = y then 1 else 2) = Suc 0"),
  ("filter (\<lambda>y. True) xs", "xs"),
  ("xs = ys \<Longrightarrow> length xs = length ys", "True"),
  ("(a::nat) \<le> b \<Longrightarrow> a < Suc b", "True")];
\<close>

ML \<open>
local
  val ctxt = \<^context>;

  fun rewrite ctxt' input =
    Simplifier.asm_full_rewrite ctxt' (Thm.cterm_of ctxt (read_term ctxt input));
  val result = plain ctxt o Thm.term_of o Thm.rhs_of;
in
  val _ =
    baseline |> List.app (fn (input, expected) =>
      let
        val eq = rewrite ctxt input;
        val bounded = Simp_Steps.limited 1000000 (fn ctxt' => rewrite ctxt' input) ctxt;
        val ((_, n), events) = logged (counted (fn ctxt' => rewrite ctxt' input)) ctxt;
      in
        check_showing ("9: " ^ input) (fn () => result eq) (result eq = expected);
        check ("10: " ^ input)
          (case bounded of
            SOME eq' => Thm.prop_of eq' aconv Thm.prop_of eq
          | NONE => false);
        check_showing ("7: events of " ^ input)
          (fn () => string_of_int n ^ " steps, events: " ^ commas events) (n = length events)
      end);
end;
\<close>


section \<open>11. Bounded runs in parallel\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val m = #2 (counted finite ctxt);
in
  val _ =
    check "11: parallel runs that reach their bounds"
      (forall (fn r => r = (Reached, 11))
        (Par_List.map (fn _ => counted (ending 10 spin) ctxt) (1 upto 8)));

  val _ =
    check "11: parallel runs that just fit their bounds"
      (forall (fn r => r = Returned ())
        (Par_List.map (fn _ => ending m finite ctxt) (1 upto 8)));
end;
\<close>


section \<open>12. Interrupts\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val kept = Unsynchronized.ref NONE;

  fun check_closed name =
    let val ctxt' = the (! kept) in
      check ("12: " ^ name ^ ": no counter") (Simp_Steps.count ctxt' = NONE);
      steps 100 ctxt';
      finite ctxt';
      check ("12: " ^ name ^ ": steps do not count") (Simp_Steps.count ctxt' = NONE)
    end;
in
  (*a timeout is not turned into NONE*)
  val _ =
    check "12: a timeout passes"
      ((ignore (Timeout.apply (Time.fromMilliseconds 500) (fn () =>
          Simp_Steps.limited 1000000000 (fn ctxt' => (kept := SOME ctxt'; spin ctxt')) ctxt) ());
        false) handle Timeout.TIMEOUT _ => true);
  val _ = check_closed "after a timeout";

  val _ =
    check "12: an interrupt raised by the function passes"
      (case
        Exn.capture0 (fn () =>
          Simp_Steps.limited 10
            (fn ctxt' => (kept := SOME ctxt'; raise Exn.Interrupt_Break)) ctxt) ()
       of
        Exn.Exn Exn.Interrupt_Break => true
      | _ => false);
  val _ = check_closed "after an interrupt";
end;
\<close>

end
