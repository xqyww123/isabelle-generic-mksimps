# simplifier 的步数上限（`generic_mksimps` 的一部分）：方案，第四稿

会话"simplifier 限步数"写（它是从会话"concept B"fork 出来的）。
状态：**第四稿（2026-11-22 15:53 UTC）；第四轮评审判"可以接受"，它的更正（F25 至 F27）已于 16:31 UTC 改入；作者 16:38「很好，批准开工」；代码、测试、清单、README 于 16:57 写完，17:10 构建通过，已提交；代码评审 17:40 判可以接受，它的修改于 11-23 02:27 做完、02:36 构建通过并提交，作者同时下令推送（第 11 节）。**
作者 16:39 另两句：对两个 REPL 探针「交给你自决了」；「提交方案」（本文件 16:40 提交为 `8b830b3`，没有推送）。构建、代码的提交、推送、release 仍然每一步等他下令。
作者 17:03：「批准构建」「批准新文件提交」「请进行代码评审」。构建 17:04 起（私有树，session `Generic_Mksimps_Test`）；代码评审 17:05 起（`wf_c3226e55-994`）。结果记在第 11 节末尾。
第 10 节列的十一项设计，作者还没有逐条看过。
第 2 至 6 节里的代码草稿与例子没有编译过；真正写下的代码与它们的出入、以及哪些已经验证过，见第 11 节。源码事实都是读源码得到的，行号以本 feature 的私有树
`contrib/generic_mksimps/worktrees/Isabelle2026-generic_mksimps/src/`（提交 `1aa94bd`）为准，下面写路径时省去这一段。

标法：
- 「」里只放作者的原话，后面跟 2026-11-22 的 UTC 时刻；出处是转录 `8a2e8d7f-26d1-4bbc-8866-34b3ac8d6b12.jsonl`（fork 之前）与
  `de98ca97-2c00-4887-ba71-e437b62616bf.jsonl`（fork 之后）。
- 【已定】作者明说过的。【本会话的设计】作者交给本会话定、还没有逐条看过的（清单在第 10 节）。【实现】实现层面的选择。

## 0. 术语

- **simplifier 的一次运行**：`Raw_Simplifier.rewrite_cterm` 的一次调用（`simp`、`auto` 里的化简、`Simplifier.rewrite`、`rewrite_rule`、`unfold` 最后都落到它）。
- **步**：本设施计数的一个事件，定义在第 3 节。
- **步数计数器**：一个 `Unsynchronized.ref`，连同它的上限。一次受限的运行有它自己的一个。
- **上限**：一个步数计数器允许的步数 N（N ≥ 0），由调用方给。
- **受限的运行**：经 `Simp_Steps.limited` 运行的一段 ML 代码（第 2 节）。受限的运行可以一个套一个；套在外面的叫外层，套在里面的叫里层。
- **开着的、已结束的步数计数器**：一次受限的运行开始时，它的计数器成为开着的；这次运行一结束（无论怎样结束）就成为已结束的，从此不计数、不引起拒绝。
- **context 带着的计数器**：context 里存着一列步数计数器，最里层的在前；它们是造这个 context 时所在的各层受限运行的计数器。
- **余地**：一个开着的计数器的上限减去它已经记的步数。余地是 0 就是已经记满 N 步。
- **一步被拒绝、计数器到达上限**：要走一步时，context 带着的开着的计数器里若有一个没有余地，或者已经到达了上限，这一步就被拒绝（抛异常 `EXCEEDED`）。
  - 若此前它们都还没有到达上限：这被拒绝的一步照样在每一个上面记一次。于是没有余地的那些记成了 N+1，这就叫**到达了上限**。
  - 若其中已经有一个到达了上限：这一步哪个都不记。
  到达了上限的计数器，只要还开着，就拒绝之后的每一步。
- **新造的 context**：受限的运行里面的代码从 theory 造出来的 context（`Proof_Context.init_global`），它不带调用处 context 的任何数据。

## 1. 本质、来由与状态

**本质**：simplifier 每走一步，就在 context 带着的每个开着的计数器上加一。调用方可以让一段代码"至多走 N 步"；要走第 N+1 步时这段代码被中止，调用方得知"到了上限"。
没有人设上限时，simplifier 的行为与 stock 完全相同。

**来由**。feature `concept` 的类型层有一个内部的 simpset（selector Simpset），有些项会让它不停地化简下去，例如
`group (f ((a = b ∧ b = a) ⟶ P a))`：`⟶` 左边的两条等式被当成两条互相撤销的改写规则。
作者先定的是限时：「建议给超时 50ms，超时后就不化简」（07:20）。限时的结果随机器快慢而变，于是：
- 12:10：「很好的提醒。我们可以限制 simplification 的步数吗？」
- 12:33：「同意。建议设置 Proof.context 下一个 Unsynchronized.ref 来做 counter，重置前所有的 rewrite 等 step 无论是当下的还是 nested simproc 中的都累加，然后受限」
- 13:07：「simplifier 的步数限制这个之后要单独做一个 feature package，交给一个单独的 agent 去做（会从你这里 fork）」
- 13:13（对本会话）：「很好，我 fork 了你，现在你专门来负责 限步数的方案」「请建一个专门的 feature repository 用 gh 要 public，名字自拟」「请书写方案，然后启动评审」

**放在哪里**【已定】。初稿把它做成单独的 feature `simp_step_limit`。之后：
- 13:24 作者对初稿"待作者定"的几条：名字「好」；不给用户做 Config 选项「好」；「可以开树了，然后等评审通过」。
- 开树之前本会话重读 SKILL isabelle-patch-feature，发现初稿里"每个 feature 只有一个 base"已不成立，停下来问；树没有开。
- 13:30 作者：「我们直接做进 generic_mksimps 里你觉得怎样？」；13:33：「定了」，并「允许」本会话动 `generic_mksimps` 的私有树；
  为它建的空仓库 `xqyww123/isabelle-simp-step-limit`「我之后删除」；方案作为单独的一份文件放在这里、`GENERIC_MKSIMPS_PLAN.md` 只加一句指路（「按你建议来」）。
- 所以：没有新的分支、新的包；`concept` 的 base 不变。

**评审**（题目 `simp_step_limit_review_brief_2026-11-22.md`，报告在同目录，都不提交）：
- 第一轮（`wf_20c56b08-3f4`，报告 `…_round1_…`）：还不能接受；十条意见七条成立。第二稿照它的 F1 至 F8 改，并照作者 14:25 的两句话改了两处设计（第 10 节第 1、2 项）。
- 第二轮（`wf_33a6765b-940`，报告 `…_round2_…`）：还不能接受；七条意见都成立，两处要实质改动。第三稿照它的 F9 至 F17 改。
- 第三轮（`wf_7ff4082a-528`，报告 `…_round3_…`）：还不能接受；六条意见都成立、都是更正，另有裁判自己查出的一处实质改动（被拒绝的步怎样记）。本稿照它的 F18 至 F24 改。
  三轮的实质改动都在作者 14:25 交给本会话的嵌套设计之内。
- 第四轮（`wf_d043f1f2-44c`，报告 `…_round4_…`）：**可以接受**；五条意见四条成立，都是不必再过一轮的更正（F25 至 F27 与一处行号），已改入本稿；没有要作者定的。
  其中 F26 改了第 5 节"缓存"的一条规矩（命中时的 `charge` 也放进与填充相同的 `limited`）。

**stock 为什么不够**（都读过源码）：
- `simp_depth_limit`（默认 40，`Pure/raw_simplifier.ML:562` 声明、`:1255` 使用）只管带条件的规则一层套一层证条件的深度；上面那个例子深度不变，它拦不住。
- simplifier 的跟踪钩子（`Trace_Ops`，`Pure/raw_simplifier.ML:1097-1112`）看得见每一步，但它是 theory 数据里的一个槽，合并时只留第一个 parent 的值
  （`fun merge (trace_ops, _) = trace_ops`），而且 `Pure/Tools/simplifier_trace.ML` 在 Pure 里已经占了它，又没有读出旧值的函数。借它计数，在 `imports Main …` 的 theory 里会被悄悄顶掉。
- 一个匹配任意项的 simproc 看不到规则引起的循环：`rewritec` 先试规则、规则都不适用才试 simproc（`:1316-1317`）。

## 2. 接口【名字已定，作者 13:24「好」；含义是本会话的设计】

一个新的 Pure 文件 `Pure/simp_steps.ML`，结构 `Simp_Steps`：

```ML
signature SIMP_STEPS =
sig
  exception EXCEEDED
  val limited: int -> (Proof.context -> 'a) -> Proof.context -> 'a option
  val step: Proof.context -> unit
  val charge: int -> Proof.context -> unit
  val count: Proof.context -> int option
  val inherit: Proof.context -> Proof.context -> Proof.context
end;
```

各项的含义：

- **`limited N f ctxt`**：在"至多 N 步"之下运行 `f`。
  - 它造一个新的步数计数器（从 0 起、上限 N），放到 `ctxt` 带着的那些开着的计数器的前面，在这个新的 context 上算 `f`。
    `ctxt` 原先带着的开着的计数器照旧在后面，所以 `f` 里的每一步同时记在各层上。
  - `f` 一结束（无论怎样结束），这个计数器就成为已结束的。然后**只看计数器**来定结果，依次是：
    1. `f` 是被中断打断的（用户取消、外层工具的定时器）：中断原样放行。
    2. 外面某一层开着的计数器到达了上限：抛 `EXCEEDED`，交给那一层去处理。不管 `f` 做了什么，也不管它自己的计数器是不是也到达了上限。
    3. 否则，它自己的计数器到达了上限：交回 `NONE`。不管 `f` 是抛了 `EXCEEDED`、抛了别的异常、还是正常返回了一个值。
    4. 都没有：`f` 正常返回 `x` 就交回 `SOME x`；`f` 抛了异常就原样再抛。
- **`step ctxt`**：计一步。simplifier 调它（第 3 节）；别的代码一般不需要调。
  - `ctxt` 没有开着的计数器：什么都不做。
  - 每个开着的计数器都还有余地：各加一。
  - 否则这一步被拒绝：若还没有哪个开着的计数器到达了上限，照样各加一；然后抛 `EXCEEDED`。
- **`charge k ctxt`**（k ≥ 0）：它在 `ctxt` 带着的计数器上留下的，恰好是一次记了 k 步（在它的 `f` 末尾用 `count` 读到 k）的缓存填充会留下的：照 `step` 的规矩一步一步地记 k 步，记到被拒绝的那一步为止；
  若已经有一个开着的计数器到达了上限，它什么都不记、直接抛 `EXCEEDED`，k = 0 时也一样（那次填充的 `limited` 结束时同样会抛，上面的第 2 种情形）。用处见第 5 节"缓存"。
- **`count ctxt`**：最里层那个开着的计数器上记的数；没有开着的计数器时是 `NONE`。这个计数器到达了上限之后，读到的是 N+1。
  在 `f` 里面、对 `f` 收到的 context 读，读到的是这一层受限的运行开始以来记的数。它也可以用来问"现在是不是在受限的运行里面"。
- **`inherit from to`**：把 `from` 带着的开着的计数器放到 `to` 上。用于受限的运行里面新造的 context（第 5 节）。
- **`EXCEEDED`**：一步被拒绝时抛的异常，不带参数。它不是中断。

两个例子（HOL 里，没有运行过）：

```ML
(*把 ct 化简；走了 10000 步还没完就原样交回*)
fun bounded_rewrite ctxt ct =
  (case Simp_Steps.limited 10000 (fn ctxt' => Simplifier.rewrite ctxt' ct) ctxt of
    SOME eq => eq
  | NONE => Thm.reflexive ct);

(*tactic：第一个结果要在 f 里面取出来（第 5 节"交出去以后才做的工作"）*)
val result: thm option option =
  Simp_Steps.limited 10000 (fn ctxt' => SINGLE (asm_full_simp_tac ctxt' 1) st) ctxt;
(*NONE：到了上限；SOME NONE：tactic 失败；SOME (SOME st')：成功*)
```

接口保证的四件事（实现后各有测试，第 8 节）：
1. **不设上限就没有变化**：context 没有开着的计数器时，`step` 立刻返回，simplifier 的结果与 stock 相同。
2. **至多 N 步**：一次 `limited N f`，在 `f` 返回之前，在带着它的计数器的 context 上至多走 N 步；里面嵌套的 simproc、嵌套的 `limited`、`inherit` 过去的 context 上的步都算在内。
   **一个 context 带着的开着的计数器总是一起变**：每走一步各加一，被拒绝的一步也各加一，除非其中已经有一个到达了上限，那时都不加；`charge k` 加的是这样的 k 步会加的数。
   所以一个计数器上记的是：在带着它的 context 上走的与 `charge` 记的步数，再加上在那里被拒绝、而当时还没有计数器到达上限的步数（每次一）。到达了上限的计数器记的是 N+1。
3. **一次 `limited` 结束时，只要它自己的计数器、或者交给它的那个 context 带着的某个开着的计数器到达了上限，它就不会交回 `SOME`。**
   外面有开着的计数器到达了上限，它就抛 `EXCEEDED`；否则它自己的到达了上限，它就交回 `NONE`。
   所以在计数器到达了上限的那些层里，最外面的那一层交回 `NONE`，它里面的各层都抛 `EXCEEDED`（不管它们自己的计数器是不是也到达了），它外面的各层还没有到达上限、接着跑（被拒绝的那一步也记在它们上面，见第 6 节）。
   `NONE` 因此只会交给一个各层都还没有到达上限的调用方。
   中间的代码把 `EXCEEDED` 吞掉（`try`、`can`、`handle _`）或换成别的异常，都改变不了这一点：
   到达了上限的计数器只要还开着，就拒绝之后的每一步，而且每个 `limited` 结束时都只看计数器。
   没到达上限时，`limited` 交回的是 `f` 返回之前做完的工作的结果（第 5 节）。
4. **活得比运行久的 context 无害，也不受限**：一次受限的运行结束后还留着的 context（留在返回值、闭包、ref 里的），它带着的这一层计数器已结束，
   以后在它上面化简，这一层既不计数也不引起拒绝；所以那些化简也不受这一层的上限管（第 5 节）。外面还开着的各层照常计数。

接口**不**规定的：到达上限之后调用方做什么（原样交回输入、报错、打 warning）、N 取多少、要不要告诉用户。这些是调用方的事（第 9 节）。

## 3. 什么算一步

**现行的定义【作者 2026-11-27 定，经会话 concept B2 问他、concept A1 核过原话】**：09:06 UTC「你先把这个步数改一下，改成实际发生作用的步数。现在就改，改完启 code 评审」；
他在 concept B2 的对话里选了"改计数器本身"（全系统只有一种数法，selector Simpset 的 1000 步也变成发生作用的步）与"concept A1 改"，09:20 UTC「代码评审也交给 concept A1」；
代码在 `generic_mksimps` 里，提交到这里再合并进 concept（作者在 concept A1 的对话里选的）。
congruence rule 与 congproc 改了项的那一下也算一步：代码评审 2026-11-28 指出不算的话两条互换头的 [cong] 规则会一步不数地一直改下去，作者在 concept A1 的对话里选了"也数"。

- **一步 = simplifier 对项做成的一次改动**，有两种：
  - 一条规则的实例被用上了（规则是给定的，或是 simproc 交出来的；带条件的规则在条件证出之后）。数在 `rewritec` 里 `rews` 交回 `SOME` 的地方（`Pure/raw_simplifier.ML`）。
    simproc 交出的规则经同一个 `rews`，所以 simproc 的改写只算一次，交回 `NONE` 的 simproc 不算。
  - 一条 congruence rule 或一个 congproc 被套用、而且项变了。数在 `congc` 交回 `SOME` 的地方（项没变时它交回 `NONE`）。
    一次标准的 congruence 套用（两边头相同，项靠前提里的改写变）因此在那些改写之外再记一步。
- 证条件、证 congruence 前提时里面做成的改动在它们做成的地方算。三个跟踪函数恢复成 stock 的样子。β 化简不算：单靠 β 化简总会结束。
- 计数在改动做成之后：被拒绝的那一步，它的改动已经算出来，随整次运行一起丢掉。
- **拦得住的**：一切一直在改动项的化简。
- **拦不住的**（整张清单；下面"以前的定义"那一段里的论证已不适用）：
  - 带条件的规则一再试而条件证不出：只有 `simp_depth_limit` 截断，每层可有几条规则可试，次数可随深度成倍增长。
  - 失败的 simproc：每次走到一个位置调一次，有限，但每次的开销不受管（例如证 `concept _` 条件时起的一次什么也没找到的搜索）。
  - 一个不断造出子目标、而每个子目标都不做成改动的 looper：没有任何东西让它结束，与不设上限时一样（这正是以前把"一次运行的开始"也算一步的理由，第一轮评审第 7 条）。
    selector Simpset 没有 looper，所以它的各个单元不受影响。
  - 一个 ML 过程自己不返回（simproc、congproc 的函数体、solver、looper、mksimps 的函数与处理器、项序、证条件与证 congruence 前提的 prover），它自己起的化简里做成的改动除外。
  - 一步本身的开销；不在带着计数器的 context 上做的化简；simplifier 之外的改写引擎。
- 量过的（concept A1 2026-11-28，concept 的两套测试里 selector Simpset 的每个单元）：
  - 以前的数法：类型层的测试 4085 个单元，中位数 1，p99 29，最大 703；搜索的测试 380 个单元，中位数 2，p99 29，最大 47。
  - 现在的数法（规则的改写加 congruence 改了项，04:1x UTC 两棵树重建之后量的）：类型层 4014 个单元，中位数 0，p99 2，最大 9；搜索 380 个单元，中位数 0，p99 7，最大 9。
  - 两种数法下碰到上限的单元相同，都是不断改写的那些。作者 2026-11-28 04:04 UTC 把 concept 的上限从 1000 降到 150（「selector Simpset 的上限要留，但降低到 150」）。

**以前的定义（作者 2026-11-27 改掉；留作记录）【当时本会话的设计；作者 14:25 对"一次化简的开始算不算一步"：「你可以自主设计」】**

**一步 = simplifier 调一次它的三个跟踪函数之一**：`trace_invoke`、`trace_rrule`、`trace_simproc`（`Pure/raw_simplifier.ML:1110-1112`）。全文件调用它们的只有五处：
- 一次运行的开始（`rewrite_cterm`，`:1659`）；
- `rewritec` 里用一条不带条件的规则（`:1248`）；
- `rewritec` 里试一条带条件的规则，在去证条件之前（`:1258`），条件证不证得出都算；
- `rewritec` 里调一个模式匹配得上的 simproc（`:1296`），它交回 `NONE` 也算；simproc 给出的规则随后被应用时再算一步；
- `app_congprocs` 里调一个 congproc（`:1360`）。

所以步恰好是 simplifier 的 trace 报告的那些事件。

**不算的**：没匹配上的规则；被项序拒掉的 permutative 规则；因 `simp_depth_limit` 没去试的带条件规则；β 化简；套用一条普通的 congruence rule（`congc`，`:1381-1401`）。
除了最后一种在下面"拦不住的"里列的那一个情形，它们在相邻两步之间都只发生有限次。

**为什么这样就拦得住**（对源码的阅读，没有形式证明）：只要 simplifier 调用的每个 ML 过程自己都会返回，不结束的化简都要无限次地走上面的步；例外只有一种，列在下面"拦不住的"里。
- 一次运行之内：`botc`（`:1417` 起）只在 `rewritec` 交回结果之后才在同一个位置再来一遍；那个结果要么是一步，要么是顶上的一次 β 化简，
  而连续的 β 化简只有有限次（项是简单类型的）。`subc` 沿着一个有限的项往下走。
- 带条件的规则：每试一次本身就是一步，不管条件由谁来证（`trace_rrule` 包着对 prover 的调用，`:1258-1259`）。
- congruence rule 的前提：prover 是 simp 的 tactic 时（HOL 的 subgoaler `asm_simp_tac`，经 `solve_all_tac`，`Pure/simplifier.ML:320-324`），证一条前提要另起一次运行，运行的开始算一步。
- 运行与运行之间：simp 的 tactic 在每个 looper 造出的子目标上再来一遍（`simp_loop_tac`，`Pure/simplifier.ML:334-336`），
  HOL 证条件用的 subgoaler 也是这个 tactic（`Pure/simplifier.ML:529`、`HOL/Tools/simpdata.ML:218`）。每来一遍至少开始一次运行。
  这就是把"一次运行的开始"也算上的理由：不算它，一个不断造出子目标、而每个子目标的化简又一步不走的 looper 会让 tactic 无限递归，N 多大都拦不住（第一轮评审第 7 条）。
  代价是每起一次运行多记一步，证条件、证 congruence 前提时起的也在内；它只让步数变大一些，不改变别的。

**它拦不住的**（如实列出）：
- simplifier 调用的某一个 ML 过程自己不返回：simproc 与 congproc 的函数体、solver、looper、mksimps 的函数与处理器、项序，
  以及证条件与证 congruence 前提的 prover（在 simp 的 tactic 里就是 subgoaler）；prover 自己再起的运行除外，那些运行的开始都算步。
  这是那段代码的 bug，不归本设施管。
- 一条普通的 congruence rule 改了项、却没有引起任何运行：它没有前提，或者它的前提由一个不是 simp tactic 的 prover 来证。
  在"让前提互相化简"的模式下（`mut_impc`，`:1565-1605`；`simp` 默认的 `asm_full_simp_tac` 就是这种模式），这样的规则可以一直重复而一步不走。
  例：两条 `[cong]` 规则 `f x = g x` 与 `g x = f x`。stock 在这里同样死循环。
- 一步本身的开销。项可以越化越大，N 步不等于有界的时间或内存。
- 交出去以后才做的工作，以及不在带着这次运行的计数器的 context 上做的化简：见第 5 节的头一条与"哪些 context 带着这次运行的计数器"一条。
- simplifier 之外的改写引擎：`Pattern.rewrite_term`、`Conv` 组合出来的循环等。本设施只管 `rewrite_cterm` 引出的一切。

## 4. 补丁【实现】

1. **新文件 `Pure/simp_steps.ML`**，约 55 行，内容是第 2 节的结构。
   - 槽是 `Proof_Data`，值是一列步数计数器（最里层的在前），每个是"上限加一个 `int Unsynchronized.ref`"；初值是空的一列。
     初值为空的理由：受限的运行之外，context 不该带任何计数器，这样 `step` 什么都不做（保证 1）；而且 `init` 只拿到 theory，没有 N 可给。
     （初稿写的理由"否则同一个 theory 造出的 context 会共用一个 ref"是错的：`Proof_Context.init_global` 每次都重新跑各个 `init`，`Pure/context.ML:585-586`、`:612-614`。）
   - 每一列都是从某个 context 的**开着的**计数器造出来的（`limited` 往前加一个、`inherit` 照抄），已结束的在造的时候就丢掉。
     所以一列里的计数器不会比造它时开着的层数多；一个活得比它的各层运行都久的 context 至多带着这么多个已结束的计数器，`step` 读到它们就跳过。
   - 不放在 simpset 里：`put_simpset` 会把整个 simpset 换掉，计数器就丢了；`Proof_Data` 的槽不受它影响。
     simplifier 交给 simproc 的 context 是从自己的派生的，所以嵌套的 simproc 看得见同样的计数器。
   - "已结束"记在那个 ref 里（负数），这样所有派生出去的 context 同时看到。
   - 它在 ML antiquotation 可用之前加载，所以不用 antiquotation；里面没有任何 `concept` 或 mksimps 特有的东西。
2. **`Pure/raw_simplifier.ML` 改两处**【2026-11-27 起；以前是三个跟踪函数开头各加一次 `Simp_Steps.step ctxt`】：
   `rewritec` 里 `rews` 交回 `SOME` 时、`congc` 交回 `SOME`（项变了）时各调一次 `Simp_Steps.step ctxt`（第 3 节）。三个跟踪函数是 stock 的样子。
3. **`Pure/ROOT.ML` 加一行**：`ML_file "simp_steps.ML";`，放在 `ML_file "raw_simplifier.ML";`（`:204`）之前。
   它需要 `context.ML`（`:116`，提供 `Proof_Data`）、`General/exn.ML`（`ROOT0.ML:7`）、`Concurrent/unsynchronized.ML`（`ROOT.ML:30`）与 `General/integer.ML`（`ROOT.ML:48`），都在它之前加载。

结构的草稿（说明意图用，没有编译过）：

```ML
type counter = {bound: int, steps: int Unsynchronized.ref};
  (*steps < 0: 已结束；steps = bound + 1: 到达了上限*)

structure Data = Proof_Data
(
  type T = counter list;  (*最里层的在前*)
  fun init _ = [];
);

fun is_open ({steps, ...}: counter) = ! steps >= 0;
fun exceeded ({bound, steps}: counter) = ! steps > bound;
val open_counters = filter is_open o Data.get;

fun charge k ctxt =
  (case open_counters ctxt of
    [] => ()
  | counters =>
      let
        (*k 步里在被拒绝之前能走几步；负数：已经有计数器到达了上限*)
        val room = fold (fn {bound, steps} => Integer.min (bound - ! steps)) counters k;
        fun add n = List.app (fn {steps, ...} => steps := ! steps + n) counters;
      in
        if room < 0 then raise EXCEEDED
        else if room >= k then add k
        else (add (room + 1); raise EXCEEDED)
      end);

val step = charge 1;

fun count ctxt =
  (case open_counters ctxt of
    {steps, ...} :: _ => SOME (! steps)
  | [] => NONE);

fun inherit from = Data.put (open_counters from);

fun limited bound f ctxt =
  let
    val steps = Unsynchronized.ref ~1;  (*造出来时是已结束的*)
    val ctxt' = Data.put ({bound = bound, steps = steps} :: open_counters ctxt) ctxt;
    val (result, n) =
      Unsynchronized.setmp steps 0  (*只在 f 运行期间开着*)
        (fn () => let val result = Exn.result f ctxt' in (result, ! steps) end) ();
  in
    if exists exceeded (open_counters ctxt) then raise EXCEEDED
    else if n > bound then NONE
    else SOME (Exn.release result)
  end;
```

- `Unsynchronized.setmp`（`Pure/Concurrent/unsynchronized.ML:41-48`）在 `Thread_Attributes.uninterruptible_body` 里运行，每一种退出（中断也在内）都把 ref 恢复成原来的值，也就是"已结束"；
  所以计数器结束与否不取决于中断落在哪里。结果是在计数器已经结束之后，由（`f` 的结果，最后的计数）这一对定出来的。
  中断不进这一对：`Exn.result`（`Pure/General/exn.ML:126-127`）让它立刻通过，`setmp` 在它出去的路上把计数器结束掉。
- `charge` 里：`room` 是 k 与各个开着的计数器的余地里最小的那个。
  负数：已经有计数器到达了上限，这些步被拒绝，什么都不记。不小于 k：每个计数器各加 k。
  否则每个计数器各加 `room + 1`（能走的那几步，加上被拒绝的那一步），余地最小的那些于是记成"上限加一"，然后抛 `EXCEEDED`。
  每个计数器加的数总是一样的；计数从 0 起，只增不减，所以没有哪个整数参数能让一个开着的计数器看起来像已结束的。

**没有设上限时的开销**：每一步多读一次 `Proof_Data` 的槽（`Context.Proof_Data.get`，`Pure/context.ML:627-630`，一次 `Datatab.lookup`），读到空的一列就返回。
同一个包装函数里 stock 本来就要为跟踪钩子读一次 theory 数据。与一步里的匹配、实例化、内核推理相比应当很小，但**没有量过**，探针在第 8 节。
若量出来不小，退路是在 `rewrite_cterm` 里每次运行只读一次槽、往下传；那要改内部函数的参数，补丁大得多。
有上限时，每一步的开销与 context 带着的计数器的个数成正比，这个数至多是造那一列时嵌套的层数，通常是一到三。

**不打补丁的办法为什么不用**：见第 1 节"stock 为什么不够"的三条；另外，在 HOL 里用 `Hooks` 一类的钩子把计数挪到上层，要给每个 theory 的每一步多加一次分发，逻辑也分在两处。

**升级 Isabelle 时**：重新套补丁，并核对"每一次改写仍然经过 `rews`、每一次 congruence 套用仍然经过 `congc`"。第 8 节按步的种类各有一条测试，漏掉的地方会被它们查出来。

## 5. 调用方要守的规矩【本会话的设计】

这些是接口契约的一部分，会写进 README。Isabelle/ML 的用户是可信的，所以不加运行时检查。

- **交出去以后才做的工作不受限：`f` 要在返回之前把化简做完。** 受限的只是 `f` 返回之前做完的工作。
  tactic 的结果序列、tactic 或 conversion 的闭包、`Lazy` 值，若是被返回或存起来、之后才在这次运行的 context 上化简，那些化简发生在计数器结束之后：不计数，也不受限。
  - 例：`Simp_Steps.limited N (fn c => simp_tac c 1 st) ctxt` 一步都没走就交回 `SOME` 一个惰性的序列（`Pure/tactical.ML:79`、`Pure/General/seq.ML:172-176`），真正的化简发生在调用方取结果的时候。
  - tactic 要在 `f` 里面用 `SINGLE` 取出第一个结果、只交回它（`Pure/tactical.ML:317`；`Goal.prove` 就是这样做的，`Pure/goal.ML:195`）。
    用 `Seq.pull` 而把剩下的序列交出去，剩下的那部分仍是交出去以后才做的工作。
  - `Lazy` 值还多一层：它若在被拒绝之后求值，会把 `EXCEEDED` 永久记住（`Pure/Concurrent/lazy.ML:108`），以后每次 force 都重新抛出，而那时已经没有人接。
- **哪些 context 带着这次运行的计数器。** `f` 要在这三种 context 上做化简：它收到的那个 context；从它派生出来的 context；
  用 `Simp_Steps.inherit ctxt' (Proof_Context.init_global thy)` 造出来的新 context，其中 `ctxt'` 是 `f` 收到的那个。
  - 从传给 `limited` 的那个 context（而不是 `f` 收到的那个）`inherit`，会漏掉这次运行自己的计数器。
  - 别的 context 都不带这次运行的计数器：没有 `inherit` 的新 context；调用之前就拿到手的 context，例如事先造好的 tactic `val tac = asm_full_simp_tac ctxt 1`。
    在它们上面走的步不受这次运行的上限管，这次运行的 `count` 也看不见。
- **要知道自己的工作是不是在上限之内做完的，就把它放进 `limited`，嵌套与否都一样。** 只是不想比调用方更紧的，就传与调用方相同的 N：
  那样它自己的计数器不会先于外层到达上限，效果与没有自己的上限相同（第 6 节）。读 `count` 看不出自己的工作有没有被拒绝过。
- **缓存。** 受限的运行里若用到跨调用共享的缓存，而填缓存要走步，那么命中与不命中步数不同，接近上限时结果就随缓存的冷热变。要结果确定：
  - 每次填充放在一个 `limited` 里做，只存它正常交回的东西（被拒绝的填充交不回东西，所以半截的结果存不进去）；
  - 在 `f` 的末尾用 `count` 读出这次填充记的数（这一层的计数器从 0 起，所以读到的就是它），随结果一起交回、一起存；
  - 命中时用 `charge` 记上存下的那个数，并且把这次 `charge` 放在一个与填充的 `limited` 一样的 `limited` 里做：
    同一个上限，同一个 context（就是不命中时交给填充的 `limited` 的那个）；
  - 算 key 与查缓存都在这两个 `limited` 的外面做，这样它们走的步在命中与不命中两条路上记得一样。

  写出来是这个样子（没有编译过；`lookup`、`store`、`fill`、`key`、`bound` 是调用方自己的）：

  ```ML
  (case lookup key of
    SOME (x, k) => Simp_Steps.limited bound (fn c => (Simp_Steps.charge k c; x)) ctxt
  | NONE =>
      (case Simp_Steps.limited bound (fn c => (fill c, the (Simp_Steps.count c))) ctxt of
        SOME (x, k) => (store key (x, k); SOME x)
      | NONE => NONE))
  ```

  这样命中在每个计数器上留下的恰好是不命中会留下的，结束的方式也相同（交回 `SOME`、交回 `NONE`、或者抛 `EXCEEDED`），
  不管这次查找用的上限是多少、在哪个 context 上做；填充里面有一个到达了自己上限的嵌套 `limited` 时也一样（第 6 节"被拒绝的步只记一次"）。
  - 为什么命中也要放进 `limited`，例一（上限不同）：同一个 key 先在 `limited 1000` 里填好，存下的数是 60；后来另一处用上限 50 查它。
    不命中：填充在 `limited 50` 里重做，第 51 步被拒绝，交回 `NONE`，外面的计数器多了 51。
    命中若直接 `charge 60`：外面的计数器多了 60，调用方还拿到了结果。放进 `limited 50` 之后，`charge 60` 记到第 51 步被拒绝，交回 `NONE`，外面多了 51，与不命中相同。
  - 例二（context 不同）：填充的 `limited` 若做在一个没有 `inherit` 的新 context 上，不命中在调用处的计数器上什么都不记。
    命中若直接在调用处的 context 上 `charge`，就记上了；放进那个新 context 上的 `limited` 之后，两边都不记。
  - 算 key 不放进去的理由：放进去的话，不命中把算 key 的步也存进了那个数，命中时这些步先真走一遍、又被 `charge` 再记一遍。

  （`concept` 的类型层是它的第一个用户：见第 9 节。）
- **不要在受限的运行里 fork 要化简的任务。** 计数器是不加锁的 ref，经 context 被 fork 出去的任务共用：加一不是原子的，到达上限落在哪一步会随调度变，`EXCEEDED` 还会在别的线程上抛出。
  Isabelle 整个 fork 出去的证明（`lemma`、`have` 的并行证明）是从命令层面开始的，那里没有开着的计数器，不受影响。
- **不要在"事先陈述好目标"的 tactic 里用它。** 在 `Goal.prove` 里到达上限，目标就证不出来，成了一个证明错误。先算、算完再陈述。
- **接住 `EXCEEDED` 之后不要无限重试。** 保证 3 靠的是"吞掉异常的代码迟早会结束"。

## 6. 行为的几处细节【本会话的设计】

- **重置就是开始一次新的 `limited`。** 没有"把计数清零"这个操作。每次 `limited` 的计数器从 0 起；它里面的步同时记在外面各层上。
  这就是作者 12:33 说的「重置前所有的 … step 无论是当下的还是 nested simproc 中的都累加」。
- **嵌套的 `limited` 各有各的上限。** 例：在 `limited 10000` 里面调 `limited 100`，里层走满 100 步、要走第 101 步时被拒绝，交回 `NONE` 的是里层，外层接着跑；
  那 100 步和被拒绝的那一步都记在外层的账上（共 101）。外层先到上限、或者两层在同一步到上限时，里层抛 `EXCEEDED`，由外层交回 `NONE`。
  - 来由：初稿定的是"嵌套的 N 不起作用"。评审指出它有一种不同的做法；作者 14:25：「但你也可以实现成一个 stack 对吗？我感觉不难？这里我交给你设计了，我都能接受」。
    本会话取栈：这样 `limited N f` 在哪里调用都是"`f` 至多 N 步"，一段代码为自己设的小上限不会因为被别人套在大上限里就失效。
  - 先看外层、再看自己的理由：`NONE` 的意思是"你的额度用完了，你可以接着干别的"。外层也已经到达上限时，拿到 `NONE` 的代码其实什么都干不了，它之后的每一步都会被拒绝；
    让它直接收到 `EXCEEDED` 一路退出去，中间就不会有代码白白去走它处理 `NONE` 的那条路。
    外层只是没有余地、还没有到达上限时，里层照样交回 `NONE`，这是对的：拿到 `NONE` 的代码若不再走步就结束（例如原样交回输入），那一层仍然交回 `SOME`。
  - 一条推论：嵌套的 `limited N`，只要 N 不小于外面某一层在它开始时剩下的余地，就永远不会交回 `NONE`。
    理由：里层的计数器每加一次，那一层也加一次，所以里层要到达上限的那一步，那一层同样没有余地。处处用同一个 N 时（`concept` 就是这样），嵌套的 `limited` 只会让 `EXCEEDED` 穿过去。
- **被拒绝的步只记一次。** 被拒绝的一步在 context 带着的每个开着的计数器上各记一次，就像真走了一样；只有当其中已经有一个到达了上限时，才都不记。
  所以一个 context 带着的开着的计数器在每一步上变的数都一样，一次填充结束时读到的计数，就包含了这次填充对它外面每个计数器所做的全部改动。
  - 吞掉 `EXCEEDED` 再重试的代码不会让账越记越多：拒绝它的那个计数器已经到达了上限，只要它还开着，之后被拒绝的步都不记。
  - 为什么不是"被拒绝的步不记账"（第三稿的写法）：那样命中缓存与不命中会给出不同的结果。
    例：一次填充的最后是一个 `limited 5`，它走了 5 步、第 6 步被它自己的计数器拒绝，填充接受了这个 `NONE`、正常返回，存下的步数是 5。
    后来一个已经走了 95 步的 `limited 100` 查到这一项。命中：`charge 5`，它正好记满 100，交回 `SOME`。
    不命中：重做那次填充，第 6 步被拒绝时它也没有余地了，被标成到达上限，交回 `NONE`。
    照"只记一次"，存下的是 6；命中与不命中都使它到达上限。
  - 为什么也不是"每次被拒绝都记"：那样填充里的代码每重试一次，不命中就比命中多记一步。
  - 代价：里层每到达一次上限，外面各层的账上就多一步并没有真走的步。
    这一步可能正好用掉外面某一层最后的余地：里层交回 `NONE` 时，那一层已经没有余地（但还没有到达上限），调用方在它上面再走一步就被拒绝。
    例：`limited 100` 的函数先走 89 步，再调一个不停化简的 `limited 10`。里层走 10 步，第 11 步被拒绝，里层交回 `NONE`；这时外层记的是 100。
    外层的函数此后不再走步，外层就交回 `SOME`；再走一步，外层交回 `NONE`。
- **只看计数器来定结果**的一处后果：某一层到达上限之后，`f` 里若因为真正的 bug 抛了别的异常，这个异常不会被看到，那一层照样交回 `NONE` 或抛 `EXCEEDED`（照保证 3）。
- **确定性**：一次运行到不到达上限，只取决于它做了哪些步，不取决于机器、负载、垃圾回收；调用方照第 5 节"缓存"那条做了的话，也不取决于缓存的冷热，
  里面的代码吞掉 `EXCEEDED` 再重试时、填充里有到达了自己上限的嵌套 `limited` 时也一样。
- **中断照常**：`limited` 不接中断，用户取消与外层工具的定时器都原样通过，计数器照样结束；`EXCEEDED` 不是中断，不会被当成取消。
- **与 `simp_depth_limit`、simplifier trace 的关系**：互不相干。因 `simp_depth_limit` 没去试的规则不算步。

## 7. 作为 `generic_mksimps` 的一部分【已定，作者 13:33】

- 代码进本 feature 的私有树 `worktrees/Isabelle2026-generic_mksimps`（分支 `Isabelle2026/generic_mksimps`，现在的头 `1aa94bd`，还没有 release 过）。作者 13:33「允许」本会话动它。
- 本 feature 已经改 `Pure/raw_simplifier.ML`；这里改的两处在 `rewritec` 的 `rews` 与 `congc`（2026-11-27 以前是跟踪函数处），与 mksimps 处理器的改动不相邻。
- 包里随之要改的：
  - `tools/patched_files.txt` 加 `src/Pure/simp_steps.ML` 与 `src/Pure/ROOT.ML`（照 SKILL 3.4 第 3 步重新生成）；
  - `tools/signature_additions.txt` 按它现有的格式给 `SIMP_STEPS` 的每一项加一行；
  - `tools/release_build.sh`、`tools/required_sessions.txt` 与许可证文件不用动（测试进现有的测试 session，见第 8 节）；
  - `README.md` 加一节，讲这个接口、第 5 节的规矩和两个例子（英文）。
- `concept` 那边：代码进来之后，它照平常合并 base 的办法（SKILL 3.3）合并本 feature 的新头即可；它的树现在合并到的是 `94c1377`。
- 开工前照 SKILL 3.2 拉取并跑 `init.sh`。写代码：作者 16:38「很好，批准开工」。构建、代码的提交、推送、release，每一步都等作者下令。

## 8. 测试与探针

**测试**：新 theory `Simp_Steps_Test`，放 `contrib/generic_mksimps/tests/`，加进现有的 session `Generic_Mksimps_Test`（parent 是 `HOL`）；写实现时一起写。
1. 每一种步各一条，都恰好在第 N+1 步被拒绝、`limited` 交回 `NONE`：
   - 规则的循环（前提 `a = b`、`b = a`），以 `SINGLE (asm_full_simp_tac c 1) st` 的形式在 `f` 里跑；
   - 一个每次都给出等式的 simproc；
   - 带条件的规则，条件靠化简来证；
   - 一个 congproc；
   - 一个不断造出子目标、子目标上一步不走的 looper（只靠"运行的开始"这一种步被拦住）。
     【2026-11-27 起去掉：现行的定义下它拦不住（第 3 节），测试里留着会一直跑下去。另加：带条件的规则条件证不出时不算步；
     每一种改动各恰好一步（simproc 的结果只算一次；条件由前提闭合、不做改写的带条件规则；改了项的 congproc 与 congruence rule）；不改项的 congproc 恰好 0 步；
     靠前提里的一次改写改了项的标准 congruence rule 恰好 2 步。】
2. 嵌套的 simproc 里起的化简，步子记在外层的计数器上：只在嵌套的化简里循环的例子，外层到达上限。
3. 嵌套的 `limited`：
   - 里层的上限小：里层交回 `NONE`，外层接着跑并正常结束，外层的计数里含里层走的步和它被拒绝的那一步；
   - 外层的上限先到：里层抛 `EXCEEDED`，外层交回 `NONE`；
   - 两层上限相同、里层在外层走任何一步之前就调用：里层抛 `EXCEEDED`，外层交回 `NONE`；
   - 外层的 `f` 里的代码先吞掉了外层的 `EXCEEDED`，之后才开始一个里层的 `limited`：里层抛 `EXCEEDED`，外层交回 `NONE`；
   - 三层，只有中间一层与最里层到达上限：中间一层交回 `NONE`，最里层抛 `EXCEEDED`，最外层接着跑；
   - 里层被拒绝的那一步恰好把外层记满：`limited 100` 的函数先走 89 步，再调一个会到达上限的 `limited 10`。里层交回 `NONE`，外层的计数是 100；
     外层的函数此后不再走步，外层交回 `SOME`；再走一步，外层交回 `NONE`；
   - 从里层逃出来的 context：在 `limited 1000` 里跑一个会到达上限的 `limited 10`，里层的函数先把它的 context 存进一个 ref。
     里层交回 `NONE` 之后、外层还开着时，在存下的 context 上：`count` 读到的是外层的计数；再化简约 20 步，不抛异常，这些步加在外层的计数上。
4. 中间的代码用 `try` 吞掉 `EXCEEDED`：`limited` 仍交回 `NONE`，不是化简到一半的结果。同样的吞法放在嵌套的 `limited` 里、被拒绝的是外层：里层抛 `EXCEEDED`，外层交回 `NONE`。
5. `f` 把 `EXCEEDED` 换成别的异常：仍是 `NONE`。没到达上限时 `f` 抛的异常原样传出。
6. 运行结束后留下来的 context：`count` 是 `NONE`；在它上面化简不计数、不抛异常；在它上面再 `limited` 从 0 数起。
7. `count` 与 `charge`：
   - 没有被拒绝时，量出的数等于实际走的步数；`charge` 记在每一层上；
     【2026-11-27 起：测试的跟踪钩子在规则做成改写时多记一个"made"；量出的数不少于"made"的个数（congruence 套用另算）、少于报告的事件总数；第 9 节那批目标逐条这样查】
   - 在 `limited 1000` 里，一个已经走了 90 步的 `limited 100` 调 `charge 30`：抛 `EXCEEDED`，里层交回 `NONE`，外层的计数恰好多了 11；
   - 在 `limited 1000` 里，一个 `limited 10` 的 `f` 做 50 次化简、每次都包在 `try` 里：里层交回 `NONE`，外层的计数恰好多了 11（走了的 10 步和头一次被拒绝的那一步）；
   - 命中与不命中一样：一次填充，它的函数最后是一个会到达自己上限的 `limited 5`、填充接受它的 `NONE`；在函数末尾读出它的计数 k（是 6）。
     然后在一个余地分别是 k − 1、k、k + 1 的运行里，一边把这次填充放在它的 `limited` 里重做，一边在同样的 `limited`（同一个上限、同一个 context）里调 `charge k`：
     两边在那个运行的计数器上留下的数相同，结束的方式（交回 `SOME`、交回 `NONE`、抛 `EXCEEDED`）也相同；
   - 同一个 key 在两个上限下：一次记 60 步的填充先在 `limited 1000` 里做完，存下 60。然后在一个外层的 `limited 1000` 里，照第 5 节"缓存"的写法用上限 50 查它，
     一次缓存里没有这一项（不命中）、一次有（命中）：两次都交回 `NONE`，外层的计数都恰好多了 51；
   - 填充的 `limited` 做在一个没有 `inherit` 的新 context 上：命中与不命中都不改变调用处的计数；
   - `charge 0`：里层的计数器到达上限之后，经一个只带着外层计数器的 context 把外层恰好记满；这时在里层的 context 上 `charge 0` 抛 `EXCEEDED`，外层的计数仍是它的上限。
8. `inherit`：在一个外层的 `limited` 里面，`f` 从它收到的 context `inherit` 造一个新 context；那上面的步记在 `f` 自己的计数器上（在 `f` 末尾用 `count` 读）也记在外层的上；
   没有 `inherit` 的新 context 上的步，两个都不记。
9. 没有计数器时：一批目标的化简结果与没有本设施的 Isabelle2026 逐条相同。
   期望值先在共用的树上用探针记下（作者 16:39 对两个探针：「交给你自决了」），再作为字面量写进测试，照 `tests/Generic_Mksimps_Test.thy:9-38` 的做法。
10. 同一批目标，套在一个到不了上限的最外层 `limited` 里，交回的是 `SOME` 同一条定理。
11. 两个并行的证明各自 `limited` 同一个项，互不影响，结果相同。
12. 中断：
    - 在约一秒的 `Timeout.apply` 里跑一个到不了上限（例如 N = 10^9）的循环，`f` 先把它的 context 存进一个 ref：出来的是 `Timeout.TIMEOUT`，不是 `NONE`；
      之后在存下的 context 上 `count` 是 `NONE`，化简不计数也不抛异常。
    - `f` 存下 context 后自己抛 `Exn.Interrupt_Break`：中断从 `limited` 出来，同样的两项检查成立。

**探针**：
- **补丁的开销**（是构建，要作者下令）：同一个大量用 `simp` 的 session（例如 `HOL`），机器空闲、`threads=1`，在不带这处补丁（2026-11-27 起是两处计数）的树与带的树上各构建一次，比 CPU 时间。
- 在那之前（REPL 里，不需要构建；作者 16:39「交给你自决了」）：读一百万次 `Proof_Data` 的槽要多久，对比普通 `simp` 平均一步要多久。
- **N 取多少不是本设施的事**（第 9 节）。给调用方的提示：普通调用用多少步，不打补丁就能量：在草稿 theory 里用 `Raw_Simplifier.set_trace_ops` 装三个只计数的钩子（2026-11-27 起它们看到的是尝试，不再恰好是第 3 节的步：步不多于钩子看到的规则事件里做成改写的那些、再加改了项的 congruence 套用）。

## 9. 与 `concept` 的分工

- **本设施给的**：第 2 节的六样东西，第 5、6 节的契约。
- **`concept` 那边的**（不在本文件里定）：N 的值（类型层里的一个常数，作者定）；selector Simpset 的入口怎样用 `limited`；哪些工作整体算一次受限的运行；
  缓存的记账；到达上限后那条 fact 怎样处理；怎样告诉用户、文案。
  这些在 `ai-artifacts/concept_B_open_questions_2026-11-22/Q01_resolution_v7.md`（下称 v7；会话"concept B"名下的小组写的，14:57 写完，它那边的第七轮评审 15:18 判可以接受、附三处更正；类型层归会话"concept A1"）。
- **本稿与 v7 有两处相抵**：要不要 client，一次运行的开始算不算一步。
  concept B 15:18 转告 v7 通过时说：v7 的评审者没有看到本会话 14:31、15:0x 的两封信，这几处以本设施的定稿为准，它把 B 区自己的部分写进计划之前会照本方案对一遍。
  **concept B 15:54 明确答复（本稿交评审之后加的一条）：`concept` 那边照本接口办，不设 client，一次运行的开始算步。**
  它说这句答复不需要再请作者：v7 的 R12 里这几项，作者 13:07 留给了它定。所以这两处不必再请作者定。
  它采用的前提是两条性质，后面的稿子若改了要告诉它：处处用同一个 N 时，嵌套的 `limited` 不自己交回 `NONE`（第 6 节的推论）；命中与不命中在每个计数器上留下的相同（第 5 节"缓存"）。
  它把 Q01 写进计划时，v7 里讲 client 的文字不照录，换成指向本方案；类型层的代码归 concept A1，由它转告以本接口为准。
  第四轮评审之后，这两条性质都没有变（裁判重新走过，报告 4.8 与第 8 节）；第 5 节"缓存"的写法变了（F26），本会话 16:31 已写信告诉 concept B，也把第二稿以来含义变了的四处告诉了 concept A1。
  - **client。** v7 的 R1 (i)（它的 225 至 241 行）要的是：开始一次受限的运行时带上一个 client；context 里已有同一个 client 的开着的计数器时就不另装；
    记若干步、读计数（那个 client 没有开着的计数器时读到"无"）、把计数器递给新造的 context，都只针对一个指定的 client；它的缓存规矩第 1、3 条建在这上面。本稿里没有 client。
    - 为什么本稿不需要它。它那边的第六轮评审（`Q01_review_round6.md` 的 1.1）指出，别的调用方的计数、或 `cached` 存下的东西，有两条路会随缓存的冷热而变。
      一条是记账：本稿里 `charge k` 就是照 `step` 的规矩记 k 步，被拒绝的步只记一次，所以命中在每个计数器上留下的与不命中相同（照第 5 节"缓存"）；
      那轮评审不接受"靠人记住的两条规矩"，而这里它们是 `step` 与 `charge` 的做法本身，并有测试 7 查着。
      另一条是别的调用方在一次合成里面开始它自己的受限运行：本稿里每次 `limited` 都有自己的上限，填充期间外面的计数器到达上限时填充的 `limited` 抛 `EXCEEDED`、什么都不存；
      所以存下的总是同一条等式和同一个步数，不管是谁调的。
    - v7 的 R12 第 4 项（749 行）把"每次开始都另有自己的上限"列为留给 concept B 的一种选择。v7 在 204 行接受的代价（别的调用方的计数器不计合成里的步）在本稿里没有了：
      那个计数器照样计，冷热缓存下计的数相同。
    - 作者 13:07 留给 concept 的那个选择（新造的 context 里的合成用它自己的计数器还是调用处的）仍归 concept：从单元的函数收到的 context `inherit`，或者另起一个自己的 `limited N`。
      两种做法里，命中都照第 5 节"缓存"放在同样的 `limited` 里、在填充的 `limited` 所用的那个 context 上做。
      后一种做法里那个 context 是没有 `inherit` 的新 context，不带调用方的任何计数器，所以命中在调用方看得见的计数器上什么都不记，与不命中一样。
      本稿拿掉的只是 v7 的第三种做法"只递 concept 自己的计数器"。
  - **步。** v7（156 行；R12 第 2 项，740 行）不把一次运行的开始算作步，并把"哪些事件算步"留给 concept B 定；本稿照作者 14:25 对本会话说的话把它算上，理由在第 3 节。
    v7 157 行说"不算的事件在相邻两步之间只发生有限次"，对 looper 那种情形不成立（第 3 节）；selector Simpset 没有 looper，所以 `concept` 不受影响。
- 另外三处，照本稿的接口 `concept` 那边要注意的（v5、v6、v7 的写法相同）：
  - **嵌套。** v7 让嵌套的入口不装计数器、直接跑。处处用同一个 N 时，照第 6 节的推论，嵌套的 `limited N` 永远不交回 `NONE`、只让 `EXCEEDED` 穿过去，行为与它相同，
    只是每一步在每一层上各多加一次。所以 `concept` 可以在每个单元里都调 `limited N`，不必自己区分最外层与嵌套。
  - **新造的 context 要从哪个 context `inherit`。** v7 的缓存规矩第 1 条（330 行）写的是把 `cached` 所在 context 的计数器递进去；应当是受限的单元的函数收到的那个 context，否则漏掉这个单元自己的计数器。
  - **填充的步数。** 每次填充，嵌套与否，都在 `f` 的末尾读 `count`；它自己的计数器从 0 起，不需要前后两次读数相减。
- 第四轮评审之后加的一处：**命中时的 `charge`。** 第 5 节"缓存"现在要命中也放进与填充相同的 `limited`（那一轮的 F26）。对 `concept` 行为不变：
  它的填充都在同一个常数 N 之下、在调用处的 context 上做，存下的数不超过 N；这时直接 `charge k` 与放在 `limited N` 里 `charge k`，加的数相同，抛不抛 `EXCEEDED` 也相同。
  所以它可以保留 v7 的直接 `charge`（缓存规矩第 3 条），也可以改成第 5 节的写法，由 concept B 定。

## 10. 作者交给本会话定的设计，列在这里供他过目

名字（文件 `simp_steps.ML`、结构 `Simp_Steps`、六样东西的名字）、不给用户做 Config 选项、做进 `generic_mksimps`，作者已明说（第 1、2 节）。下面是他没有逐条看过的：

1. **嵌套的 `limited` 各有各的上限**（第 6 节）。作者 14:25：「这里我交给你设计了，我都能接受」。
   随之：每一步记在 context 带着的每个开着的计数器上，`charge k` 也一样；`count` 读的是最里层那个开着的计数器，所以在 `f` 的末尾读到的是这次运行自己的计数。
   `concept` 那边的决议 v7 要的是相反的设计（按 client 分计数器）；理由见第 9 节。concept B 15:54 已答复照本接口办，所以这一处不必请作者定。
2. **什么算一步**（第 3 节）【2026-11-27 作者改成"做成的改动"，下面是以前的定义】：simplifier 调一次三个跟踪函数之一，恰好是 trace 报告的事件。
   带条件的规则试一次算一步，条件证不证得出都算；模式匹配得上的 simproc、congproc 调一次算一步，交回 `NONE` 也算，simproc 给出的规则被应用时再算一步；
   普通的 congruence rule 与 β 化简不算。其中"一次运行的开始也算一步"是作者 14:25 说「你可以自主设计」的那一处；v7 不算它，并把这件事留给 concept B（第 9 节）。
3. **只看计数器来定结果**，连同它的后果：到达上限之后别的异常不会被看到（第 2、6 节）。
4. **一次 `limited` 结束时，自己的或外面开着的计数器到达了上限，它就不交回 `SOME`；并且先看外层、再看自己**（第 2 节保证 3、第 6 节）：
   到达了上限的各层里最外面的交回 `NONE`，它里面的都抛 `EXCEEDED`。先看外层的理由：`NONE` 只交给各层都还没有到达上限的调用方。
5. **被拒绝的步只记一次**（第 6 节）：在每个开着的计数器上各记一次，除非其中已经有一个到达了上限。
   另两种做法：都不记（第三稿的写法；命中缓存与不命中在第 6 节那个例子里结果不同）；每次被拒绝都记（填充里的代码重试时，不命中比命中记得多）。
6. **只有 `f` 返回之前做完的工作受限**（第 5 节头一条）。
7. **已结束的状态**，与活得比运行久的 context（第 2 节保证 4）。
8. **中断原样放行并使计数器结束；`EXCEEDED` 不是中断**（第 6 节）。
9. **第 5 节的各条规矩**，它们经 README 成为公开的契约。
10. **`inherit` 作为单独的一个操作**；**`charge k`**：它在各个计数器上留下的恰好是一次记了 k 步的填充会留下的，已经有计数器到达上限时什么都不记、直接抛 `EXCEEDED`（k = 0 也一样）；用于命中缓存时记账。
    命中时这次 `charge` 要放在与填充相同的 `limited` 里做（同一个上限、同一个 context；第 5 节"缓存"），这是第四轮评审之后加的规矩。
    后者与作者 12:33 的话有一处出入：这些步这次并没有真走；它换来的是结果不随缓存冷热变。
    作者 13:07 已把这一处交给 fork 之前的会话自己定（当时列给他的"限步数的三处"之一）。
11. **新的 Pure 文件**：计数的代码放新文件，`raw_simplifier.ML` 只改几行（2026-11-27 以前是三个跟踪函数，之后是 `rews` 与 `congc` 两处）。

## 11. 实现记录（2026-11-22 16:41 至 16:57 UTC）

作者 16:38「很好，批准开工」之后写的。下面"写了什么"到"补丁的开销"各段是 16:58 构建之前写的；构建与提交的结果在本节最后一段。推送还等作者下令。

**写了什么**
- 私有树（`worktrees/Isabelle2026-generic_mksimps`，未提交）：
  - 新文件 `src/Pure/simp_steps.ML`，102 行（连文件头的说明；第 4 节估的"约 55 行"没有算文件头与注释）；
  - `src/Pure/raw_simplifier.ML`：三个跟踪函数各加一次 `Simp_Steps.step ctxt`；
  - `src/Pure/ROOT.ML`：在 `raw_simplifier.ML` 之前加 `ML_file "simp_steps.ML";`。
- feature 仓库（未提交）：
  - 新文件 `tests/Simp_Steps_Test.thy`（674 行），`tests/ROOT` 的 session `Generic_Mksimps_Test` 加上它；
  - `tools/patched_files.txt` 加两行；`tools/signature_additions.txt` 加六行；`README.md` 加一节（英文）。
  - `tools/patched_files.txt` 是手写的；照 SKILL 3.4 第 3 步，release 之前要在提交之后用 `git diff-tree` 重新生成并用 `check-signatures` 核对，这两件事现在做不了（它们只认提交）。

**与第 4 节草稿的出入**（都不改变行为）
- `exceeded` 这个函数改名为 `has_reached_bound`，与"到达了上限"这个词一致。
- `raw_simplifier.ML` 的三行各折成两行，前面加一行注释 `(*each call is one step of Simp_Steps*)`，为的是不超过 80 列。

**与第 8 节测试清单的出入**
- 多了第 0 组：没有计数器时 `count` 是 `NONE`、`step` 与 `charge` 什么都不做；上限 0；计数从 0 起。
- 多了一种独立的对照：测试 theory 自己装的 trace 钩子把 simplifier 报的每个事件记下来。
  于是"计数 = 事件的个数"可以直接核对（用 `Main` 的 simpset，对测试 9 的 22 个项与另一个项），每一种步的测试也核对"那一种事件确实在里面"。
- 第 1 组"规则的循环"用的是**一个**前提 `a = b ∧ b = a`，不是分开的两个前提。分开的两个前提会互相化简掉，不循环（16:57 在 stock 上试过：两个前提的那个目标正常结束，一个前提的那个 2 秒内不结束）。
- 第 1 组每个不结束的例子都用同一个检查：上限 20，`limited` 交回 `NONE`，外面一层读到的恰好是 21，trace 钩子记下的恰好是 20 个事件。
- 第 12 组的超时用 0.5 秒，不是约一秒。

**构建之前已经验证的**（探针，在共用的树上，它现在就是没有任何 feature 的 Isabelle2026，提交 `7d475f7`；经 isabelle-mcp，session `HOL`）
- `simp_steps.ML` 这个文件原样用 `ML_file` 载入，编译通过。
- 补丁的三行用 trace 钩子模拟：每个钩子先调 `Simp_Steps.step`，位置与打了补丁的三个函数相同。在这个模拟之下，测试 theory 全文通过（最后一次是 16:57，用的是最终的文本）。
- 生成探针的脚本与探针在 `ai-artifacts/probes/`（`make_simp_steps_probe.py`、`Simp_Steps_Probe.thy`），不提交。
- **还没有验证的，只有构建能验证**：真正的那三行补丁；`ROOT.ML` 的那一行；`simp_steps.ML` 在 Pure 引导阶段（ML antiquotation 可用之前）的编译；
  测试 theory 在私有树里、接在 `Generic_Mksimps_Test_Base` 之后的那一份。

**变异检查**：把实现故意改错 8 种，各跑一遍测试，8 种都至少有一组测试失败（改错的文件都编译通过，失败的都是测试）。
- 被拒绝的步不记在还有余地的计数器上（第三稿的做法）；
- `limited` 结束时先看自己的计数器、再看外层；
- `charge 0` 在已有计数器到达上限时不抛；
- 运行结束时不把计数器结束掉；
- `count` 读最外层的计数器；
- 多放一步才拒绝；
- 恰好走满上限的运行交回 `NONE`；
- 补丁里 `trace_simproc` 那一行漏掉（在模拟里去掉那个钩子的 `step`）。
- 没有试的两种：漏掉 `trace_invoke` 或 `trace_rrule` 那一行。那样测试里不结束的例子真的不会结束，探针会挂住；在真正的构建里它表现为测试 session 超时（600 秒）。

**测试 9 的期望值**：16:51 在共用的树上用探针 `ai-artifacts/probes/Simp_Steps_Baseline_Probe.thy` 记下，22 个项，已作为字面量写进测试。

**补丁的开销**（探针 `ai-artifacts/probes/Simp_Steps_Cost_Probe.thy`，16:54，只量了一次，机器负载约 1）
- 没有计数器时一次 `step`：约 22 纳秒；有一个开着的计数器：约 30 纳秒；有三个：约 38 纳秒。
- 一批 26 个项用 `Main` 的 simpset 各化简一遍是 3366 步；不打补丁时平均每步约 2460 纳秒。
- 所以没有设上限时，补丁给化简本身增加约 0.9% 的时间；整个构建里化简只占一部分，比例更小。第 4 节的退路（每次运行只读一次槽）不需要。
- 第 8 节那个要构建的开销探针（两棵树各构建一次 `HOL` 比 CPU 时间）没有做，要作者下令；照上面的数字，本会话认为不必做。

**构建与提交**（作者 17:03：「批准构建」「批准新文件提交」「请进行代码评审」）
- 构建：17:04 起、17:10 结束，退出码 0。命令（在 MLML 根目录，低优先级）：
  `contrib/generic_mksimps/worktrees/Isabelle2026-generic_mksimps/bin/isabelle build -v -b -d contrib/generic_mksimps/tests Generic_Mksimps_Test`。
  Pure 17 秒，HOL 6 分 09 秒，`Generic_Mksimps_Test` 5 秒（其中 `Simp_Steps_Test` 累计 1.3 秒）。
  所以上面"只有构建能验证"的四样都过了：真正的三行补丁、`ROOT.ML` 的那一行、新文件在 Pure 引导阶段的编译、测试 theory 在私有树里的那一份。
- 私有树的提交：`1b3a1ae`（17:11，分支 `Isabelle2026/generic_mksimps`，没有推送）。
- 提交之后核对两个清单：
  - `tools/patched_files.txt` 与 `git diff-tree -r --no-renames --name-only c105fb8 HEAD` 的输出相同。
  - `isabelle-patch-control check-signatures` 退出码 1，报两处，**都在 `raw_simplifier.ML`、都是本次改动之前就有的**（对上一个头 `1aa94bd` 和当时的清单跑，报的完全相同）；`simp_steps.ML` 的六项没有报任何东西。
    1. `dest_ss` 这一项的类型变了（mksimps 处理器那部分给它加了字段 `mksimps_handlers`，是作者当时批过的设计）；这个检查不允许 base 里已有的签名项改变。
    2. `RAW_SIMPLIFIER` 签名里一段注释有一行以 `type variables not declared …` 开头（`:68`），检查工具把它当成了一项 `type`。
    这两处会在 release 时挡住 `make-patches`，不属于步数上限这件事；怎样处理要作者定。
- 代码评审：17:05 起（`wf_c3226e55-994`，题目 `simp_step_limit_code_review_brief_2026-11-22.md`，报告 `simp_step_limit_code_review_round1_2026-11-22.md`，都不提交）。
  17:40 结束，裁判判**可以接受**：`simp_steps.ML`、补丁、`ROOT.ML`、两个清单都没有要改的；九条意见四条成立、五条驳回，成立的都不改变代码的行为。
  - 成立：README 漏了 `Lazy` 那条规矩；README"拦不住的"漏了两种情形；"中断原样放行"没有一条在它被破坏时会失败的测试；测试里有两处重复的代码。
  - 修改要等作者同意（17:41 已报给他）；改了之后在这里记下。

**照代码评审改的**（2026-11-23；作者 02:23：「可以改代码」；改于 02:24 至 02:27；02:36 构建通过，随后提交，见本段末尾）
- 私有树没有动：`simp_steps.ML`、`raw_simplifier.ML`、`ROOT.ML` 都是 `1b3a1ae` 的样子。
- `README.md`：
  - "只有 `f` 返回之前的工作受限"那条后面加一句：求值时抛了 `EXCEEDED` 的 `Lazy` 值会把它永久记住，以后每次 `Lazy.force` 都重新抛出。
  - "拦不住的"头两项照裁判给的原文替换：补上证条件与 congruence 前提的 prover（它自己起的运行除外）；congruence rule 那一项写成"不引起任何运行"（没有前提，或前提由一个不是 simp tactic 的 prover 来证）。
  - `limited N f ctxt` 与 `charge k ctxt` 后面写上 `N ≥ 0`、`k ≥ 0`（裁判说可加可不加，本会话加了）。
- `tests/Simp_Steps_Test.thy`：
  - 第 12 组的第二条改成：两层 `limited 10` 嵌套，里层的函数先化简到被拒绝（用 `try` 吞掉），再抛 `Exn.Interrupt_Break`；要求出来的仍是这个中断。
    这是对第 8 节测试清单的又一处出入：原先那一条是在没有计数器到达上限时抛中断，一个把中断当普通异常接住的错误实现也能通过。
  - `check_closed` 原有两份（第 6 组、第 12 组），合成一个放进"Helpers"一节；第 6 组多出来的那条检查留在它自己的 `check_kept` 里。检查的名字与个数不变。
  - 事件日志改用测试基座的 functor（下一条），不再自己写一份。
- `tests/Generic_Mksimps_Test_Base.thy`（代码评审第 6 条的前一半，裁判留给作者定；本会话的建议是做，并把作者的「可以改代码」理解为包括它；这一处没有提交，要撤回很容易）：
  - 加 functor `Context_Log(type entry)`：一个挂在 context 上的日志，带 `log` 与 `logged`。
  - 原来的 `Call_Log` 改成 `Context_Log(type entry = string * thm)`；`log_call`、`calls_of` 保留为包装函数，mksimps 测试里用到它们的地方都不用改。
- 验证（02:26，探针，在共用的树上；不是构建）：
  - 测试 theory 全文通过；基座里 functor 与 `Call_Log` 那一段也原样编译通过。
  - 变异检查重跑：原来的 8 种仍然全部被抓到；新加第 9 种"把中断当普通异常接住"（`Exn.result` 换成 `Exn.capture0`），只有第 12 组新改的那一条检查失败，别的都通过。
  - **没有验证的**：mksimps 的几个测试 theory 用改过的基座还能不能通过。它们要用到 feature 本身，只有在私有树里构建测试 session 才知道；要作者下令。
- 作者 02:35：「下令构建」「构建通过后提交」「推送」；对测试基座里的 functor：「这个你可以自主设计」（保留）；并问「需要代码复审吗？」。
  - 构建 02:36，同一条命令，退出码 0。只重建了 `Generic_Mksimps_Test`（5 秒）；八个 theory 都通过，mksimps 的七个用的是改过的基座，`Simp_Steps_Test` 累计 1.3 秒。
  - 本会话对"要不要复审"的回答是不需要：实现本身（私有树的三个文件）在评审之后一行没有动；四处修改用的是裁判给的原文，裁判逐条写明不必再过一轮；
    functor 是裁判给的形状，只在测试里，已由这次构建与变异检查验证。

**`check-signatures` 报的那两处旧问题的处理**（2026-11-23；作者 02:43：「接受 dest_ss 多了一个字段」；对注释那一处「请你自决，我倾向于改注释的断行，但允许你动那个仓库」；「现在就做」。02:44 至 02:51 做完；作者 02:52「下令提交，推送」，工具仓库的提交是 `485cb2a`，已推送）
- 两处都改在检查工具里（`contrib/my_better_isabelle_prover`，`isabelle_patch_control/check_signatures.py`），本 feature 的 Isabelle 源码没有动，所以不用重建 Pure 与 HOL。
- **`dest_ss`**：清单里可以写一行 `changed <path> <SIGNATURE NAME> <keyword> <name>`，声明 base 里的这一项在这里换了类型；声明了的不再算错。
  - 清单仍然是精确的：声明了却没有改的会报 `listed as changed but not changed`；整个删掉的项不能声明，照旧报错。
  - 本 feature 的 `tools/signature_additions.txt` 加了一行 `changed src/Pure/raw_simplifier.ML RAW_SIMPLIFIER val dest_ss`，并在文件头注明是作者接受的。
- **注释**：本会话没有照作者倾向的"改注释的断行"，而是修了工具，理由三条：
  工具反正要为 `dest_ss` 改；改断行要重建 Pure 与 HOL，`concept` 的树合并之后也要再重建一次；修了工具，所有 feature 都不会再踩到。
  - 工具现在在签名段里认得跨行的与嵌套的注释。顺带改了三处读法：签名段的 `end` 后面带注释也认；遇到下一个 `signature` 时把手上的一项归给前一个签名；文件结束时把手上的一项记下。
- 验证：
  - 本 feature：`check-signatures` 退出码 0，报"1 listed as changed, 12 additions as listed"。
  - 本机七棵有清单的 feature 树，改之前与改之后各跑一遍：除了本 feature 少掉那一行误报之外，逐字相同。
  - 新旧两种读法在 Isabelle2026 与 AFP 的 1464 个 `.ML` 文件上逐个比较：1447 个相同；17 个不同，都是旧读法读错的
    （注释里以 `type`、`val` 开头的行被当成一项；老式文件里签名的 `end` 不在行首，项被归到了下一个签名）。
  - 工具自己的测试：`tools/tests/test_signatures.sh` 加了跨行注释与 `changed` 的用例，28 条全过（旧的读法在新加的注释上会多读出三项，所以这条测试对旧工具会失败）；
    另两个 toy 测试 92 条、116 条全过；`pytest` 198 条全过。
- 工具自己的计划文件（`ai-artifacts/ISABELLE_PATCH_CONTROL_PLAN.md`）没有记这两处改动；作者 02:52：「工具自己的计划文件不用记这两处改动」。

## 12. 修订记录

- 2026-11-22 13:20 UTC：初稿，作为单独的 feature `simp_step_limit`（文件当时在 `contrib/simp_step_limit/ai-artifacts/`）。
- 13:33：作者定做进 `generic_mksimps`。14:22：第一轮评审出报告。14:23：文件搬到这里，`GENERIC_MKSIMPS_PLAN.md` 加了一句指路。
- 14:30：第二稿。照第一轮评审的 F1 至 F8 改；照作者 14:25 的话，嵌套的 `limited` 改成各有各的上限，一次运行的开始也算一步；第 7 节改写成"作为 `generic_mksimps` 的一部分"；
  第 10 节改成列出交给本会话定的设计。初稿里把本会话的设计说成作者的话的两处（第 3 节标题、第 6 节嵌套的 N）已改正。
- 15:08：第三稿。照第二轮评审的 F9 至 F17 改：结束时先看外层的计数器、再看自己的；`charge k` 与走 k 步的效果完全相同，被拒绝的步不记账；
  每一列计数器都从开着的计数器造；删去"先问 `count` 就不必 `limited`"的建议，换成"要知道自己的工作有没有被拒绝就放进 `limited`"；写明哪些 context 带着这次运行的计数器；
  第 3 节的论证改准，补上 prover 与普通 congruence rule 那一种拦不住的情形；测试 3、7、8 补全；第 9、10 节重写。`limited` 的草稿里把负的 N 当作 0。
- 15:53：第四稿。照第三轮评审的 F18 至 F24 改：**被拒绝的步只记一次**（取代第三稿的"不记账"；`charge` 的草稿随之变短）；`charge` 在已有计数器到达上限时直接抛、k = 0 也一样；
  保证 2 与 `count` 的说法改准（计数器上记的不再说成"恰好是真正走了的步数"）；保证 3 的头一句改准；`limited` 的草稿改用 `Exn.result`、去掉类型不对的那一支；
  删去把负的 N 当作 0 的那一行（计数只增不减，它没有用处了）；第 9 节改成对照已通过的 v7，写明两处相抵与本稿不需要 client 的理由；测试 3、7 的数字与条目随之改。
- 15:55：第 9 节与第 10 节第 1 项记下 concept B 15:54 的答复（`concept` 照本接口办）。这是第四轮评审开始之后加的，只加了这一件事实，别处没有动。
- 16:31：第四轮评审判可以接受；照它的更正改入，仍称第四稿。
  - F25：被拒绝的步只记一次之后变得不准的四句话改准（保证 3 的两句、第 6 节"先看外层"的理由、第 10 节第 4 项），"没有余地"改成"到达上限"；
    第 6 节的代价一条写明里层被拒绝的那一步可能正好把外层记满，带例子；测试 3 加一条。
  - F26：第 5 节"缓存"改成命中时的 `charge` 也放进与填充相同的 `limited`（同一个上限、同一个 context），算 key 与查缓存在外面，带草稿与三个例子；
    第 9 节写明这对 `concept` 行为不变、两种写法由 concept B 定；测试 7 改一条、加两条；第 10 节第 10 项记下这条规矩。
  - F27：`charge k` 的说法里"一次走 k 步的填充"改成"一次记了 k 步的填充"（第 2 节与第 10 节第 10 项）。
  - `setmp` 的行号 `41-47` 改成 `41-48`。
- 16:40：记下作者的三句话：16:38「很好，批准开工」；16:39 对两个 REPL 探针「交给你自决了」；16:39「提交方案」。状态行、第 7 节、第 8 节随之改。
  同一分钟提交为 `8b830b3`（连同 `GENERIC_MKSIMPS_PLAN.md` 里那句指路），没有推送。
- 16:58：加第 11 节"实现记录"（写了什么、与草稿和测试清单的出入、探针验证了什么与没有验证什么、变异检查、开销的数字）；原第 11 节"修订记录"改为第 12 节。状态行随之改。
  这些是提交 `8b830b3` 之后的改动，随代码一起提交。
- 2026-11-23 02:52：第 11 节加"`check-signatures` 报的那两处旧问题的处理"一段。
- 2026-11-23 02:28：第 11 节加"照代码评审改的"一段（README 三处、测试 theory 三处、测试基座一处；探针与变异检查的结果）；此前 11-22 17:41 加了代码评审结果的几行。
- 17:12：第 11 节加"构建与提交"一段（构建通过；私有树提交 `1b3a1ae`；两个清单的核对，其中 `check-signatures` 报出两处本次改动之前就有的问题）；状态行记下作者 17:03 的三句话。
- 2026-11-28 03:13 UTC，concept A1：作者 2026-11-27 把"一步"改成"做成的一次改写"。第 3 节换成现行的定义（拦得住的、拦不住的、量过的数），以前的定义留作记录；
  第 8 节的测试 1、7 记下随之改的地方（looper 那一条去掉，条件证不出的带条件规则不算步，量出的数是改写数）。
- 2026-11-28 04:02 UTC，concept A1：代码评审（一个 Opus agent）之后：作者选 congruence rule 与 congproc 改了项也算一步；第 3 节重写成两种步与整张"拦不住的"清单；
  第 4 节补丁、升级时的核对、第 7 节、第 8 节的探针与测试、第 10 节第 2 项里讲旧做法的句子改准或标为以前的定义。
