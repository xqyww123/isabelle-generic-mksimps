# 通用的 pattern-based mksimps：施行计划（rev 3，方案评审已通过）

标记：【已定】作者已批；【提案】我的建议，未批，不能当作基线；【实测】跑过；【读源码】只读了源码。行号指本 feature 的私有树 `worktrees/Isabelle2026-generic_mksimps/src`，AFP 指 `contrib/afp-2026-10-26/thys`，phi-system 指 `MLML/contrib/phi-system`。作者原话对过会话转录。日期按 UTC。文中"作者"指项目所有者。

用语（全文只用这几个词）：

- **槽位**：simpset 里现有的那一个函数 `mk`，类型 `thm -> Proof.context -> thm list * Proof.context`，由 `set_mksimps`、`set_mksimps_context` 设置，`get_mksimps_context` 读出。一个 simpset 只有一个。HOL 的槽位是 `Simpdata.mksimps mksimps_pairs`。作者称它 default process、the default mksimp。
- **处理器**：本 feature 让人登记的函数，类型 `Proof.context -> thm -> (thm list * Proof.context) option`。登记时附一个名字、一个或多个 pattern、一个优先级，以及它会不会被 `clear_simpset` 清掉的标记。返回 `NONE` 表示"这条定理不归我管"。作者称它「mk_simps 处理器」、process、handler。
- **表**：simpset 里按 pattern 索引处理器的那张 Net。
- **分派**：拿一条定理到表里找出匹配的处理器，按优先级依次调用；第一个返回 `SOME` 的，其结果就是这条定理的全部规则；没有匹配的、或全都返回 `NONE`，交给槽位。
- **顺序模式**（作者的用语）：simplifier 先化简前提，再把它收进来。`asm_lr_simp_tac`（`simp (asm_lr)`）和 `asm_simp_tac`（HOL 证条件时的 subgoaler）是这样。
- **乱序模式**（作者的用语）：simplifier 先一次收进全部前提，再让前提互相化简。`simp` 默认的 `asm_full_simp_tac` 是这样，`auto`、`clarsimp` 也用它。

## 0. 来由与状态

本 feature 出自 concept 会话 2026-11-17 的讨论，随后作者把会话 fork 出来专做它（本会话，名字 "generic mksimps"）。作者原话，按时间：

- 「我在想，我们是不是可以 hack the simplifier，加入一个通用的 pattern-based mksimps 机制 `(Proof.context -> thm -> thm list * Proof.context) Net` 你觉得如何？如果你觉得好的话我可以 fork 出一个 agent 单独做一个 feature」
- 「很好，我 fork 了 session，我们专门来做这个 feature，我想需求是已经确定了」
- 「原本的 concept 工作你完全不用管了，完全交给你的另一个 fork」
- 「用 gh 做一个 public repository 构建在 concept 前的那个 base 上」
- 「先写一个施行计划，然后走方案评审」
- 第二批（对草稿的答复）：「名字：赞同 generic_mksimps Isabelle2026/generic_mksimps xqyww123/isabelle-generic-mksimps contrib/generic_mksimps」；pattern 匹配什么：「匹配交给 simplifier 的那条定理本身」「而且这会是一个递归机制，例如 `A /\ B` 的 mk_simps 处理器会递归对 A, B 调用 mksimps 你觉得如何？」
- 「记得方案评审通过后你才能开工」
- 「方案评审前你自己先通读一下，确保自洽，核实一下各个消息来源」
- 「新增接口的 signatures 让我看一眼」
- 第三批（看过 signatures 之后）：
  - 对"有处理器命中时，槽位不再对这条定理运行，处理器返回什么就是什么"：「没错」
  - 「建议把 signatures 改为：`val make_mksimps_handler: {patterns: term list, handler: Proof.context -> thm -> thm list * Proof.context} -> mksimps_handler`、`val add_mksimps_handler: string (*name*) * mksimps_handler -> Proof.context -> Proof.context`、`val del_mksimps_handler: string (*name*) -> Proof.context -> Proof.context`」
  - 「具体来说，没有命中时，fallback to a default process」
  - 「然后我们在 HOL_basic_ss 再额外给一个 `A /\ B` 的 process 去递归地对 A, B 调用 mksimps_context，返回其结果的并」「在 HOL 我们依旧设置 the default mksimp」
- 第四批（评审进行中）：「我认为 /\, ∀，If 是可以做的」「⟶ 要怎么做？化成 ==> 吗？」「此外我建议 the pattern matching 只匹配 the conlusion of `... ==> ...` 你觉得如何？」「此外各个 handler 是否需要一个优先级来区分多个 handlers 都匹配时去调用谁？」
- 第五批（看过第一轮评审的报告之后）：
  - 「同意做 /\, ∀，If, ⟶」
  - 「同意匹配之前先做一步 Variable.gen_all」
  - 「同意处理器拿到的是整条定理，连同前提」
  - 「同意concept 的处理器遇到带前提或带 unknown 的定理，不登记，直接返回默认的规则」
  - 「建议改类型为 val make_mksimps_handler: {patterns: term list, handler: Proof.context -> thm -> (thm list * Proof.context) option} -> mksimps_handler」「如果返回 NONE 就表示 PASS，选取匹配的处理器列表中的下一个，若下一个为空，则退回 fallbacks」
- 第六批：「候选的先后 建议优先级」「run Opus agent 查一下，除了 AutoCorres2，还有谁会覆写 HOL 的 mksimps 吗？」
- 第七批：「很好，我们先不管 AutoCorres2，phi-system 之后会我们做适配，你可以记一笔」；我据此确认"HOL 的四个 connective 处理器照原定默认登记、总是拆，不做只在需要时才拆"，作者答「理解正确」（第八批第 1 条）。
- 第八批：「那不如这样，mksimp handler 多一个参数指定"顺序模式"还是"乱序模式"交给 handler 自己去处理。然后我们这边，给每个规则一个 optionally mask 函数 `(Proof.context -> bool) option` 指示此 rule 是否可用。然后在乱序模式下写入的 intro rule 必须要配备 mask 来检查此 rule 是否可用。你觉得如何？」
- 第九批：
  - 「好的，赞同取消 "顺序模式 / 乱序模式"这个参数，那必须在注释里明确写明这些陷阱」
  - 「hyps_in_prems 这个名字太奇怪了需要更直接一点，例如 `val simproc_can_use_thm: Proof.context -> thm -> bool` 你觉得如何？然后注释里讲清楚」
  - 「建议先写进计划里，等评审通过后你再发送给 concept agent」
  - 「批准现在就把全部决定写进计划，然后通读」
- concept A1 会话转来作者对它说的话：「建议允许每个 handler 多一个 config 来决定它们自己是否会被 clear_simpset 清除。你觉得如何？若同意，请转发」。我在本会话里请作者确认。
- 第十批：「确认加这个配置」「第 8 节按建议」「优先级最大的是 0 吗？允许负数吗？应该给用户设置比 HOL.conj 等优先级更大的 handlers 以空间」
- 第十一批（看过复审的七条修改之后）：「这七条如果没有需要跟我讨论的我就不予置评了」。我判断七条都在已定设计之内、不需要作者定，据此写入 rev 3。
- 第十二批：我自行开工后被叫停：「等一下！我批准你开工了吗？」；问清进度后：「很好，建议准备 compact 后再开工」（见第 11 节）。压缩后：「开工」；实现中途：「请同步发起 Opus 代码评审」。
- 第十三批（看过代码评审的四条存活意见之后）：「以上四条如果不需要跟我讨论我不予置评」；要不要复审：「要」。
- 第十四批（构建期间）：「于此同时你可以提交，push，并通知 concept A1 rebase」；新文件逐个列出后，作者选了打包文件 9 个、测试 session 8 个、计划文件 1 个；「修测试代码时可以直接重跑，不用每次问我」；「与测试、文档相关的，在不改变需求、设计、与我的决策的前提下，你可以自决」。

状态（2026-11-17 15:55 UTC）：

- GitHub 仓库 `xqyww123/isabelle-generic-mksimps`（public）已建，克隆在 `contrib/generic_mksimps`。私有树 `worktrees/Isabelle2026-generic_mksimps` 在分支 `Isabelle2026/generic_mksimps` 上，起点 `origin/Isabelle2026/dot_syntax`（`c105fb8`），分支已推到 origin（`xqyww123/isabelle-patched`）。stock 树在 `c105fb8`。
- feature 仓库里 `new-tree` 已暂存 `.gitmodules` 和两棵树，**没有提交**（注册提交等作者下令）。`init.sh`、`tools/*.txt`、`.gitattributes`、README 还没写。MLML 里没有登记子模块（等作者下令）。
- 第一轮方案评审（workflow `wf_b79ec858-d78`，2026-11-17）：未通过，六条意见 M1–M6。作者的裁定（第五批到第十批）和我对 M3–M6 的修改写入 rev 2，第 8 节全部定下。
- 复审（workflow `wf_7feff49e-d01`，2026-11-17）：**通过**，条件是做完七条在已定设计之内的修改 N1–N7；裁判认为 M1–M6 都已解决，改完不需要第三轮。N1、N2 我实测确认（探针 `ai-artifacts/probes/Rereview_Checks_Probe.thy`），实测时另发现 `\<^prop>` 根本不接受 `?x`。七条已写入本 rev 3（4.2、4.3、4.4、4.6、4.8、第 6 节）。评审明细不进任何仓库。
- 调查"谁覆写 HOL 的槽位"（作者第六批要求，Opus agent，2026-11-17）：结果写在 4.5 与第 10 节。
- ~~代码一行未动，未构建。~~ 作者令压缩后开工（第十二批），随后「开工」（2026-11-17 压缩后）。
- 实现（2026-11-17/18 UTC）：私有树三个文件已改（`Pure/raw_simplifier.ML`、`Pure/simplifier.ML`、`HOL/Tools/simpdata.ML`），**未构建、未提交**。feature 仓库已写测试 session `tests/`（8 个文件）与打包文件（`init.sh`、`.gitattributes`、`LICENSE`、`README.md`、`tools/*.txt`、`tools/release_build.sh`），**都未提交**。第 6 节第 1、2、7 条的期望值来自 stock 探针 `ai-artifacts/probes/Stock_Baseline_Probe.thy`（共享树上跑，不提交）。
- 代码评审（作者「请同步发起 Opus 代码评审」，workflow `wf_a8d83a09-fd5`）：裁判判可以构建测试；4 条存活意见（都是小改）。作者第十三批：「以上四条如果不需要跟我讨论我不予置评」「（复审）要」。四条已改：注释陷阱第 1 条补上 body 模式的例外（本计划 4.2、4.6 第 1 条同步）；分派先找候选、有候选才校正 maxidx，改用 `get_first`；条目类型改名 `mksimps_entry` 等；注释陷阱第 6 条恢复计划原意、第 2 条补全措辞。复审（一个 Opus agent）：四条都已解决，没有新缺陷；它指出的两处文字小毛病（陷阱第 1 条"处理器的上下文"补上"化简过程中"、README 一行过长）已改。评审明细不进任何仓库。
- 构建（作者「下令」，2026-11-18 02:30 UTC 起）：私有树 `build -b -v -d tests HOL Generic_Mksimps_Test`。Pure、HOL 通过（HOL 6:56）；测试 session 失败在 `tests/Generic_Mksimps_Test_Base.thy:71` 的 ML 类型错误（`map #1` 没给类型，测试本身的错）。之后按作者的授权修测试、重跑，又修了四处测试代码的错：`eq_list` 两边类型不同（改 `ListPair.allEq`）；记录处理器的 pattern 写成 `\<^prop>‹x::bool›`；期望里 `"a = b"` 改 `"(a::nat) = b"`（单独读进来是 `'a`）；第 6 条 `∀i. P (f i)` 拆出的定理期望从 `P (f ?x1)` 改为 `P (f ?x)`（我从最终规则抄错了编号，最终规则经 `RS Eq_TrueI` 才变成 `?x1`）。另让检查失败时打印实际值。**2026-11-18 02:53 UTC 测试 session 全部通过**（第 6 节第 1–16 条），feature 代码仍是 `94c1377`。已通知 concept A1。测试的这些修正尚未提交。第 17 条（开销）、第 19 条（变异检查）未做，要另外构建。
- 作者「于此同时你可以提交，push，并通知 concept A1 rebase」：私有树提交 `94c1377` 已推 origin；feature 仓库注册提交 `adf8396`（作者批准的 18 个新文件：打包 9 个、测试 8 个、本计划）已推 origin main；已通知 concept A1，它已按 SKILL 3.7 把 base 改成 generic_mksimps（私有树快进到 94c1377，它那边的推送交作者处理），等测试通过的通知。

**本会话不碰 concept 的任何文件**（`CONCEPT_UNARY_PLAN.md`、`CONCEPT_OWN_TYPE_PLAN.md`、`CONCEPT_INSTANCE_CONTEXT_PLAN.md`、`CONCEPT_TAT_NOTES.md`、`contrib/concept`），它们归另一个 fork。要告诉 concept 的内容在 4.8，评审通过后再发（作者第九批）。

## 1. 本质

**simplifier 每次要把一条定理变成改写规则时（`simp add:` 给的定理，以及化简 `A ⟹ B` 时收进来的前提 `A`），先拿这条定理的结论到表里按 pattern 找处理器，按优先级从高到低依次调用。第一个返回 `SOME` 的处理器负责这条定理的全部改写规则；它可以改上下文，也可以把定理拆开，对拆出的各部分再分派（递归）。没有处理器匹配、或匹配的都返回 `NONE`，照旧交给槽位。**

这句话的每一部分都是作者定的：按 pattern 匹配定理本身、能改上下文、递归（第二批）；命中后槽位不运行、找不到交给槽位（第三批）；只匹配结论（第四批，第五批同意）；`option` 与"`NONE` 交给下一个"（第五批）；优先级（第六批）。

HOL 现在的槽位内部就是这个形状，只是写死的【读源码】：`mk_atomize`（`HOL/Tools/simpdata.ML:105-123`）看定理结论的头常量，到 `mksimps_pairs`（`:186-192`）里查出一组 destruct rule（`∧` 对应 `conjunct1`、`conjunct2`，`∀` 对应 `spec`，`⟶` 对应 `mp`，`If` 对应 `if_bool_eq_conj RS iffD1`），作用之后对每个结果递归。本 feature 把这张写死的表打开：键从头常量变成 pattern，值从一组 destruct rule 变成 ML 函数，并且能改上下文；谁都可以登记，互不顶替。

## 2. 为什么需要

**第一个使用者是 concept。** `concept_fact`（证 `C t` 这类 concept fact 的引擎）要能用上 simplifier 手里的前提。例：`lemma "group G ⟹ x ∈ carrier G ⟹ monoid G"`，`simp` 把 `group G` 收成前提之后，`concept_fact` 的 simproc 证 `monoid G` 时要看得到它。做法是在前提收进来的那一刻把它登记进 concept 的上下文数据（intro table 的上下文部分），并附上惰性的 destruction 结果；之后 simproc 调多少次都只是查表。作者 2026-11-17 问的是「这个是要每次 simproc 启动时注册吗？能某种方式缓存此注册吗？」，这就是那个缓存。concept 的命令证义务时 cut 进去的前提走同一条路。

登记随上下文走：离开这条前提所在的蕴含，登记就不在了。但在这个蕴含之内，有几个时刻登记看得见、前提却不能用，使用者必须用 `simproc_can_use_thm` 检查（4.4）。

**为什么不能只用现有的槽位。**【读源码】

- 槽位本来就能改上下文：上游在 `HOL/Imperative_HOL/ex/Congproc_Ex.thy:471-507` 用"读出旧的、包一层、设回去"演示了这个用法。AFP 的 AutoCorres2 也这样用（`AutoCorres2/in_out_parameters.ML:2060-2070`）。
- 但它是单个槽位。两个 simpset 合并时只留第一个的（`merge_ss`，`Pure/raw_simplifier.ML:349-375`，`:349` 的注释 "ignores some fields of 2nd simpset"）。谁之后调 `set_mksimps`，之前包的那一层就没了。
- HOL 自己就在后面重设：`HOL/Set.thy:396-402`（给 `mksimps_pairs` 加上 `Ball`）、`HOL/Nominal/Nominal.thy:392-396`（加 `fresh`）；AFP 里 Transport 的 `Bounded_Quantifiers.thy:102-108`、Nominal2 的 `Nominal2_Base.thy:2294-2300` 同样。所以"包一层"在 `Main` 之后装上能用，但任何后来的重设都会静默地把它顶掉。
- 包一层也不按 pattern 分派：每个使用者都要在每条定理上自己判断相不相干。

## 3. 需求【已定】

来源：作者提出这个机制时给了第 1 条；我在 concept 会话的答复里（2026-11-17 10:59 UTC）列了"concept 这边对它的要求"四条，即第 2 到第 5 条，并在同一答复里写了"通用，Pure 不认识 concept"，即第 6 条的前半；作者随后说「我想需求是已经确定了」。

1. 处理器登记在一张按 pattern 索引的 Net 里。类型原为 `Proof.context -> thm -> thm list * Proof.context`（作者原话：「一个通用的 pattern-based mksimps 机制 `(Proof.context -> thm -> thm list * Proof.context) Net`」）；作者第五批改为 `Proof.context -> thm -> (thm list * Proof.context) option`。
2. 处理器能改上下文，改过的上下文接着用于化简后面的部分。收前提的路径现在就是这样传的（`rules_of_prem`，`:1319-1330`：`val (rews, ctxt'') = extract_safe_rrules asm ctxt'`，`ctxt''` 往下传），要保持。
3. 存放在 simpset 里，和槽位分开：别人调 `set_mksimps` 不会顶掉它；不同的 simpset（系统的、concept 的 selector Simpset）各有各的一份。
4. 两个 simpset 合并时不出重复：每条登记要有身份。作者第三批定为名字（4.1）。
5. 表为空时，行为与现在逐字相同。simplifier 处理前提的核心代码不改（4.4），所以这一条照字面成立。
6. 通用：Pure 不认识 concept，也不认识任何 object logic。后半是我加的引申，作者第十批「第 8 节按建议」批准；它本来也由加载顺序决定（`raw_simplifier.ML` 在 `Pure/ROOT.ML:204` 编译，`Isar/object_logic.ML` 在 `:232`）。

## 4. 设计

### 4.1 数据【已定：第三、十批】

表放进 simpset 的 `mk_rews` 记录（`:282-287`），与槽位 `mk` 并列，暂称 `mk_handlers`：

```ML
mk_rews:
 {mk: thm -> Proof.context -> thm list * Proof.context,
  mk_handlers: (条目) Net.net,     (*新增*)
  mk_cong: ..., mk_sym: ..., mk_eq_True: ..., reorient: ...}
```

Net 里每个 pattern 一条条目：`{name: string, pattern: term, priority: int, kept_by_clear_simpset: bool, handler: Proof.context -> thm -> (thm list * Proof.context) option}`。对外的类型 `mksimps_handler`（4.6）是登记之前的样子：若干 pattern、一个优先级、一个标记、一个函数，不含名字；名字在登记时给。

- 【已定】**身份是名字**（作者第三批的 signatures）。不用 stamp。这与同一个文件里 looper 的接口同形【读源码】：`add_loop: string * (Proof.context -> int -> tactic) -> …`、`del_loop: string -> …`（`:82-83`，定义在 `:865-875`）。
- 一个处理器可以带多个 pattern：每个 pattern 一条条目，名字相同（simproc 的 `lhss` 是同样的拆法：`split_proc`，`:800-801`）。
- 表与槽位是同一个记录里的两个字段，互不影响：`set_mksimps`、`set_mksimps_context` 只换 `mk`，不动 `mk_handlers`（需求 3）。
- **放进 `mk_rews`（第 8 节，第十批批准）。** 理由：
  - `empty_ss`（`:339-346`）给出初始的 `mk_rews`，表因此随 `empty_simpset` 一起清空，不用另写。
  - 改动小。第二个分量的七元组在 15 处被解构（`map_ss2'` 的各个调用）；`mk_rews` 的记录只在 `empty_ss` 里构造一次、在 `map_mk_rews`（`:815-823`）里重建一次，五个 `set_mk…`（`:830-843`）不用动。
- **`clear_simpset` 只保留标记为 `true` 的处理器【已定：第十批「确认加这个配置」】。** `clear_simpset`（`:408-410`）今天原样保留 `mk_rews`；改后它过滤表，只留 `kept_by_clear_simpset = true` 的条目。`empty_simpset` 照旧清空全部，不看标记。为什么需要、谁该填什么，见 4.6。
- **名字相同时的三条规矩（第 8 节，第十批批准）**，都照 looper 的做法：
  - **合并**：两边有同名的处理器，整个留第一个 simpset 的（looper：`AList.merge (op =) (K true)`，`:369`）。做法：收集第一张表里出现的名字（`Net.content`），丢掉第二张表里凡是这些名字的条目，再把剩下的并进来。不能直接用 `Net.merge` 按名字判等：它是逐个 pattern 去重的（`Pure/net.ML:98-100`、`:252-253`），同名而 pattern 不同的两个版本会都留下、混在一起（评审 M6）。这种情形不需要谁违约就会出现：T1 在 `P ?x` 上登记 `foo`；T2 import T1，用 `foo` 在 `Q ?x` 上重新登记；T3 同时 import T2 和 T1 的另一个没改过的后代。
  - **`add_mksimps_handler` 遇到已有的名字**：先按各条目存着的 pattern 删掉这个名字的全部条目，再插入新的（looper：`AList.update`，`:868`）。
  - **`del_mksimps_handler` 遇到没有的名字**：给一条 warning，不报错（looper：`:873-875`）。
  - 名字由登记的人保证不撞，建议带上自己的前缀（如 `HOL.conj`、`concept.group`）。ML 层的用户按契约守约。
- 合并时其余字段（槽位等）仍取第一个 simpset 的，保留 `merge_ss` 开头的 `pointer_eq` 捷径。优先级和 `kept_by_clear_simpset` 存在每个条目里，合并时跟着条目走。

### 4.2 分派【已定】

**pattern 是命题**（评审 M3 的修改）：类型 `prop`，带 object logic 的判断，在 HOL 里是 `Trueprop (…)`。它与定理的结论比较，结论也是 `prop`。本文为了好读，写 `group ?x`、`?A ∧ ?B` 时省略了 `Trueprop`，与 Isabelle 平常的写法一样。

**pattern 的写法和登记时的一般化**（复审 N2，实测）：

- 像 simproc 的 lhs 一样，用自由变量写：ML 里写 `\<^prop>‹group x›`。`\<^prop>‹group ?x›` 写不出来：`\<^prop>` 不接受 `?x`，直接报 "Unbound schematic variable"。
- 用 `\<^prop>` 读进来的项，自由变量是 `Free`，类型变量是固定的 `TFree`。实测 `\<^prop>‹finite A›` 去匹配 `finite (S :: nat set)` 结果是 `false`，不报错。带类型变量的谓词（concept 的谓词都是，`'z concept_scheme`）因此会悄无声息地永远匹配不上。
- 所以 `add_mksimps_handler` 在检查之前先把 pattern 一般化，照 `Simplifier.make_simproc`（`Pure/simplifier.ML:116-123`）的做法：用 `Variable.add_fixes_implicit`、`Variable.declare_term` 把 pattern 加进登记时的上下文，再用 `Variable.export_terms` 导回去。没被登记上下文固定的自由变量、没被它声明的类型变量都变成 unknown，被固定的保持不变。**例外（代码评审 `wf_a8d83a09-fd5` 指出，原句漏了）**：登记上下文在证明体内时（`Variable.is_body`：Isar 证明里的目标上下文、`Goal.prove`、化简过程中交给处理器或 simproc 的上下文），`Variable.add_fixes_implicit` 什么都不做，于是没固定的自由变量和它们类型里的类型变量原样留下；例如在证明方法里登记 `\<^prop>‹finite A›`，存下的是 `finite (A :: 'a set)`，匹配不上 `nat set`，且不报错。`make_simproc` 在证明体内也是这样。所以要从 theory 或 local theory 的上下文登记（本计划的用法都是这样）。评审提过"登记时强制关掉 body 模式"，裁判否决：证明里 `fix x` 之后会报 "Duplicate fixed variable"，目标里的变量照样被固定，规则仍不统一。`make_simproc` 用的 `Proof_Context.augment`（`Pure/Isar/proof_context.ML:578-581`）就是这两步再加 `Soft_Type_System.augment`；后者在 `raw_simplifier.ML` 加载时还不存在（`Pure/ROOT.ML:204` 对 `:237`），也用不到。实测：一般化后 pattern 是 `finite (?A :: ?'a set)`，与 `make_simproc` 存下的一样，匹配 `nat set` 为 `true`。
- 一般化之后用 `Sign.cert_prop` 检查（替换草稿里的 `Sign.cert_term`，不是新加一道检查）。它能拦住的是把 `bool` 类型的项当成 pattern（如 `\<^term>‹group x›`）；让带类型变量的 pattern 能匹配上的，是上一条的一般化。表里存的是一般化之后的 pattern，按名字删除时用的也是它。
- HOL 的四个处理器不受影响：它们的 pattern 取自已存的定理，本来就是 unknown。

分派 `mksimps_context thm ctxt` 的步骤：

1. **表为空**：直接调槽位，不做 `Variable.gen_all`，不查 Net（需求 5）。
2. **取要匹配的项**【已定：第四、五批】：`thm' = Variable.gen_all ctxt thm`，取 `Thm.concl_of thm'`，做 eta 收缩（照 simproc 的查找，`:1024-1026`、`:1127`）。只看结论：`A ⟹ B` 匹配的是 `B`。
   - 先做 `Variable.gen_all`：最外层的 `⋀x` 换成 unknown `?x`（`Pure/variable.ML:510-514`）。前提 `⋀i. group (G i)` 的结论因此是 `group (G ?i)`，匹配得上 `group ?x`。HOL、FOL、ZF、Sequents 的槽位都先做这一步（`HOL/Tools/simpdata.ML:125`、`FOL/simpdata.ML:53`、`ZF/pair.thy:15`、`Sequents/simpdata.ML:75`）。
   - 只看结论，是递归穿过 `⟶` 所必需的：`A ⟶ B ∧ C` 经 `mp` 成为 `A ⟹ B ∧ C`，`∧` 的处理器要在结论 `B ∧ C` 上匹配。`mk_atomize` 看的也是 `Thm.concl_of`（`HOL/Tools/simpdata.ML:115`）。
3. **找候选**：`Net.match_term` 取，`Pattern.matches` 确认（simproc 的做法：`:1127` 取，`:1101` 确认）；按名字去重（一个处理器的两个 pattern 都命中时只算一次）；**按优先级从高到低排，同优先级按名字的字典序**【已定：第六批】。这个顺序只取决于表的内容，不取决于登记或合并的先后。Net 本身不记先后，合并后的顺序也无定义（`Pure/net.ML:252-253` 的注释 "FIXME non-canonical merge order"）。
   - **优先级是任意整数**，没有上限，允许负数（作者第十批问到，要给用户留出比 `HOL.conj` 等更高的空间）。HOL 的四个处理器用 0（4.5），两边都有空间：要排在 HOL 前面（例如为 `group ?x ∧ ?B` 写的专门处理器要抢在 `HOL.conj` 之前）用正数；要排在所有人后面（例如兜底的 `Trueprop ?P`）用负数；和 HOL 同为 0 时按名字的字典序。
4. **依次调用**【已定：第五批】：把 `thm'' = Thm.adjust_maxidx_thm ~1 thm'`（整条定理，连同前提，第五批）和 `ctxt` 交给第一个候选。返回 `SOME (rules, ctxt')`：这就是结果，后面的候选不再调用。返回 `NONE`：换下一个候选，交给它的仍是原来的 `ctxt`。
   - 为什么校正 maxidx（复审 N1，实测）：定理上记着的 maxidx 只是 unknown 编号的上界。实测假设 `P a ∧ R b` 得到的定理 maxidx 是 −1，`RS conjunct1` 得到的 `P a` 不带任何 unknown，记着的 maxidx 却是 0，校正后才是 −1。不校正的话，处理器用 `Thm.maxidx_of th >= 0` 判断"带不带 unknown"会出错，concept 的处理器会把合取拆出的 `group G` 当成带 unknown 而返回 `NONE`。校正之后 maxidx 是准的：恰好在定理不带（类型）unknown 时为 −1。
   - 先 `Variable.gen_all`、后校正：`gen_all` 选的新编号与槽位自己做 `gen_all` 时相同，HOL 产出的规则因此与今天一致。`raw_simplifier.ML:1553` 有同样的两步，顺序相反。
   - 命题不变；第 5 步交给槽位的仍是原定理；第 1 步表为空时不做这一步。
5. **都不管**：没有候选，或全都返回 `NONE`，交给槽位【已定：第三、五批】。交过去的是原来的 `thm`，没有做过 `Variable.gen_all`（第 8 节，第十批批准）。理由：Pure 默认的槽位（`empty_ss`，`:341`）不做这一步，`⋀x. f x ≡ g x` 今天在它那里得不到规则，改后也必须得不到。

**处理器的结果就是最终的改写规则，不再被分派。** 递归由处理器自己发起：它把定理拆成更小的定理，对每个调 `mksimps_context`。会不会停机由处理器的作者负责（一个把自己拿到的定理原样再分派的处理器会死循环）。ML 层的用户按契约守约，不加运行时防御。

**已知的限制。** 第一个返回 `SOME` 的处理器负责全部结果，所以同一条定理上优先级低的处理器不会被调用。两个都只想"登记一下、规则照旧"的处理器落在同一条定理上时，只有优先级高的那个登记得上。现在只有 concept 一个这样的使用者，先记为限制；以后真有需要，可以加一个"在比我优先级低的候选里继续分派"的函数，不改已有的类型。另一个相关的情形见 4.6 陷阱第 2 条：处理器直接调槽位时，槽位内部拆出的部分不会再经过表。

（草稿里我曾建议改为匹配槽位产出的每条规则的左边，作者没有采纳。处理器拿到的是定理本来的样子，如 `group G`，而不是 `group G ≡ True`；"匹配产出的规则"今天包一层槽位就能做。草稿里"多个处理器命中时全部调用、按登记先后、结果相连"已撤回：Net 不记先后，而且两个都调槽位取规则的处理器同时命中时，每条规则会出现两遍（评审 M2）。`option` 加优先级取代了它。）

### 4.3 处理器负责这条定理的全部结果【已定：第三批「没错」】

一条定理有处理器返回 `SOME` 时，槽位不对这条定理运行，处理器返回什么就是什么。草稿里"处理器的规则追加在槽位的结果之后"已撤回：`A ∧ B` 的处理器已经分别得到 `A`、`B` 的规则，槽位若再跑一遍，每条规则出现两遍。

两个例子：

- **connective 的处理器**。pattern `?A ∧ ?B`，拿到 `A ∧ B`：用 `conjunct1`、`conjunct2` 得到 `A`、`B`，各自调 `mksimps_context`，结果依次相连（作者说的"并"，先 `A` 的后 `B` 的，与槽位今天的顺序相同）。
- **只想登记、规则照旧的处理器（concept）**。pattern `group ?x`：
  - 拿到带前提或带 unknown 的定理（如 `A ⟹ group G`、`group (G ?i)`），返回 `NONE`，不登记（第五批同意的"不登记，直接返回默认的规则"；`NONE` 之后由下一个候选或槽位产出规则）。
  - 拿到前提 `group G`：把它登记进 intro table 的上下文部分，再自己调槽位取默认的规则，返回 `SOME ([group G ≡ True], ctxt')`。

判断"带不带 unknown"用 `Thm.maxidx_of th >= 0` 即可，因为分派交来的定理 maxidx 已校正（4.2 第 4 步）。

处理器自己调槽位时，交给槽位的是它手里的定理，也就是做过 `Variable.gen_all` 的。对 HOL、FOL、ZF、Sequents 的槽位这没有区别，它们自己也先做这一步。这与 4.2 第 5 步不矛盾：那一步说的是没有处理器管的情形，那时必须与今天逐字相同。

### 4.4 调用点与登记的可见范围

**调用点【读源码】。** simplifier 自己把定理变成改写规则时，调用槽位的地方只有 `extract_rews`（`:599-604`）：

```ML
fun extract_rews {sym} thm ctxt =
  let
    val mk = #mk (get_mk_rews ctxt);
    val (rews, ctxt') = mk thm ctxt;
    val rews' = if sym then rews RL [Drule.symmetric_thm] else rews;
  in (map (rpair (Thm.get_name_hint thm)) rews', ctxt') end;
```

把其中的 `mk thm ctxt` 换成 `mksimps_context thm ctxt`。`sym` 的处理、name hint 不变。（`:664` 附近另有一份 `extract_rews` 的调用在注释里，不是活代码。）

它有两条调用路径：

- **收前提**：`rules_of_prem`（`:1319-1330`）→ `extract_safe_rrules`（`:606-607`）。返回的上下文被保留并往下传。前提含 unknown 时 simplifier 根本不收（`:1320-1325`），也就不分派。
- **显式加规则**：`add_simps`、`add_flipped_simps`、`del_simps`（`comb_simps`，`:620-624`）和 `mk_rrules`（`:609-613`）。这条路径只取规则、丢掉返回的上下文（今天对槽位也是如此）。处理器在这里也会被调用，规则生效，对上下文的改动不生效。`del_simps` 走同一条路，所以加进去的和删掉的是同一组规则。

**公开函数 `mksimps ctxt thm`**（`:828`，现在是"调槽位、丢掉上下文"）也走分派（第 8 节，第十批批准），改为 `#1 (mksimps_context thm ctxt)`。理由：它的调用者要的就是"simp 会用的规则"。发行版里有 `Pure/Tools/find_theorems.ML:213`、`HOL/Library/rewrite.ML:61`、`Tools/eqsubst.ML:55`、`Tools/Code/code_runtime.ML:350`；AFP 与本项目里还有约十几处，其中 phi-system 的 `guard_cache.ML:200-207`、`rule_generation.ML:321-324` 明说要"和普通 simp 声明一样的规则"。不走分派，一旦有别的处理器，这些调用者就和 simp 不一致。

**登记的可见范围【实测，评审 M4】。** 处理器在收前提时写进上下文的东西，在这条前提所在的整个蕴含里都看得见。顺序模式下这正好是前提的作用域。乱序模式下多出三个时刻：

1. **化简这条前提自己的时候。** 乱序模式先用 `mut_impc0`（`:1375-1382`）一次收进全部前提，上下文一路传下去；再由 `mut_impc` 用其他前提的规则化简每一条前提（`:1395-1396`）。化简前提 P 时，simplifier 特意不用 P 自己的规则和假设（前提不能证明它自己），但上下文里已经有 P 的处理器写下的东西。
2. **这条前提被改写之后。** P 被改写成 P' 时，simplifier 对 P' 重新收一次（`:1406`），但 P 的登记还留在上下文里，没有人删它。
3. **最后重新拼合 `P ⟹ C` 的时候**（复审 N4）。乱序模式化简完结论后，由 `rebuild`（`:1360-1371`）一层层把前提拼回去，并试着改写 `P ⟹ C` 这一整项；那里在 P 的作用域之外，P 不在 `prems_of` 里，但 P 的登记还看得见。这个时刻实际影响不大，列出来是为了完整。

这几个时刻里用 P 的登记得出的东西带着假设 P，而 simplifier 消不掉这个假设，证明最后报 "Undeclared hyps"。这一步现在是读源码得出的（评审两轮都这样读），由第 6 节第 2 条的端到端测试实测。

探针（没有本 feature 的 Isabelle2026，`ai-artifacts/probes/Premise_Visibility_Probe.thy`：一个把收到的每条定理都记进上下文的槽位，一个在 `P _` 处报告所见的 simproc）的结果。前四列是实测；最后一列是按源码读出的判断，由第 6 节第 2 条实测：

| 模式 | 命题，位置 | 上下文里记着 | `prems_of` | P 的登记能不能用 |
|---|---|---|---|---|
| 乱序 | `P a ⟹ R`，化简前提 `P a` 自己 | `P a` | 空 | 不能（时刻 1） |
| 乱序 | `a = b ⟹ P a ⟹ R`，`P a` 已改写成 `P b` | `P a`、`a = b` | `a = b` | `P a` 不能（时刻 2）；`a = b` 能 |
| 乱序 | `P a ⟹ P c ⟹ R`，化简前提 `P a` | `P c`、`P a` | `P c` | `P c` 能，`P a` 不能 |
| 顺序（`asm_lr`） | `P a ⟹ P c ⟹ R`，化简前提 `P c` | `P a` | `P a` | `P a` 能 |

另外两行实测：乱序模式下 `P a ⟹ P c ⟹ R` 化简前提 `P c` 时也是对称的结果；顺序模式下 `P a ⟹ R` 化简前提 `P a` 自己时，上下文里什么都没记（先化简、后收）。HOL 证条件用的 `asm_simp_tac` 不化简前提，simproc 在前提上没有触发。

**判据**：一条登记此刻能不能用，等于问"它的每个假设，是不是此刻 `Simplifier.prems_of ctxt` 里某条前提的命题"。上表最后一列全部符合这个判据。本 feature 提供这个判据的函数 `simproc_can_use_thm`（4.6）【已定：作者第八、九批；名字是作者提议、我赞同】。

**不加"顺序模式 / 乱序模式"参数【已定：第九批】**：同一个判据在两种模式下都对；在同一次化简之内，顺序模式下它恒为真。作者要求**在注释里明确写明这些陷阱**（4.6 列出注释必须写的内容）。

**嵌套化简换了 simpset 时**（复审 N3）：`prems_of` 读的是当前 simpset 的前提（`:490-491`）。simproc 里换上另一个 simpset 做嵌套化简时（`put_simpset` 装上存好的 simpset，`:394`；`clear_simpset`、`empty_simpset` 都从没有前提的 `init_ss` 起步，`:333-334`），新 simpset 里没有前提，判据因此拒绝外层收进来的全部登记。登记本身存在别的上下文数据里，换 simpset 后还在。这个错误偏向安全一侧（只会少用，不会用错），但外层的前提就用不上了。要用的话，换完 simpset 后用 `Simplifier.add_prems (Simplifier.prems_of 外层上下文)` 把前提带进去，判据就和外层一致；副作用是嵌套化简的 solver 也会拿这些前提去解目标（`HOL/Tools/simpdata.ML:130`、`:148`）。concept 用 selector Simpset 做的化简正是这种嵌套（4.8）。

**simplifier 处理前提的核心代码（`mut_impc0`、`mut_impc`、`rebuild`、`nonmut_impc`，`:1360-1440`）不改。** 我一度提议改它们，让登记只在结论里看得见；作者改用 mask 的做法（第八批），那个提议撤回。用 mask 还保留了一项能力：化简前提 B 时可以用前提 A 的登记（上表第三行的 `P c`）。

### 4.5 HOL 的 connective【已定：作者第三、四、五、七、十批】

**问题【实测】。** HOL 的槽位自己拆 `∧`、`∀`、`⟶`、`If`，拆的递归发生在槽位内部（`mk_atomize`），不回到表里。只登记了 `group ?x` 的处理器时，前提 `group G ∧ x ∈ carrier G` 在表里找不到处理器，整条交给槽位，`group ?x` 的处理器始终没有被调用。探针（`ai-artifacts/probes/Slot_Input_Probe.thy`，包一层槽位，记下它每次收到的定理和返回的规则）：

| 化简的命题 | 槽位收到的定理 | 槽位返回的规则 |
|---|---|---|
| `P a ∧ R b ⟶ Q c`（`simp`） | `P a ∧ R b`，整条 | `P a ≡ True`、`R b ≡ True` |
| `P a ∧ R b ⟹ Q c`（`asm_full_simp`） | `P a ∧ R b`，整条 | `P a ≡ True`、`R b ≡ True` |
| `(∀i. P (f i)) ⟶ Q c`（`simp`） | `∀i. P (f i)` | `P (f ?x1) ≡ True` |
| `(R b ⟶ P a) ⟶ Q c`（`simp`） | `R b ⟶ P a` | `R b ⟹ P a ≡ True` |
| `(∀x∈S. P x ∧ R x) ⟶ Q c`（`simp`） | `∀x∈S. P x ∧ R x` | `?x4 ∈ S ⟹ P ?x4 ≡ True`、`?x4 ∈ S ⟹ R ?x4 ≡ True` |

**【已定】**

- HOL 在构造 `HOL_basic_ss`（`HOL/Tools/simpdata.ML:194-202`）时登记处理器，覆盖 `mksimps_pairs` 里 destruct rule 非空的四项：`∧`、`∀`、`⟶`、`If`（第三批给了 `∧`，第四、五批加上其余三项）。由 `HOL_basic_ss` 派生的 simpset，包括 `Main` 的默认 simpset，都带着它们。
- `⟶` 用 `mp` 化成 `⟹`：`A ⟶ B` 变成 `A ⟹ B`，再分派；它的结论 `B` 继续被匹配（4.2 第 2 步）。最后产出条件改写规则，与今天相同（上表第四行）。`If` 离不开它：`if c then a else b` 经 destruct 成为 `(c ⟶ a) ∧ (¬c ⟶ b)`。
- `True`、`False` 不做处理器：它们的 rule 列表是空的，交给槽位结果相同（不产出规则）。
- HOL 的槽位照旧是 `mksimps mksimps_pairs`（`:200`），一行不改；`Set.thy`、`Nominal.thy` 等对槽位的重设也照旧（第三批「在 HOL 我们依旧设置 the default mksimp」）。
- **总是拆，默认登记**（第七、八批确认）。草稿里的"只提供、不默认登记"和评审后提的"只在拆开后有部分需要别的处理器时才拆"都不采用。

**生成方式（第 8 节，第十批批准）。** 由 `mksimps_pairs` 生成，不另写一份知识：四项各一个处理器，名字取常量名（`HOL.conj`、`HOL.All`、`HOL.implies`、`HOL.If`），优先级 0，`kept_by_clear_simpset = true`（它们产出的规则和槽位一样，留在 `simp only:` 里不改变结果；别的处理器在 `clear_simpset` 造的 simpset 里也靠它们看到 connective 里面的部分）。

- pattern：该项第一条 destruct rule 的第一个前提，本身就是命题：`conjunct1` 给 `Trueprop (?P ∧ ?Q)`，`spec` 给 `Trueprop (∀x. ?P x)`，`mp` 给 `Trueprop (?P ⟶ ?Q)`，`if_bool_eq_conj RS iffD1` 给 `Trueprop (if ?P then ?Q else ?R)`。
- 函数：做 `mk_atomize` 的一步 destruct，再对每个结果调 `mksimps_context`，结果依次相连，返回 `SOME`。destruct 的代码与 `mk_atomize` 共用（`mk_atomize` 先把定理里的 unknown 固定住再 destruct，`res_fixed`，`:109-113`；提出来共用，不复制）。destruct 失败（`THM`）时返回 `NONE`，定理落到槽位，槽位里的 `mk_atomize` 同样失败、把它当原子（`:118`），结果与今天相同。
- 分成四个处理器而不是一个：需要槽位一次看到整条定理的代码，可以在自己的上下文里用 `del_mksimps_handler` 删掉其中几个，恢复今天的输入。这也是下面 phi-system 适配的一条路。

**对 stock HOL 的后果【读源码，未实测】。** stock HOL 自己产出的规则不变，顺序也不变：处理器每一步做的正是 `mk_atomize` 的一步，深度优先、从左到右；拆到底的各部分落到槽位，槽位照旧处理 `Ball` 等它自己认识、处理器不认识的常量。评审对 `∧` 逐条核对过；四项都由第 6 节第 7 条的测试确认。

**会看到差别的代码【读源码；作者第七批：AutoCorres2 先不管，phi-system 以后由我们适配】。** 槽位此后看不到整条的 `∧`、`∀`、`⟶`、`If`，只看到拆开后的各部分。包着或换掉槽位、又装在带表的 simpset 上的代码会看到差别。调查结果（第 10 节有全部位置）：

- **AutoCorres2，少规则。** `c-parser/UMM_Proofs.ML:134-189`：包装先调一次 HOL 的槽位，再在得到的规则列表里同时找 `i <s n ≡ True` 和 `0 ≤s i ≡ True`（`:162`），两条都在才推出 `nat (sint i) < n ≡ True`。合取被先拆开，两条落在两次调用里，推不出来。用到它的 lemma：`doc/open_struct.thy:1303-1306`（`(i::32 signed word) <s 4 ∧ 0 ≤s i ⟹ nat (sint i) < 4` by `simp`），多半会失败，simp 能否从别的路证出未测。若 `mksimps` 也走分派（4.4），另有两个入口受影响：`l2_opt.ML:322` 对整条 guard 调 `Simplifier.mksimps`，`Polish.thy:1730-1747` 的 `gen_mksimps`。作者：先不管。
- **AutoCorres2，规则可能不同。** `lib/ml-helpers/Tuple_Tools.thy:757-767` 先化简整条前提再拆，改后变成各部分分别化简。它唯一的实际用处（`doc/AutoCorresInfrastructure.thy:501-512`）里前提没有这四种 connective，不受影响。
- **phi-system，要适配。** `Phi_Logic_Programming_Reasoner/library/reasoners.ML` 的 `gen_simplify`（`:608-617`）把槽位换成"先用 `extract_prems`（`:578-601`）从整条定理里抽出带 `Premise` 标记的部分，再交给 HOL 的槽位"。
  - `use_origin = false` 的模式（调用处 `constr_abst.ML:219`、`PLPR.thy:2214`、`rule_generation.ML:344`）会多出规则。例：`Q ∧ Premise default P`，今天只产出 `P` 的规则、故意丢掉 `Q`；改后 `Q` 单独到达，抽不到东西，于是原样保留，多出 `Q ≡ True`。我读代码确认。
  - 两种模式都可能抛异常。例：`c ⟶ Premise default B`，改后槽位收到 `c ⟹ Premise default B`；`extract_prems` 看到结论是 `Premise`，对整条命题用只适用于 `Trueprop …` 的变换（`:593` 附近），抛 `CTERM`，simp 失败。`c ⟶ \<r>Guard X` 同理。调查的 agent 还读出 `c ⟶ Ant_Seq A B` 可能死循环，我没有核对。
  - 其余 37 个 `use_origin = true` 的调用处只是规则顺序变。
  - 适配的两条路：在 `gen_simplify` 的上下文里删掉 HOL 的四个处理器，槽位就和今天一样收到整条定理；或者让 `extract_prems` 接受带前提的定理。这是 phi-system 仓库里的事，本 feature 落地之后、按作者的命令做，不在本 feature 里。
- **只是规则顺序变的**：AutoCorres2 `in_out_parameters.ML:2060-2070`、`:2231-2243`，发行版 `Congproc_Ex.thy:491-507`，phi-system `library/tools/simplification_protect.ML:13-25`。顺序只在同一条定理产出的两条规则争同一个项、并且权重相同时才有影响。
- **不受影响**：从 `empty_simpset`、`empty_ss` 起步的槽位，表是空的（`lin_arith.ML:107-114`、`quotient_tacs.ML:35-38`、`function_elims.ML:40-50`、`Provers/hypsubst.ML:141-148`、`HOL/Prolog/prolog.ML:62-70`、Induct 的 simpset、AutoCorres2 的缓存 simpset、phi-system 的 `Empty_SS`）。其中 quotient、function_elims、hypsubst 三处故意不拆前提，它们只因为 `empty_simpset` 清空表才不受影响（4.6）。只加新常量的 `mksimps_pairs` 扩充（`Set.thy`、`Nominal.thy`、Transport、Nominal2、Zippy）产出的规则相同。没有找到"故意不拆、又装在带表的 simpset 上"的槽位。

**已知的限制。** `Ball`、`fresh`，以及 AFP 里 Transport 的 `ball_pred`、Nominal2 的 `fresh`，是各自的 `.thy` 通过重设槽位加进去的。它们继续由槽位处理，所以 `∀x∈A. group (f x)` 里面的 `group (f ?x)` 不会被分派。要补上得改这些 `.thy`（会改 theory key），本 feature 不做。FOL、ZF、Sequents 的 connective 同理留在各自的槽位里。

代码放在 `HOL/Tools/simpdata.ML`（ML 文件，不影响 theory key，见 4.7）。Pure 仍然不认识任何 object logic。

### 4.6 接口

加进 `Raw_Simplifier` 的 signature；`Simplifier` 用 `include RAW_SIMPLIFIER` 重新导出，不用另改（进 `tools/signature_additions.txt`）：

```ML
type mksimps_handler
val make_mksimps_handler: {patterns: term list, priority: int, kept_by_clear_simpset: bool,
  handler: Proof.context -> thm -> (thm list * Proof.context) option} -> mksimps_handler
val add_mksimps_handler: string (*name*) * mksimps_handler -> Proof.context -> Proof.context
val del_mksimps_handler: string (*name*) -> Proof.context -> Proof.context
val mksimps_context: thm -> Proof.context -> thm list * Proof.context
val simproc_can_use_thm: Proof.context -> thm -> bool
```

来源：`add`、`del` 是作者第三批逐字给的；`make_mksimps_handler` 的 `option` 是第五批，`priority` 字段是第六批（作者选了我提的"整数优先级"那一种），`kept_by_clear_simpset` 字段是第十批（作者确认加这个配置；字段名是我提的）；`mksimps_context` 这个名字作者在第三批用过，类型与槽位相同（第 8 节，第十批批准）；`simproc_can_use_thm` 的名字是作者第九批提议、我赞同。

- **`mksimps_context`** 是整套分派（4.2），供处理器递归用，类型与槽位相同（定理在前、上下文在后），可以直接用于 `fold_map`。名字照上游的约定：`set_mksimps` 不带上下文、`set_mksimps_context` 带上下文；`mksimps` 与 `mksimps_context` 同理。
- **`kept_by_clear_simpset`** 是必填字段，没有隐含的默认值，每个登记者都得明说。concept A1 曾建议"默认清掉"；做成必填，就不需要默认值。
- **`simproc_can_use_thm ctxt th`**：`th` 的每个假设，都是 `Simplifier.prems_of ctxt`（`:490`）里某条定理的命题（`aconv`）时为真。不带假设的定理恒为真。
- **处理器的参数顺序**照需求 1（上下文在前），不改。

**注释必须写明的陷阱【已定：作者第九批要求写清】。** `add_mksimps_handler` 和 `simproc_can_use_thm` 的注释写明下面这些，不靠读者自己推：

1. pattern 是命题，带 `Trueprop`；像 simproc 的 lhs 一样用自由变量写（`\<^prop>‹group x›`，`\<^prop>` 不接受 `?x`）；登记时，没被登记上下文固定的自由变量、没被它声明的类型变量都变成 unknown，被固定的保持不变；但登记上下文在证明体内时（`Variable.is_body`），没固定的自由变量和它们类型里的类型变量原样留下（4.2），所以要从 theory 或 local theory 的上下文登记。pattern 与定理做过 `Variable.gen_all` 之后的结论比较；处理器拿到的是做过 `Variable.gen_all` 的整条定理，可能带前提、带 unknown；它的 maxidx 是准的，恰好在不带（类型）unknown 时为 −1，所以可以用 `Thm.maxidx_of th >= 0` 判断带不带 unknown。
2. 返回 `SOME` 就负责这条定理的全部规则，槽位不再运行；要保留默认规则，自己调 `get_mksimps_context ctxt th ctxt`。返回 `NONE` 时，对上下文的改动一并丢弃。槽位不查表：HOL 的槽位自己拆 `∧`、`∀`、`⟶`、`If`，拆出的部分不会再经过别的处理器。所以只有定理不再往下拆时才该直接调槽位；还要让各部分经过别的处理器的，自己拆开，对每个更小的定理调 `mksimps_context`（第 5 条）。
3. 第一个返回 `SOME` 的处理器之后，优先级更低的候选不会被调用。优先级是任意整数，高的先调；HOL 的四个处理器是 0，要排在它们前面用正数，排在后面用负数；同为 0 时按名字的字典序。
4. `kept_by_clear_simpset`：`clear_simpset` 只保留填 `true` 的处理器。`simp only:` 和带定理参数的 `simplified` attribute 都用 `clear_simpset`，用户期望那里只有他列出的规则和前提。所以只有"不让产出的规则比槽位多"的处理器才应填 `true`（HOL 的四个、只登记前提的 concept）；会额外推出规则的处理器应填 `false`。`empty_simpset` 不看这个标记，总是清空全部。
5. 递归只对更小的定理调 `mksimps_context`，否则死循环。
6. 显式加规则的路径（`simp add:`、`[simp]`、`add_simps`、`del_simps`、`mksimps`）也会调用处理器，但对上下文的改动被丢弃；`del_simps` 也调用它，所以同一条定理必须给出同一组规则。
7. **收前提时写进上下文的东西，在乱序模式（`simp` 默认、`auto`、`clarsimp`）下，化简这条前提自己的时候、它被改写之后、以及最后重新拼合 `P ⟹ C` 的时候，都还看得见，但这时它不能用。** 凡是从这类登记里取定理来用的代码（simproc、solver、loop、subgoaler），都必须先用 `simproc_can_use_thm` 检查。在同一次化简之内，顺序模式下检查恒为真，所以不必区分模式。
8. `simproc_can_use_thm` 只适用于假设全部来自 simplifier 前提的定理，也就是处理器在收前提时拿到的定理及由它推出的东西。假设来自别处的定理（如 Isar `assume` 得到的事实，它的假设由 Isar 负责消掉，不在 `prems_of` 里）会被判为不可用，所以不要对它们用这个检查。
9. **嵌套化简换了 simpset 时，`prems_of` 是新 simpset 的，通常为空**（`put_simpset` 装上存好的 simpset，`clear_simpset`、`empty_simpset` 都从没有前提起步）。这时检查会拒绝外层收进来的全部登记：偏向安全，但外层的前提用不上了。要用的话，换完 simpset 后调 `Simplifier.add_prems (Simplifier.prems_of 外层上下文)`；副作用是嵌套化简的 solver 也会拿这些前提去解目标。

**已有、类型不变**（`Pure/raw_simplifier.ML:48-51`、`Pure/simplifier.ML:52`）：

```ML
val mksimps: Proof.context -> thm -> thm list   (*含义改为走分派，见 4.4*)
val get_mksimps_context: Proof.context -> (thm -> Proof.context -> thm list * Proof.context)   (*读槽位*)
val set_mksimps_context: (thm -> Proof.context -> thm list * Proof.context) ->
  Proof.context -> Proof.context   (*设槽位*)
val set_mksimps: (Proof.context -> thm -> thm list) -> Proof.context -> Proof.context   (*设槽位*)
```

**用法示意。**

```ML
(* ∧ 的处理器（示意；HOL 里真正的那个按 4.5 与 mk_atomize 共用 destruct，失败时返回 NONE） *)
fn ctxt => fn th =>
  SOME (fold_map Simplifier.mksimps_context [th RS conjunct1, th RS conjunct2] ctxt |>> flat)

(* concept 的 group ?x 的处理器（示意） *)
fn ctxt => fn th =>
  if Thm.nprems_of th > 0 orelse Thm.maxidx_of th >= 0 then NONE
  else
    let val ctxt' = (把 th 登记进 intro table 的上下文部分，配 mask simproc_can_use_thm) ctxt
    in SOME (Simplifier.get_mksimps_context ctxt' th ctxt') end
```

装进 theory 的 simpset：`Simplifier.map_simpset (Simplifier.add_mksimps_handler (name, h))`（`map_simpset`，`:406`）；也可以只装进某个自建的 simpset。`make_mksimps_handler` 没有上下文参数，所以 pattern 的一般化和检查都放在 `add_mksimps_handler` 里做（4.2）。

**`dest_ss` 与 `print_simpset`（第 8 节，第十批批准）**：`dest_ss`（`:29`、`:320-329`）加一个字段，列出每个处理器的名字、优先级、`kept_by_clear_simpset` 和 pattern，形状照 `simprocs` 那个字段；`print_simpset`（`Pure/simplifier.ML:265` 的 `pretty_simpset`）显示出来。发行版里 `dest_ss` 唯一的使用者是 `simplifier.ML:293`，用 `#字段` 取值；AFP 里没有使用者。

**"清空"时表的去留【读源码；`clear_simpset` 的标记：已定，第十批】**：造 simpset 的地方只有三处。`empty_ss`（`:339-346`，`empty_simpset` 用它，`:398`）：表为空。`clear_simpset`（`:408-410`）：只留 `kept_by_clear_simpset = true` 的处理器（4.1）。`merge_ss`：按 4.1 合并。`simpset_map`（`:396`）只是"装上、变换、取出"。`Pure/simplifier.ML` 在 `:433`（带定理参数的 `simplified` attribute）、`:467`、`:475`（`simp only:` 一类的方法参数）用 `clear_simpset`，今天保留槽位，改后同样保留槽位，并保留标记为 `true` 的处理器。

- `empty_simpset` 清空全部是要紧的：三处故意不拆前提的槽位（`function_elims.ML:48`、`quotient_tacs.ML:38`、`hypsubst.ML:148`）都写成 `Simplifier.empty_simpset ctxt |> Simplifier.set_mksimps …`。表清空了，它们才不受 HOL 的 connective 处理器影响。
- `clear_simpset` 只留标记为 `true` 的，是为了 `simp only:` 的含义：用户期望只有他列出的规则和前提；会额外推出规则的处理器不该悄悄留在那里（陷阱第 4 条）。
- concept 的 selector Simpset 是由 `clear_simpset` 造的（另一个 fork 的 `MLML/ai-artifacts/CONCEPT_UNARY_PLAN.md:396`，2026-11-17 读到的）。concept 的处理器填 `true`，就会留在里面；HOL 的四个也填 `true`，所以 concept 的处理器在那里同样看得到 connective 里面的部分。这正是 concept A1 转来这个配置的原因：定义实例时"祖先实例成立"作为前提 cut 进来，selector Simpset 里条件 `concept t` 要靠它消掉。

不提供 Isar 层的命令或 attribute，不做 morphism 变换（simproc 的 `Morphism.entity` 那一套）：第一个使用者在 theory 层按常量登记，用不到。以后要再加。

### 4.7 不做的

- 不改槽位的类型与语义，不改 `set_mksimps`、`set_mksimps_context`、`get_mksimps_context`。
- 不改 simplifier 处理前提的核心代码（4.4）。
- 不改任何 `.thy` 文件。Pure 一侧只动 `Pure/raw_simplifier.ML`（`Pure/simplifier.ML` 只在要显示处理器时动 `pretty_simpset`）；HOL 一侧只动 `HOL/Tools/simpdata.ML`。所以语义库的 theory key 不变：theory hash 只取 theory 全名、它自己的 `.thy` 文件内容、各 parent 的 hash（`MLML/contrib/Performant_Isabelle_ML/library/theory_hash.ML:180-190`），不含 `.ML` 文件。
- 不动 FOL、ZF、Sequents 的 `simpdata.ML`。
- 不为 `Ball`、`fresh` 等在 `.thy` 里加进槽位的 connective 生成处理器。
- 不在本 feature 里适配 phi-system 或 AutoCorres2（4.5）。

### 4.8 要告诉 concept 会话的内容【作者第九批：评审通过后再发】

1. 接口与语义：4.2、4.3、4.6。pattern 是命题，像 simproc 的 lhs 一样用自由变量写（`\<^prop>‹group x›`），登记时自动一般化，所以 concept 带类型变量的谓词也匹配得上。
2. concept 的处理器：带前提或带 unknown 的定理返回 `NONE`；不带的，登记进 intro table 的上下文部分，再调槽位取默认规则，返回 `SOME`。
3. **mask（作者第八批的设计）**：intro table 的规则带一个可选的 mask `(Proof.context -> bool) option`，指示此规则此刻能不能用。处理器在收前提时写进去的规则必须配 mask，即 `SOME (fn ctxt => Simplifier.simproc_can_use_thm ctxt th)`；theory 里登记的全局规则、Isar `assume` 得到的事实不配。理由与陷阱见 4.4 和 4.6 陷阱的第 7、8、9 条。
4. **嵌套化简**：concept_fact 在用户的 `simp` 里用 selector Simpset 做的化简，就是 4.6 陷阱第 9 条说的嵌套化简。那里 `prems_of` 是 selector Simpset 自己的，外层收进来的登记会被 mask 判为不能用；要用就在换 simpset 后 `add_prems` 外层的 `prems_of`。带不带、怎么带，由 concept 自己定。
5. selector Simpset 由 `clear_simpset` 造。concept 的处理器登记时填 `kept_by_clear_simpset = true`，才会留在里面；HOL 的四个 connective 处理器也是 `true`。这回应了 concept A1 转来的请求。
6. 优先级：concept 的处理器与 HOL 的四个 pattern 不重叠，填 0 即可；要抢在 HOL 前面才用正数。
7. concept 要用本 feature，就得把 base 从 `dot_syntax` 改成本 feature（SKILL `isabelle-patch-feature` 3.7）。那是 concept 会话和作者的事。

## 5. 改动清单【提案】

| 文件 | 改动 |
|---|---|
| `src/Pure/raw_simplifier.ML` | `mk_rews` 加 `mk_handlers`；`empty_ss`、`map_mk_rews`、`merge_ss`（按名字整个取舍）、`clear_simpset`（只留标记为 `true` 的处理器）；分派函数 `mksimps_context`；`extract_rews` 与 `mksimps` 改为调它；4.6 的接口与注释；`dest_ss` 加字段 |
| `src/Pure/simplifier.ML` | `pretty_simpset` 显示处理器；signature 不用改（`include RAW_SIMPLIFIER`） |
| `src/HOL/Tools/simpdata.ML` | 由 `mksimps_pairs` 生成 `∧`、`∀`、`⟶`、`If` 四个处理器，在 `HOL_basic_ss` 里登记；把 `mk_atomize` 里的 destruct 那一段提出来共用；槽位的设置不动 |

估计一两百行。Pure 和 HOL 的 heap 要重建。Pure 一侧需要的 `Net`、`Pattern`、`Variable`、`Sign`、`Thm`、`sort_distinct` 都在 `raw_simplifier.ML`（`Pure/ROOT.ML:204`）之前加载；`raw_simplifier.ML` 在 `ml_antiquotations.ML`（`:255`）之前编译，不能用 antiquotation，这部分也用不到。

## 6. 测试【提案】

放在 feature 仓库的 `tests/` 里一个测试 session（照 `contrib/default_fact_qualifiers/tests` 的做法），每条检查失败就让构建失败。构建要作者下令。结果写文件，不靠 `writeln`。规则同时经两条路观察：`Simplifier.mksimps_context`，以及 simplifier 自己的路径（`add_simps` 之后读 simpset 的规则；收前提时由结论里的 simproc 读）。这样测试不依赖 4.4 里 `mksimps` 走不走分派。

1. **表为空**：在 `empty_simpset` 上，以及在 `empty_simpset` 加 HOL 的槽位上，一组定理得到的规则与 stock 树上录的基准逐字相同。
2. **收前提与可见范围**（复审 N4 加强）：
   - 一个低优先级的处理器登记在 `Trueprop P`（一般化后是 `Trueprop ?P`，记下每条前提）上，把收到的定理记进上下文，再调槽位返回；一个 simproc 报告所见。把 4.4 的表逐行写成测试（乱序与顺序两种模式），每行检查记录是否看得见、`simproc_can_use_thm` 的判断是否与表中一致；再检查在蕴含之外看不见。
   - **端到端**：一个使用登记的 simproc，在 `Q x` 处用记下的 `P x` 和一条固定引理把 `Q x` 改写成 `True`；分"先查 `simproc_can_use_thm`"和"不查"两个版本，在表的各行和 `P a ∧ Q a ⟹ R` 上分别用 `asm_full_rewrite`、`asm_lr_rewrite` 跑。查的版本：结果定理 `Thm.hyps_of` 为空，能用的那几行确实改写了。不查的版本：在 4.4 的时刻 1、2，结果带着消不掉的假设。另用一条预期失败的 lemma 确认一次 "Undeclared hyps"。这一条实测 4.4 那张表的最后一列。
   - **区分对错判据的情形**：乱序模式 `P a ∧ R b ⟹ R'`，`HOL.conj` 拆出的登记 `P a` 的假设是 `P a ∧ R b`（不是 `P a`），在结论里能用，化简这条前提自己时不能用；乱序模式 `P a ⟹ P c ⟹ R`，一条同时带两个假设的定理，化简 `P a` 时不能用，在结论里能用；不带假设的定理总能用。
   - **嵌套化简**（4.6 陷阱第 9 条）：在结论里换上 `clear_simpset` 造的 simpset 后，判据对外层登记为假；`add_prems` 外层的 `prems_of` 之后为真。
4. **校正 maxidx**（复审 N1）：处理器记下收到定理的 `Thm.maxidx_of`；前提 `P a ∧ R b` 拆出的 `P a` 必须是 −1。`Main` 下用 4.6 示意里 concept 处理器的判断（`Thm.maxidx_of th >= 0` 就返回 `NONE`），前提 `P a ∧ R b` 和 `(P a ∧ R b) ∧ P c` 的每个合取支都被登记。
5. **pattern 的一般化**（复审 N2）：用 `\<^prop>` 和自由变量，在一个带类型变量的常量上登记处理器（如 `finite A`）；它必须在具体类型的前提（`finite (S :: nat set)`）、类型变量名不同的前提、`simp add:` 的多态定理上都被调用。登记上下文里固定的变量保持固定：在 `fix x` 的局部上下文里登记 `P x`，只匹配那个 `x`。
3. **处理器负责全部结果**：返回 `SOME ([], …)` 时 `P a ≡ True` 不在规则里；返回 `SOME`（槽位的规则）时在；返回 `NONE` 时由槽位产出。
6. **递归**：`Main` 的默认 simpset 下，前提 `P a ∧ R b`、`(P a ∧ R b) ∧ P c`、`∀i. P (f i)`、`R b ⟶ P a`、`if c then P a else R b` 中，`P ?x` 的处理器在每个该出现的部分上各被调用一次，拿到的定理分别是 `P a`、`P (f ?i)`、`R b ⟹ P a` 等；上下文沿递归传递。对照：在上下文里删掉 HOL 的四个处理器后，这些前提上 `P ?x` 的处理器不被调用。
7. **与今天等价**：`Main` 的默认 simpset 下，一组覆盖四项 connective 与 `True`、`False`、含嵌套、含 destruct 失败（如四个参数的 `If`）、含带 unknown 的定理、含 `Ball` 的输入，产出的规则与 stock 树上逐字相同、顺序相同。
8. **`⋀` 与带前提的定理**（评审 M5）：前提 `⋀y. R y ⟹ P y`，处理器在 `Trueprop (P ?x)` 上，恰好被调用一次，拿到 `R ?y ⟹ P ?y`；`simp add:` 一条带前提的定理同样。另：在 `empty_simpset` 上登记一个不相干的处理器后，`⋀x. f x ≡ g x` 仍然得不到规则（4.2 第 5 步）。
9. **显式加规则的路径**：`simp add: foo` 时处理器被调用，规则生效，对上下文的改动不生效；`del_simps` 删掉的是同一组。
10. **不被顶掉**：登记之后再 `set_mksimps`，处理器仍被调用。对照：用"包一层"的写法在同样情况下失效。
11. **合并**（评审 M6）：两个 theory 各登记一个不同名的处理器、第三个 theory 同时 import，两个都在；同一个处理器经两条 import 路径进来只调用一次。同名的情形按 4.1 的场景造：T1 在 `P ?x` 上登记 `foo`，T2 import T1、用 `foo` 在 `Q ?x` 上重新登记，T3 写成 `imports T2 T1'`（T1' 是 T1 的另一个没改过的后代），固定这个 import 顺序；断言留下的是第一个 parent T2 的版本（`foo` 在 `Q ?x` 上），`P ?x` 不再命中（复审 N5；theory 数据按 import 顺序从左往右合并，`Pure/context.ML:791`）。槽位仍取第一个 simpset 的。
12. **`option` 与优先级**：优先级高的先调（含正数排在 HOL 的 0 前面、负数排在后面）；返回 `NONE` 时换下一个（`NONE` 不带上下文，所以它对上下文的改动被丢弃是由类型保证的，不另测）；全都 `NONE` 时交给槽位；同优先级按名字的字典序；交换两个登记它们的 theory 的 import 顺序，结果不变；一个处理器的两个 pattern 都命中时只调用一次。
13. **名字**：`add_mksimps_handler` 用已有的名字时旧的被换掉（旧的 pattern 不再命中）；`del_mksimps_handler` 之后不再被调用；删一个没有的名字只给 warning。
14. **清空**：`empty_simpset` 之后所有处理器都不被调用（含 HOL 的四个、含标记为 `true` 的）；`clear_simpset`、`simp only:`、带定理参数的 `simplified` 之后，标记为 `true` 的仍被调用，标记为 `false` 的不被调用；经过合并之后，标记跟着条目走。另把第 6 条的递归输入（`∧`、嵌套 `∧`、`∀`、`⟶`、`If`）在 `simp only:` 下再跑一遍，配一个标记为 `true` 的 `P x` 处理器：它必须和默认 simpset 下一样在每个部分上被调用（复审 N5：这检查 HOL 的四个处理器标的是 `true`）。
15. **前提含 unknown 时不调用。**
16. **`mksimps` 走分派**：处理器返回 `SOME ([], …)` 时 `Simplifier.mksimps` 给出 `[]`。
17. **开销**：`Main` 的默认 simpset 下 `simp` 一组基准（含许多合取、全称、蕴含前提的）的耗时与 stock 树对比。
18. **整体回归**：构建 `HOL`（作者下令）。AutoCorres2 不作为本 feature 的验收条件（作者第七批：先不管）。
19. **变异检查作用于测试本身**，下列每个错误实现都应有测试失败：分派换成直接调槽位；不管 `NONE` 只调第一个候选；不按优先级（用 Net 的顺序）；丢掉返回的上下文；命中后仍调槽位；把做过 `Variable.gen_all` 的定理交给槽位；匹配整个命题而不是结论；匹配前不做 `Variable.gen_all`；交给处理器的是没做 `Variable.gen_all` 的定理；交给处理器前不校正 maxidx；登记时不一般化 pattern；合并直接用 `Net.merge`；合并留第二个 simpset 的版本；`mksimps` 绕过分派；`clear_simpset` 不看标记（全留或全清）；HOL 的四个处理器标成 `false`；`simproc_can_use_thm` 恒为真；`simproc_can_use_thm` 只要有一个假设在就算；`simproc_can_use_thm` 看定理的命题而不是假设。（草稿里"`NONE` 时不丢弃上下文的改动"这个变异写不出来，已删，复审 N7。）

## 7. 作为补丁式 feature【照 SKILL `isabelle-patch-feature` 3.6】

- **名字**【已定】：feature `generic_mksimps`，分支 `Isabelle2026/generic_mksimps`，仓库 `xqyww123/isabelle-generic-mksimps`，本地 `contrib/generic_mksimps`。conda 包名按规则是 `isabelle-generic-mksimps`。
- **base**【已定】：作者「构建在 concept 前的那个 base 上」，即 `Isabelle2026/dot_syntax`（concept 的 `.gitmodules` 里的 base；该分支现在停在 `c105fb8`，不是 dot_syntax 的 release，所以本 feature 现在还不能 release）。
- 步骤：(1) 建仓库并克隆，已做；(2) `new-tree`，已做；(3) 推分支，已做；(4) 加 `init.sh`、`tools/*.txt`、`.gitattributes`、README，未做；(5) 注册提交，等作者下令；(6) 在 MLML 登记子模块，等作者下令。
- 提交、构建、release 都等作者下令；只推 origin。

## 8. 待作者定

没有待定的设计点。下面七条原是待定点，每条我都给了建议（第一轮评审的裁判也建议同样的做法），作者第十批「第 8 节按建议」全部批准，已写进各节：

1. 4.2 第 5 步：没有处理器管时，交给槽位的是原来的定理（没有做过 `Variable.gen_all`）。
2. 4.1：表放进 `mk_rews`；名字相同时的三条规矩（合并整个留第一个、`add` 换掉旧的、`del` 没有的名字只给 warning）。
3. 4.4：公开函数 `mksimps` 也走分派。
4. 4.6：`mksimps_context` 的类型与槽位相同。
5. 4.6：`dest_ss` 与 `print_simpset` 列出处理器的名字、优先级和 pattern（加上第十批的配置后，也列 `kept_by_clear_simpset`）。
6. 4.5：HOL 的处理器按 `mksimps_pairs` 的四项分成四个，名字取常量名，优先级 0。
7. 第 3 节第 6 条的后半：Pure 也不认识任何 object logic。

字段名 `kept_by_clear_simpset` 是我提的，作者确认了这个配置，没有单独评论名字。

## 9. 里程碑

0. 草稿。已完成。
1. 建仓库、开私有树、推分支、本计划挪进仓库。已完成（2026-11-17）。
2. 第一轮方案评审（`wf_b79ec858-d78`）：未通过。作者裁定、调查覆写槽位的代码、写入 rev 2。已完成（2026-11-17）。
3. 通读 rev 2、作者定第 8 节（第十批）、复审 `wf_7feff49e-d01`：通过，七条修改 N1–N7 报给作者（第十一批不予置评）后写入 rev 3。已完成（2026-11-17）。
4. **评审通过后**：把 4.8 发给 concept 会话（作者第九批）——已发，concept A1 已确认收到。开工：作者令压缩后开工（第十二批，第 11 节）；实现、测试（构建等作者下令）、代码评审。
5. 注册提交、release，等作者下令；通知 concept 会话 feature 可用。
6. 本 feature 落地之后，按作者的命令适配 phi-system（4.5）。

## 10. 附：已核对的源码事实一览【读源码，2026-11-17】

Pure（`src/Pure`）：

- `raw_simplifier.ML:275-291`：simpset 的两个分量；`mk_rews` 的类型在 `:282-287`，其中槽位 `mk` 在 `:283`。
- `:48-51`：`mksimps`、`get_mksimps_context`、`set_mksimps_context` 的 signature；`:827-831` 定义，其中 `:828` 是 `mksimps`。`simplifier.ML:52`、`:77`：不带上下文的 `set_mksimps`。
- `:333-346`：`init_ss`、`empty_ss`（默认槽位在 `:341`：结论是 `≡` 就原样返回，否则返回空）。`init_ss` 只被 `empty_ss`（`:340`）和 `clear_simpset`（`:410`）调用。
- `:349-375`：`merge_ss`，`mk_rews` 取第一个 simpset 的；simproc 的合并在 `:367-368`，looper 的合并在 `:369`。
- `:396`、`:398`、`:406`、`:408-410`：`simpset_map`、`empty_simpset`、`map_simpset`、`clear_simpset`。
- `:490`、`:493`：`prems_of`、`add_prems`。
- `:599-613`：`extract_rews`、`extract_safe_rrules`、`mk_rrules`。`:620-637`：`comb_simps`、`add_simps`、`add_flipped_simps`、`del_simps`，丢掉返回的上下文。
- `:815-843`：`map_mk_rews`（`:815-823`）与五个 `set_mk…`（`:830-843`）。`map_ss2'` 在文件里出现 16 次，1 次定义、15 次使用。
- looper 的接口：signature `:81-83`；`add_loop` `:865-868`（`AList.update`）；`del_loop` `:870-875`（没有该名字时 warning）。
- `:226-232`：simproc 的 `procedure` 数据类型（身份 `id: stamp * thm list`）；`:237-238` `eq_procedure_id`；`:753-759` `cert_simproc`；`:800-801` `split_proc`；`:1024-1026`、`:1101`、`:1127` simproc 的查找与匹配。
- `:1319-1333`：`rules_of_prem`（`:1319-1330`）、`add_rrules`（`:1332-1333`）。`:1360` `rebuild`，`:1375-1382` `mut_impc0`，`:1384-1415` `mut_impc`（化简前提在 `:1395-1396`，改写后重收在 `:1406`），`:1418` `nonmut_impc`。`:1467` 收前提的路径上下文不可见（`set_visible false`）。
- `simplifier.ML:352-354`：`asm_lr_simp_tac` 的模式 `(true, true, false)`，`asm_full_simp_tac` 的模式 `(true, true, true)`（第三位是乱序）；`:481-483`：`simp` 方法默认用 `asm_full_simp_tac`，`(asm_lr)` 选 `asm_lr_simp_tac`。`simplifier.ML:54-57`：`asm_rewrite`、`asm_lr_rewrite`、`asm_full_rewrite`。
- `more_thm.ML:271-277`：`declare_hyps`、`assume_hyps`（收前提时把假设登记进上下文）；`:294` 起 `check_hyps`（"Undeclared hyps"）。
- `variable.ML:510-514`：`gen_all`。`net.ML:98-100`：`insert` 只在同一个叶子里判重；`:252-253`：`merge` 逐条重新插入，注释 "FIXME non-canonical merge order"。
- `ROOT.ML:204`：`raw_simplifier.ML`；`:232`：`Isar/object_logic.ML`；`:255`：`ML/ml_antiquotations.ML`。

HOL 与其他 object logic：

- `HOL/Tools/simpdata.ML:105-125`：`mk_atomize`（`res_fixed` 在 `:109-113`，失败当原子在 `:118`）、`mksimps`（`map_filter (try mk_eq) o mk_atomize ctxt pairs o Variable.gen_all ctxt`）；`:186-192` `mksimps_pairs`；`:194-202` `HOL_basic_ss` 的设置。先做 `Variable.gen_all` 的还有 `FOL/simpdata.ML:53`、`ZF/pair.thy:15`、`ZF/ZF.thy:70`、`ZF/OrdQuant.thy:354`、`Sequents/simpdata.ML:75`。
- `HOL/HOL.thy:1447`：`lemmas [cong] = imp_cong simp_implies_cong`。
- 设置槽位的地方（Isabelle 发行版里含 `set_mksimps` 的文件共 18 个，其中 2 个是 Pure 自己的定义）：加 connective 的 `HOL/Set.thy:396-402`、`HOL/Nominal/Nominal.thy:392-396`；逐条后处理的 `HOL/HOL.thy:1609-1611`（Induct 的 simpset，从 `empty_ss` 起步）；从 `empty_simpset` 起步的 `HOL/Tools/lin_arith.ML:108-110`、`HOL/Tools/Quotient/quotient_tacs.ML:36-38`、`HOL/Tools/Function/function_elims.ML:47-48`、`Provers/hypsubst.ML:148`，从 `empty_ss` 起步的 `HOL/Prolog/prolog.ML:63-65`；包一层的 `HOL/Imperative_HOL/ex/Congproc_Ex.thy:491-507`；以及 FOL、ZF、Sequents 各自的设置。
- `mksimps` 的调用者：`Pure/Tools/find_theorems.ML:213`、`HOL/Library/rewrite.ML:61`、`Tools/eqsubst.ML:55`、`Tools/Code/code_runtime.ML:350`。

AFP（`contrib/afp-2026-10-26/thys`）：

- AutoCorres2 `c-parser/UMM_Proofs.ML`：`is_positive` `:128-131`，`derive_bounds` `:134-173`（成对查找在 `:162`），`add_array_bound_mksimps` `:176-184`，`set_array_bound_mksimps` `:186-189`。装在 `l2_opt.ML:870-872`（`basic_ss`）和 `Polish.thy:912-914` 的 attribute `array_bound_mksimps` 上。用到的 lemma：`doc/open_struct.thy:1303-1306`。经公开函数的入口：`l2_opt.ML:322`、`Polish.thy:1730-1747`（`gen_mksimps`，`:1743` 调 `Simplifier.mksimps`）。
- AutoCorres2 `in_out_parameters.ML:2060-2070`（`add_mk_disjoint_global_simps`）、`:2231-2243`（`add_derived_rel_alloc_mksimps`、`set_derived_rel_alloc_mksimps`）；`lib/ml-helpers/Tuple_Tools.thy:757-767`（用于 `doc/AutoCorresInfrastructure.thy:510`、`:533`）；`c-parser/cached_theory_simproc.ML:69-72`（从 `empty_simpset`）。
- 加 connective 的：`Transport/HOL_Basics/Predicates/Bounded_Quantifiers.thy:101-108`、`Nominal2/Nominal2_Base.thy:2294-2300`、`Zippy/Zippy/Instances/Zip/Examples/Benchmarks/Set.thy:390-399`。

本项目：

- phi-system `Phi_Logic_Programming_Reasoner/library/reasoners.ML`：`is_syntactic_premise_mode` `:523-527`，`extract_prems` `:578-601`，`gen_simplify` `:608-617`。`library/tools/simplification_protect.ML:13-25`，`library/tools/simpset.ML:42-45`（`Empty_SS`）。
- theory hash 的输入：`MLML/contrib/Performant_Isabelle_ML/library/theory_hash.ML:180-190`。

调查（Opus agent，2026-11-17）搜过的范围与命令：AFP 全部、发行版全部、`MLML/contrib/` 下本项目的代码（不含 Isabelle 与 AFP 的各版本副本，不含 ICSE27）；模式 `set_mksimps`、`set_mksimps_context`、`get_mksimps_context`、`mksimps_pairs`、`mk_atomize`、`Simpdata.mksimps`、`setmksimps`、`mksimps`，以及 Simplifier 的别名；用 `/usr/bin/grep -rnI`。AFP 里 820 处 `mk_eq`、82 处 `mk_meta_eq` 是调用，不是装槽位，没有逐个看。

实测：

- 【concept 会话 2026-11-17，stock Isabelle2026，探针 `MLML/ai-artifacts/concept_unary_partition_A_probes/Destruct_Timing_Probe.thy`】每次运行：用 `OF` destruct 4 个子句 9.71 微秒；对这 4 个结果做改写，小 simpset 42.36 微秒、固定规则 47.05 微秒；一次用户级的小 `simp` 146.78 微秒。这是使用者一侧的数字。本 feature 自己的开销没有测过（第 6 节第 17 条）。
- 【2026-11-17，探针 `ai-artifacts/probes/Slot_Input_Probe.thy`，不提交】HOL 把 `P ∧ Q`、`∀i. …`、`A ⟶ B`、`∀x∈S. …` 这些前提整条交给槽位；结果表在 4.5。
- 【2026-11-17，探针 `ai-artifacts/probes/Premise_Visibility_Probe.thy`，不提交】乱序与顺序模式下，收前提时写进上下文的东西在哪里看得见；结果表在 4.4。

- 【2026-11-17，探针 `ai-artifacts/probes/Rereview_Checks_Probe.thy`，不提交】复审 N1：假设 `P a ∧ R b` 的定理 maxidx 为 −1，`RS conjunct1`、`RS conjunct2` 得到的 `P a`、`R b` 记着的 maxidx 为 0，`Thm.adjust_maxidx_thm ~1` 后为 −1。复审 N2：`\<^prop>‹finite ?A›` 报 "Unbound schematic variable"；`\<^prop>‹finite A›` 的类型变量是 `TFree 'a`，匹配 `finite (S :: nat set)` 为 `false`；用 `Variable.add_fixes_implicit`、`Variable.declare_term`、`Variable.export_terms` 一般化后是 `finite (?A :: ?'a set)`，与 `Simplifier.make_simproc` 存下的 pattern 相同，匹配为 `true`。

复审引用、我核对过的位置：`Pure/raw_simplifier.ML:1553`（先 `adjust_maxidx_thm` 后 `gen_all`）；`Pure/simplifier.ML:116-123`（`make_simproc`）；`Pure/Isar/proof_context.ML:578-581`（`augment`）；`Pure/variable.ML:487`（`add_fixes_implicit`）；`Pure/context.ML:791`（theory 数据按 parent 顺序从左往右合并）；`HOL/Tools/simpdata.ML:130`、`:148`（HOL 的 solver 用 `prems_of`）。

未实测，只读了源码：4.5 "stock HOL 自己产出的规则不变"（由第 6 节第 7 条确认）；4.5 里 AutoCorres2、phi-system 受到的影响；4.4 里"用了会报 Undeclared hyps"（由第 6 节第 2 条确认）。

## 11. 开工须知（压缩前写，2026-11-17 16:00 UTC）

**作者的命令。** 复审通过、rev 3 写完后，我曾自行开工（只读了 `raw_simplifier.ML`，没改任何文件），作者叫停：「等一下！我批准你开工了吗？」。随后作者问清进度，说「很好，建议准备 compact 后再开工」。所以：**压缩之后开工实现**。开工不等于可以构建或提交：

- 构建（任何 session、任何参数）要作者明令；`isabelle REPL`、isabelle-mcp 跑的是共享树，测不到私有树的改动（SKILL `isabelle-patch-feature` 第 2 节），所以改动只能靠作者下令的私有树构建来验证。
- 提交要作者下令；feature 仓库里新增的文件（`tests/`、`init.sh`、`tools/*.txt`、`.gitattributes`、README）每个都要作者批准后才能提交。只推 origin。
- 只改私有树 `contrib/generic_mksimps/worktrees/Isabelle2026-generic_mksimps`；共享树 `contrib/Isabelle2026` 和 stock 树只读。
- 计划文件只手工改，改设计要作者批准。

**改哪里。**

- `src/Pure/raw_simplifier.ML`（第 5 节表格）。它在 Pure 引导阶段编译（`Pure/ROOT.ML:204`），早于 `ML/ml_antiquotations.ML`（`:255`），**不能用 antiquotation**（只认 `\<^here>`、`@{make_string}`）；常量名等要写成字面构造子。需要的 `Net`、`Pattern`、`Variable`、`Sign`、`Thm`、`sort_distinct` 都已在它之前加载；`Proof_Context` 还没有（4.2 的一般化因此用 `Variable` 的三步，不用 `Proof_Context.augment`）。
- `src/Pure/simplifier.ML`：只动 `pretty_simpset`。
- `src/HOL/Tools/simpdata.ML`：四个处理器，与 `mk_atomize` 共用 destruct 的那段代码（4.5）。
- 测试 session 放在 feature 仓库的 `tests/`，照 `contrib/default_fact_qualifiers/tests`（`ROOT` 加一个 `.thy`）；打包文件照 `contrib/default_fact_qualifiers/tools`（`license.txt`、`patched_files.txt`、`release_build.sh`、`required_sessions.txt`、`signature_additions.txt`）。
- Isabelle/ML 写法照 `.claude/skills/isabelle-ML` 和 `isabelle-ml-style`；注释简短，但 4.6 列出的九条陷阱必须写进 signature 注释（作者第九批）。

**建议的顺序。** (1) Pure：`mk_rews` 加表、`empty_ss`、`map_mk_rews`、`merge_ss`、`clear_simpset`、分派 `mksimps_context`、`extract_rews` 与 `mksimps`、4.6 的接口与注释、`dest_ss`；(2) `pretty_simpset`；(3) HOL 的四个处理器；(4) 测试 session；(5) 打包文件；(6) 自查后向作者报告，请求构建的命令（Pure、HOL、测试 session）；(7) 构建通过后做变异检查（第 6 节第 19 条，变异作用于测试本身）和代码评审。

**还在等的。**

- concept A1 会话（`uds:/run/user/1002/cc-socks/2054725.sock`）2026-11-17 回复：已收到 4.8，没有疑问；已在 concept 计划 5.3、5.6 和类型层计划里记下 `kept_by_clear_simpset`、concept 的处理器填 `true`；mask 与嵌套化简转给了 concept B（intro table 和 concept_fact 的搜索归它）；作者定了 concept 的 A 区原型等本 feature 的代码完成再开工；concept 改 base 要作者下令，3.7 第 1 步的检查已核过（两个分支都在 `c105fb8`）。**本 feature 可用时要通知 concept A1。**
- 我向作者提议记一条 memory（"作者说 X 之后才能做 Y，是给 Y 设前提，不是授权 Y"），作者否决，不写。
- feature 仓库的注册提交、MLML 子模块登记，都等作者下令。

**评审记录的位置**（不进任何仓库）：第一轮 `~/.claude/projects/-home-qiyuan-Current-MLML/702220e8-76dc-48eb-8e92-e9c22095d5fd/subagents/workflows/wf_b79ec858-d78/journal.jsonl`，复审同目录下 `wf_7feff49e-d01/journal.jsonl`。探针在 `ai-artifacts/probes/`，不提交。
