theory TM
  imports Main "Supplementary/Misc" "Supplementary/Lists"
    "Intro_Dest_Elim.IHOL_IDE" "HOL-Library.Countable_Set"
begin

class blank =
  fixes Bk :: 'a

instantiation nat :: blank begin
definition Bk_nat :: nat where "Bk_nat = 0"
instance ..
end

instantiation option :: (type) blank begin
definition "Bk_option \<equiv> None"
instance ..
end

type_synonym 'b lang = "'b list set"

datatype 'b action = L | R | W 'b | Nop

fun symbol_of_write :: "'b action \<Rightarrow> 'b::blank" where
  "symbol_of_write (W w) = w" | "symbol_of_write _ = Bk"

lemma symbol_of_write_def: "symbol_of_write a = (case a of W w \<Rightarrow> w | _ \<Rightarrow> Bk)"
  by (induction a) auto

fun action_app :: "('b1 \<Rightarrow> 'b2) \<Rightarrow> 'b1 action \<Rightarrow> 'b2 action" where
  "action_app _ L = L"
| "action_app _ R = R"
| "action_app f (W x) = W (f x)"
| "action_app _ Nop = Nop"

lemma symbol_action_app[simp]:
  assumes "g Bk = Bk"
  shows "symbol_of_write ` action_app g ` A \<subseteq> g ` symbol_of_write ` A"
proof -
  from assms have "symbol_of_write (action_app g a) = g (symbol_of_write a)" for a::"'b action"
    by (cases a) simp_all
  then show ?thesis by auto
qed

record 'b tape =
  left :: "'b list"
  middle :: 'b
  right :: "'b list"

fun tape_app :: "('b1 \<Rightarrow> 'b2) \<Rightarrow> 'b1 tape \<Rightarrow> 'b2 tape" where
  "tape_app f \<lparr> left = l, middle = m, right = r \<rparr> = \<lparr> left = map f l, middle = f m, right = map f r \<rparr>"

abbreviation "empty_tape \<equiv> \<lparr> left=[], middle = Bk, right=[] \<rparr>"

definition [simp]: "set_of_tape tp \<equiv> set (left tp) \<union> {middle tp} \<union> set (right tp) \<union> {Bk}"

lemma set_of_tape_helpers: "middle tp \<in> set_of_tape tp" "Bk \<in> set_of_tape tp" by auto

text\<open>TM execution begins with the head at the start of the input word.\<close>
fun input_tape ("<_>\<^sub>t\<^sub>p") where
  "<[]>\<^sub>t\<^sub>p = empty_tape"
| "<x # xs>\<^sub>t\<^sub>p = \<lparr> left=[], middle = x, right = xs \<rparr>"

lemma input_tape_def:
  "<w>\<^sub>t\<^sub>p = (if w = [] then empty_tape else \<lparr> left=[], middle = hd w, right = tl w \<rparr>)"
  by (induction w) auto

abbreviation tp_size :: "'b tape \<Rightarrow> nat" where
  "tp_size tp \<equiv> length (left tp) + length (right tp) + 1"

fun tp_update :: "('b::blank) action \<Rightarrow> 'b tape \<Rightarrow> 'b tape" where
  "tp_update L \<lparr>left=[],   middle = m, right=rs  \<rparr> = \<lparr>left=[],   middle = Bk, right=m#rs \<rparr>"
| "tp_update L \<lparr>left=l#ls, middle = m, right=rs  \<rparr> = \<lparr>left=ls,   middle = l,  right=m#rs \<rparr>"
| "tp_update R \<lparr>left=ls,   middle = m, right=[]  \<rparr> = \<lparr>left=m#ls, middle = Bk, right=[]   \<rparr>"
| "tp_update R \<lparr>left=ls,   middle = m, right=r#rs\<rparr> = \<lparr>left=m#ls, middle = r,  right=rs   \<rparr>"
| "tp_update (W w) tp = tp\<lparr> middle := w \<rparr>"
| "tp_update Nop tp = tp"

lemma tp_update_set: "set_of_tape (tp_update a tp) \<subseteq> set_of_tape tp \<union> {symbol_of_write a}"
proof -
  obtain l m r where expand_tp: "tp = \<lparr>left=l, middle=m, right=r\<rparr>" by (rule tape.cases)
  show ?thesis unfolding expand_tp
  proof (induction a)
    case L show ?case by (induction l) auto next
    case R show ?case by (induction r) auto next
    case (W x) show ?case by (induction r) auto
  qed simp
qed

abbreviation "tp_read \<equiv> middle"


record ('a, 'b) TM =
  tape_count :: nat

  states       :: "'a set"
  start_state  :: 'a
  final_states :: "'a set"
  accepting_states :: "'a set"

  symbols :: "'b set"

  next_state  :: "'a \<Rightarrow> 'b list \<Rightarrow> 'a"
  next_action :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b action list"

record ('a, 'b) TM_config =
  state :: 'a
  tapes :: "'b tape list"


locale pre_TM =
  fixes M :: "('a, 'b::blank) TM" (structure)
begin

abbreviation "wf_word w \<equiv> set w \<subseteq> symbols M"

abbreviation "wf_words \<equiv> {w. wf_word w}"

abbreviation "wf_lang X \<equiv> X \<subseteq> wf_words"

\<comment> \<open>A state \<open>q\<close> in combination with a vector \<open>w\<close> (\<^typ>\<open>'b list\<close>) of symbols currently under the TM-heads,
  is considered a well-formed state w.r.t. a \<^typ>\<open>('a, 'b) TM\<close> \<open>M\<close>, iff
  \<open>q\<close> is a valid state for \<open>M\<close>,
  the number of elements of \<open>w\<close> matches the number of tapes of \<open>M\<close>, and
  all elements of \<open>w\<close> are valid symbols for \<open>M\<close> (members of \<open>M\<close>'s tape alphabet).\<close>
definition wf_state :: "'a \<Rightarrow> 'b list \<Rightarrow> bool" where
  "wf_state q w \<equiv> q \<in> states M \<and> length w = tape_count M \<and> wf_word w"

mk_ide wf_state_def |intro wf_stateI[intro]| |elim wf_stateE[elim]| |dest wf_stateD[dest]|

\<comment> \<open>A \<^typ>\<open>('a, 'b) TM_config\<close> \<open>c\<close> is considered well-formed w.r.t. a \<^typ>\<open>('a, 'b) TM\<close> \<open>M\<close>, iff
  the \<^const>\<open>state\<close> of \<open>c\<close> is valid for \<open>M\<close>,
  the number of \<^const>\<open>tapes\<close> of \<open>c\<close> matches the number of tapes of \<open>M\<close>, and
  all symbols on all \<^const>\<open>tapes\<close> of \<open>c\<close> are valid symbols for \<open>M\<close>.\<close>
definition wf_config :: "('a, 'b) TM_config \<Rightarrow> bool" where
  "wf_config c \<equiv> let q = state c; tps = tapes c in
        q \<in> states M
      \<and> length tps = tape_count M
      \<and> list_all (\<lambda>tp. set_of_tape tp \<subseteq> symbols M) tps"

mk_ide wf_config_def[unfolded list_all_iff Let_def]
  |intro wf_configI[intro]| |elim wf_configE[elim]| |dest wf_configD[dest]|

lemma wf_configD'[dest]:
  "wf_config c \<Longrightarrow> list_all (\<lambda>tp. set_of_tape tp \<subseteq> symbols M) (tapes c)"
  unfolding list_all_iff by blast

end \<comment> \<open>\<^locale>\<open>pre_TM\<close>\<close>

locale TM = pre_TM +
  assumes at_least_one_tape: "1 \<le> tape_count M"
  and state_axioms: "finite (states M)" "start_state M \<in> states M"
                    "final_states M \<subseteq> states M" "accepting_states M \<subseteq> final_states M"
  and symbol_axioms: "finite (symbols M)" "Bk \<in> (symbols M)"
  and next_state: "\<And>q w. wf_state q w \<Longrightarrow> next_state M q w \<in> states M"
  and next_action_length: "\<And>q w. wf_state q w \<Longrightarrow>
                                 length (next_action M q w) = tape_count M"
  and next_write_symbol: "\<And>q w. wf_state q w \<Longrightarrow>
                                 symbol_of_write ` set (next_action M q w) \<subseteq> symbols M"
  and final_state: "\<And>q w. wf_state q w \<Longrightarrow> q \<in> final_states M \<Longrightarrow>
                          next_state M q w = q"
  and final_action: "\<And>q w. wf_state q w \<Longrightarrow> q \<in> final_states M \<Longrightarrow>
                           set (next_action M q w) \<subseteq> {Nop}"
begin

abbreviation wf_state_of_config ("wf'_state\<^sub>c")
  where "wf_state\<^sub>c c \<equiv> wf_state (state c) (map tp_read (tapes c))"

lemma wf_config_state: "wf_config c \<Longrightarrow> wf_state\<^sub>c c"
  by (intro wf_stateI) (blast, force, use set_of_tape_helpers in fast)

corollary wf_state_tape_count: "wf_state\<^sub>c c \<Longrightarrow> length (tapes c) = tape_count M"
  unfolding wf_state_def by simp

abbreviation is_final :: "('a, 'b) TM_config \<Rightarrow> bool" where
  "is_final c \<equiv> state c \<in> final_states M"

definition step :: "('a, 'b) TM_config \<Rightarrow> ('a, 'b) TM_config" where
  "step c = (let q=state c; w=map tp_read (tapes c) in \<lparr>
      state=next_state M q w,
      tapes=map2 tp_update (next_action M q w) (tapes c)
   \<rparr>)"

abbreviation all_Nop ("Nop\<^sub>k") where "Nop\<^sub>k \<equiv> Nop \<up> (tape_count M)"


corollary all_Nop_update[simp]: "length ts = tape_count M \<Longrightarrow> map2 tp_update Nop\<^sub>k ts = ts"
  unfolding map2_replicate by (simp add: map_idI)

lemma final_action_explicit:
  "\<lbrakk>wf_state q w; q \<in> final_states M\<rbrakk> \<Longrightarrow> next_action M q w = Nop\<^sub>k"
  using next_action_length final_action by (intro replicate_eqI) blast+

lemma final_step_fixpoint:
  assumes wf: "wf_state\<^sub>c c" and fc: "is_final c"
  shows "step c = c"
proof -
  let ?q = "state c" and ?w = "map tp_read (tapes c)" and ?ts = "tapes c"

  have ns: "next_state M ?q ?w = ?q" using wf fc by (rule final_state)
  have na: "next_action M ?q ?w = Nop\<^sub>k" using wf fc by (rule final_action_explicit)
  have tu: "map2 tp_update Nop\<^sub>k ?ts = ?ts" using all_Nop_update wf_state_tape_count wf .

  show "step c = c" unfolding step_def Let_def unfolding ns na tu by simp
qed

lemma final_steps: "wf_state\<^sub>c c \<Longrightarrow> is_final c \<Longrightarrow> (step^^n) c = c"
  by (intro funpow_fixpoint final_step_fixpoint)

lemma wf_config_step: "wf_config c \<Longrightarrow> wf_config (step c)"
proof
  let ?q = "state c" and ?w = "map tp_read (tapes c)" and ?ts = "tapes c"
  let ?q' = "state (step c)" and ?ts' = "tapes (step c)"
  let ?na = "next_action M ?q ?w"
  assume "wf_config c"
  then have wf: "wf_state\<^sub>c c" by (rule wf_config_state)

  from \<open>wf_config c\<close> have "?q \<in> states M" ..
  have q': "?q' = next_state M ?q ?w" unfolding step_def Let_def by simp
  show "?q' \<in> states M" unfolding q' using wf by (rule next_state)

  have lna: "length ?na = tape_count M" using wf by (rule next_action_length)
  moreover have lts: "length ?ts = tape_count M" using \<open>wf_config c\<close> ..
  ultimately show lts': "length ?ts' = tape_count M" unfolding step_def Let_def by simp

  have "\<forall>i < length ?ts'. set_of_tape (?ts' ! i) \<subseteq> symbols M" unfolding lts'
  proof (intro allI impI)
    fix i assume "i < tape_count M"
    have *: "?ts' ! i = tp_update (?na ! i) (?ts ! i)" unfolding step_def Let_def TM_config.simps(2)
      using lna lts \<open>i < tape_count M\<close> by (intro nth_map2) auto

    have "set_of_tape (?ts' ! i) \<subseteq> set_of_tape (?ts ! i) \<union> {symbol_of_write (?na ! i)}"
      unfolding * by (rule tp_update_set)
    also have "... \<subseteq> symbols M"
    proof (intro Un_least)
      have "i < length ?ts" unfolding lts by (fact \<open>i < tape_count M\<close>)
      moreover from \<open>wf_config c\<close> have "\<forall>tp \<in> set ?ts. set_of_tape tp \<subseteq> symbols M" ..
      ultimately show "set_of_tape (?ts ! i) \<subseteq> symbols M" by (rule list_ball_nth)

      have "i < length ?na" unfolding lna by (fact \<open>i < tape_count M\<close>)
      moreover have "\<forall>tp \<in> set ?na. symbol_of_write tp \<in> symbols M"
        using next_write_symbol \<open>wf_state\<^sub>c c\<close> unfolding image_subset_iff .
      ultimately show "{symbol_of_write (?na ! i)} \<subseteq> symbols M" by (intro list_ball_nth) blast+
    qed
    finally show "set_of_tape (?ts' ! i) \<subseteq> symbols M" .
  qed
  then show "\<forall>tp \<in> set ?ts'. set_of_tape tp \<subseteq> symbols M" unfolding all_set_conv_all_nth .
qed

corollary wf_config_steps: "wf_config c \<Longrightarrow> wf_config ((step^^n) c)"
  using wf_config_step by (induction n) auto


definition start_config :: "'b list \<Rightarrow> ('a, 'b) TM_config" where [simp]:
  "start_config w = \<lparr>
    state = start_state M,
    tapes = <w>\<^sub>t\<^sub>p # empty_tape \<up> (tape_count M - 1)
  \<rparr>"

abbreviation "run n w \<equiv> (step^^n) (start_config w)"

lemma words_length_finite[simp]: "finite {w\<in>wf_words. length w \<le> n}"
  using symbol_axioms(1) finite_lists_length_le[of "symbols M"] by simp

lemma set_of_wf_word: "wf_word w \<Longrightarrow> set_of_tape <w>\<^sub>t\<^sub>p \<subseteq> symbols M"
  using symbol_axioms(2) by (induction w) auto

lemma wf_start_config: "wf_word w \<Longrightarrow> wf_config (start_config w)"
proof
  let ?ts = "tapes (start_config w)"
  show "state (start_config w) \<in> states M" using state_axioms(2) by simp
  show "length ?ts = tape_count M" using at_least_one_tape by simp

  assume "set w \<subseteq> symbols M"
  have "set ?ts \<subseteq> {<w>\<^sub>t\<^sub>p} \<union> {empty_tape}" by fastforce
  moreover have "set_of_tape empty_tape \<subseteq> symbols M" using symbol_axioms(2) by simp
  moreover have "set_of_tape <w>\<^sub>t\<^sub>p \<subseteq> symbols M" using \<open>set w \<subseteq> symbols M\<close> by (fact set_of_wf_word)
  ultimately show "\<forall>tp \<in> set ?ts. set_of_tape tp \<subseteq> symbols M" by blast
qed

corollary wf_config_run: "wf_word w \<Longrightarrow> wf_config (run n w)"
  using wf_start_config by (rule wf_config_steps)

lemma final_le_steps:
  assumes "wf_config c"
      and "is_final ((step^^n) c)"
      and "n \<le> m"
    shows "(step^^m) c = (step^^n) c"
proof -
  from \<open>n\<le>m\<close> obtain n' where "m = n' + n" by (metis add.commute less_eqE)
  have wf: "wf_state\<^sub>c ((step^^n) c)" using wf_config_state wf_config_steps \<open>wf_config c\<close> .
  have "(step^^m) c = (step^^n') ((step^^n) c)"
    unfolding \<open>m = n' + n\<close> funpow_add by (rule comp_apply)
  also have "... = (step^^n) c" using wf assms(2) by (rule final_steps)
  finally show "(step^^m) c = (step^^n) c" .
qed

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>

subsection \<open>Composition of Turing Machines\<close>

\<comment> \<open>Let M1 be a k1-tape TM, M2 a k2-tape TM. We define the composition of M1 and M2
    as a (k1+k2-1)-tape TM. First M1 operates on the tapes 0,1,...,k1-1.
    When M1 finishes, M2 operates on the tapes 0,k1,k1+1,...,k1+k2-2.
    Therefore, M1 is expected to write its output (M2's input) on the zeroth tape.\<close>

fun tm_comp :: "('a1, 'b::blank) TM \<Rightarrow> ('a2, 'b) TM \<Rightarrow> ('a1+'a2, 'b) TM" ("_ |+| _" [0, 0] 100)
  where "tm_comp M1 M2 = (let k = tape_count M1 + tape_count M2 - 1 in \<lparr>
    tape_count = k,
    states = states M1 <+> states M2,
    start_state = Inl (start_state M1),
    final_states = Inr`final_states M2,
    accepting_states = Inr`accepting_states M2,
    symbols = symbols M1 \<union> symbols M2,
    next_state = (\<lambda>q w. case q of
                        Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                  let q' = next_state M1 q1 w1 in
                                  if q' \<in> final_states M1
                                    then Inr (start_state M2)
                                    else Inl q'
                      | Inr q2 \<Rightarrow> let w2 = nths w (insert 0 {tape_count M1..<k}) in
                                  Inr (next_state M2 q2 w2)
                 ),
    next_action = (\<lambda>q w. case q of
                         Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                   pad k Nop (next_action M1 q1 w1)
                       | Inr q2 \<Rightarrow> let w2 = nths w (insert 0 {tape_count M1..<k}) in
                                   let a2 = next_action M2 q2 w2 in
                                   hd a2 # Nop \<up> (tape_count M1 - 1) @ tl a2
                        )
  \<rparr>)"

lemma wf_tm_comp: "TM M1 \<Longrightarrow> TM M2 \<Longrightarrow> TM (M1 |+| M2)"
  sorry

hide_const (open) "TM.action.L" "TM.action.R" "TM.action.W"

subsection \<open>Hoare Rules\<close>

type_synonym ('a, 'b) assert = "('a, 'b) TM_config \<Rightarrow> bool"

definition (in TM) hoare_halt :: "('a, 'b) assert \<Rightarrow> ('a, 'b) assert \<Rightarrow> bool" where
  "hoare_halt P Q \<longleftrightarrow> (\<forall>c. wf_config c \<longrightarrow> P c \<longrightarrow>
    (\<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn))"

context TM begin
lemma hoare_haltI[intro]:
  fixes P Q
  assumes "\<And>c. wf_config c \<Longrightarrow> P c \<Longrightarrow>
             \<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn"
  shows "hoare_halt P Q"
  unfolding hoare_halt_def using assms by blast

lemma hoare_haltE[elim]:
  fixes c
  assumes "wf_config c" "P c"
      and "hoare_halt P Q"
    obtains n where "is_final ((step^^n) c)" and "Q ((step^^n) c)"
  using assms
  unfolding hoare_halt_def by meson

lemma hoare_contr:
  fixes P and c
  assumes "wf_config c" "P c" "hoare_halt P (\<lambda>_. False)"
  shows "False"
using assms by (rule hoare_haltE)

lemma hoare_true: "hoare_halt P Q \<Longrightarrow> hoare_halt P (\<lambda>_. True)"
  unfolding hoare_halt_def by metis

lemma hoare_and[intro]:
  assumes h1: "hoare_halt P Q1"
    and h2: "hoare_halt P Q2"
  shows "hoare_halt P (\<lambda>c. Q1 c \<and> Q2 c)"
proof
  fix c assume "P c" and wf: "wf_config c"
  from wf \<open>P c\<close> h1 obtain n1 where fn1: "is_final ((step^^n1) c)" and q1: "Q1 ((step^^n1) c)"
    by (rule hoare_haltE)
  from wf \<open>P c\<close> h2 obtain n2 where fn2: "is_final ((step^^n2) c)" and q2: "Q2 ((step^^n2) c)"
    by (rule hoare_haltE)

  define n::nat where "n \<equiv> max n1 n2"
  hence "n1 \<le> n" "n2 \<le> n" by simp+

  from wf fn1 \<open>n1 \<le> n\<close> have steps1: "((step^^n) c) = ((step^^n1) c)" by (rule final_le_steps)
  from wf fn2 \<open>n2 \<le> n\<close> have steps2: "((step^^n) c) = ((step^^n2) c)" by (rule final_le_steps)
  from fn1 q1 q2 have "let qn=(step^^n) c in is_final qn \<and> Q1 qn \<and> Q2 qn"
    by (fold steps1 steps2) simp
  thus "\<exists>n. let cn = (step ^^ n) c in is_final cn \<and> Q1 cn \<and> Q2 cn" ..
qed

abbreviation init where "init w \<equiv> (\<lambda>c. c = start_config w)"

definition halts :: "'b list \<Rightarrow> bool"
  where "halts w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>_. True)"

lemma halts_I[intro]: "wf_word w \<Longrightarrow> \<exists>n. is_final (run n w) \<Longrightarrow> halts w"
  unfolding halts_def hoare_halt_def by simp

lemma halts_E[elim]:
  assumes "halts w"
  shows "wf_word w"
    and "\<exists>n. is_final (run n w)"
  using assms hoare_halt_def wf_start_config
  unfolding halts_def by fastforce+

lemma hoare_halt_neg:
  assumes "\<not> hoare_halt (init w) Q"
    and "halts w"
  shows "hoare_halt (init w) (\<lambda>tp. \<not> Q tp)"
  using assms unfolding hoare_halt_def halts_def Let_def unfolding wf_config_def by fast

lemma halt_inj:
  assumes "wf_word w"
      and "hoare_halt (init w) (\<lambda>c. f c = x)"
      and "hoare_halt (init w) (\<lambda>c. f c = y)"
    shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have *: "a = x \<and> a = y \<longleftrightarrow> False" for a by blast

  from hoare_and assms(2-3) have "hoare_halt (init w) (\<lambda>c. f c = x \<and> f c = y)".
  then have "hoare_halt (init w) (\<lambda>_. False)" unfolding * .
  thus False using hoare_contr wf_start_config[OF assms(1)] by fastforce
qed

end

abbreviation "tps_word c \<equiv> let tp = hd (tapes c) in left tp @ right tp"
abbreviation "input_assert (P::'b list \<Rightarrow> bool) \<equiv> \<lambda>c::('a, 'b) TM_config. P (tps_word c)"

lemma hoare_comp:
  fixes M1 :: "('a1, 'b::blank) TM" and M2 :: "('a2, 'b) TM"
    and Q :: "'b list \<Rightarrow> bool"
  assumes "TM.hoare_halt M1 (input_assert P) (input_assert Q)"
      and "TM.hoare_halt M2 (input_assert Q) (input_assert S)"
    shows "TM.hoare_halt (M1 |+| M2) (input_assert P) (input_assert S)"
sorry

subsection\<open>Deciding Languages\<close>

abbreviation input where "input w \<equiv> (\<lambda>c. hd (tapes c) = <w>\<^sub>t\<^sub>p)"

context TM begin

lemma init_input: "init w c \<Longrightarrow> input w c"
  unfolding start_config_def by simp

lemma init_state_start_state: "init w c \<Longrightarrow> state c = start_state M"
  unfolding start_config_def by simp

definition accepts :: "'b list \<Rightarrow> bool"
  where "accepts w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M)"

lemma acceptsI[intro]:
  assumes "wf_word w"
    and "state (run n w) \<in> accepting_states M"
  shows "accepts w"
  using assms unfolding accepts_def hoare_halt_def
  by (meson state_axioms(4) subsetD)

definition rejects :: "'b list \<Rightarrow> bool"
  where "rejects w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<notin> accepting_states M)"

lemma rejectsI[intro]:
  assumes "wf_word w"
    and "is_final (run n w)"
    and "state (run n w) \<notin> accepting_states M"
  shows "rejects w"
  using assms unfolding rejects_def hoare_halt_def
  by meson

lemma halts_iff: "halts w \<longleftrightarrow> accepts w \<or> rejects w"
proof (intro iffI)
  assume "halts w"
  then obtain n where fin: "is_final (run n w)" and wf: "wf_word w"
    using halts_E by blast
  thus "accepts w \<or> rejects w"
  proof (cases "state (run n w) \<in> accepting_states M")
    case True hence "accepts w"
      using fin wf acceptsI by blast
  next
    case False hence "rejects w"
      using fin wf rejectsI by blast
  qed blast+
next
  assume "accepts w \<or> rejects w" thus "halts w"
  unfolding accepts_def rejects_def halts_def using hoare_true by blast
qed

lemma acc_not_rej:
  assumes "accepts w"
  shows "\<not> rejects w"
proof (intro notI)
  assume "rejects w"
  let ?acc = "accepting_states M"

  have "hoare_halt (init w) (\<lambda>c. state c \<in> ?acc)"
    using \<open>accepts w\<close> unfolding accepts_def by (rule conjunct2)
  moreover have "hoare_halt (init w) (\<lambda>c. state c \<notin> ?acc)"
    using \<open>rejects w\<close> unfolding rejects_def by (rule conjunct2)
  ultimately have "hoare_halt (init w) (\<lambda>c. state c \<in> ?acc \<and> state c \<notin> ?acc)" by (fact hoare_and)
  then have "hoare_halt (init w) (\<lambda>c. False)" by presburger

  moreover from assms have "wf_config (start_config w)"
    unfolding accepts_def by (intro wf_start_config) blast
  moreover have "init w (start_config w)" ..
  ultimately show False by (intro hoare_contr)
qed

lemma rejects_altdef:
  "rejects w = (halts w \<and> \<not> accepts w)"
  using acc_not_rej halts_iff by blast

definition decides_word :: "'b lang \<Rightarrow> 'b list \<Rightarrow> bool"
  where decides_def[simp]: "decides_word L w \<equiv> (w \<in> L \<longleftrightarrow> accepts w) \<and> (w \<notin> L \<longleftrightarrow> rejects w)"

abbreviation decides :: "'b lang \<Rightarrow> bool"
  where "decides L \<equiv> \<forall>w\<in>wf_words. decides_word L w"

lemma decides_halts: "decides_word L w \<Longrightarrow> halts w"
  by (cases "w \<in> L") (simp add: halts_iff)+

corollary decides_halts_all: "decides L \<Longrightarrow> \<forall>w\<in>wf_words. halts w"
  using decides_halts by blast

lemma decides_altdef:
  "decides_word L w \<longleftrightarrow> halts w \<and> (w \<in> L \<longleftrightarrow> accepts w)"
proof (intro iffI)
  fix w
  assume "decides_word L w"
  hence "halts w" by (rule decides_halts)
  moreover have "w \<in> L \<longleftrightarrow> accepts w" using \<open>decides_word L w\<close> by simp
  ultimately show "halts w \<and> (w \<in> L \<longleftrightarrow> accepts w)" ..
next
  assume "halts w \<and> (w \<in> L \<longleftrightarrow> accepts w)"
  then show "decides_word L w" by (simp add: rejects_altdef)
qed

lemma decides_altdef3: "decides_word L w \<longleftrightarrow> hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M \<longleftrightarrow> w\<in>L)"
  sorry

lemma decides_altdef4: "decides_word L w \<longleftrightarrow> (if w \<in> L then accepts w else rejects w)"
  unfolding decides_def using acc_not_rej by (cases "w \<in> L") auto

end

subsubsection\<open>TM Languages\<close>

definition TM_lang :: "('a, 'b::blank) TM \<Rightarrow> 'b lang" ("L'(_')")
  where "L(M) \<equiv> if (\<forall>w\<in>pre_TM.wf_words M. TM.halts M w)
                then {w\<in>pre_TM.wf_words M. TM.accepts M w}
                else undefined"

context TM begin

lemma decides_TM_lang_accepts: "(\<And>w. wf_word w \<Longrightarrow> halts w) \<Longrightarrow> decides {w. accepts w}"
  unfolding decides_def rejects_altdef mem_Collect_eq by blast

lemma decides_TM_lang: "(\<And>w. wf_word w \<Longrightarrow> halts w) \<Longrightarrow> decides L(M)"
  unfolding TM_lang_def using decides_TM_lang_accepts by simp

lemma decidesE: "wf_lang L \<Longrightarrow> decides L \<Longrightarrow> L(M) = L"
proof safe
  assume wfl: \<open>wf_lang L\<close> and dec: \<open>decides L\<close>
  from dec have "\<forall>w\<in>wf_words. halts w" by (rule decides_halts_all)
  then have L_M: "L(M) = {w\<in>wf_words. accepts w}" unfolding TM_lang_def by presburger

  fix w
  show "w \<in> L(M)" if "w \<in> L" proof -
    from \<open>w\<in>L\<close> wfl have "wf_word w" by blast
    moreover from \<open>w\<in>L\<close> \<open>wf_word w\<close> \<open>decides L\<close> have "accepts w" unfolding decides_def by blast
    ultimately show "w \<in> L(M)" unfolding L_M by fastforce
  qed
  show "w \<in> L" if "w \<in> L(M)" proof -
    from \<open>w \<in> L(M)\<close> have "accepts w" "wf_word w" unfolding L_M by blast+
    with \<open>decides L\<close> show "w \<in> L" unfolding decides_def by blast
  qed
qed

lemma TM_lang_unique: "\<exists>\<^sub>\<le>\<^sub>1L. wf_lang L \<and> decides L"
  using decidesE by (intro Uniq_I) metis

end


subsection\<open>Computation of Functions\<close>

context TM begin

definition computes_word :: "('b list \<Rightarrow> 'b list) \<Rightarrow> 'b list \<Rightarrow> bool"
  where computes_def[simp]: "computes_word f w \<equiv> hoare_halt (input w) (input (f w))"

abbreviation computes :: "('b list \<Rightarrow> 'b list) \<Rightarrow> bool"
  where "computes f \<equiv> \<forall>w. computes_word f w"

end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>


subsection\<open>Rejecting TM\<close>


locale Rej_TM =
  fixes \<Sigma> :: "'b::blank set"
    and \<alpha> :: 'a
  assumes finite_alphabet: "finite \<Sigma>"
begin

definition Rejecting_TM :: "('a, 'b) TM"
  where [simp]: "Rejecting_TM \<equiv> \<lparr>
    tape_count = 1,
    states = {\<alpha>},
    start_state = \<alpha>,
    final_states = {\<alpha>},
    accepting_states = {},
    symbols = \<Sigma> \<union> {Bk},
    next_state = \<lambda>q w. \<alpha>,
    next_action = \<lambda>q w. [Nop]
  \<rparr>"

lemma wf_rej_TM: "TM Rejecting_TM"
  unfolding Rejecting_TM_def using finite_alphabet
  by unfold_locales simp_all

sublocale TM "Rejecting_TM" by (fact wf_rej_TM)

lemma rej_TM:
  assumes "set w \<subseteq> \<Sigma>"
  shows "rejects w"
  unfolding rejects_def
proof
  show "wf_word w" using assms by auto
next
  let ?acc = "accepting_states Rejecting_TM"
  show "hoare_halt (init w) (\<lambda>c. state c \<notin> ?acc)"
  proof
    fix c0
    assume "init w c0"
    then have "state c0 = start_state Rejecting_TM" by (fact init_state_start_state)
    then have "is_final ((step^^0) c0)" unfolding Rejecting_TM_def by simp
    moreover have "?acc = {}" unfolding Rejecting_TM_def by simp
    ultimately show "\<exists>n. let cn = (step ^^ n) c0 in is_final cn \<and> state cn \<notin> ?acc"
      using empty_iff by metis
  qed
qed

end \<comment> \<open>\<^locale>\<open>Rej_TM\<close>\<close>

lemma exists_wf_TM: "\<exists>M::('a, 'b::blank) TM. TM M"
proof
  fix \<alpha> :: 'a
  show "TM (Rej_TM.Rejecting_TM {} \<alpha>)" by (intro Rej_TM.wf_rej_TM) (unfold_locales, blast)
qed


subsection\<open>(nat, nat) TM\<close>
text \<open>Every well-formed TM is equivalent to some (nat, nat) TM\<close>

locale nat_TM = TM +
  fixes f :: "'a \<Rightarrow> nat" and f_inv
    and g :: "'b \<Rightarrow> nat" and g_inv
  defines "f \<equiv> SOME f. inj_on f (states M)"  and "f_inv \<equiv> the_inv_into (states M) f"
    and   "g \<equiv> SOME g. inj_on g (symbols M) \<and> g Bk = Bk" and "g_inv \<equiv> the_inv_into (symbols M) g"
begin

lemma f_inj: "inj_on f (states M)" unfolding f_def
  using countable_finite[OF state_axioms(1)] unfolding countable_def ..

lemma g_inj: "inj_on g (symbols M)" and g_Bk: "g Bk = Bk"
proof -
  from symbol_axioms(1) have "\<exists>g::'b \<Rightarrow> nat. inj_on g (symbols M) \<and> g Bk = Bk"
    by (fact finite_imp_inj_to_nat_fix_one)
  then have "inj_on g (symbols M) \<and> g Bk = Bk" unfolding g_def by (fact someI_ex)
  then show "inj_on g (symbols M)" and "g Bk = Bk" by auto
qed


definition natM :: "(nat, nat) TM" ("M\<^sub>\<nat>")
  where [simp]: "natM \<equiv> \<lparr>
    tape_count = tape_count M,
    states = f ` states M,
    start_state = f (start_state M),
    final_states = f ` (final_states M),
    accepting_states = f ` (accepting_states M),
    symbols = g ` (symbols M),
    next_state = \<lambda>q w. f (next_state M (f_inv q) (map g_inv w)),
    next_action = \<lambda>q w. map (action_app g) (next_action M (f_inv q) (map g_inv w))
  \<rparr>"


sublocale pre_natM: pre_TM natM .

lemmas natM_simps = natM_def TM.TM.simps


lemma g_inv_word_wf: "pre_natM.wf_word w \<Longrightarrow> wf_word (map g_inv w)"
proof simp
  assume "set w \<subseteq> g ` symbols M"
  then have "g_inv ` set w \<subseteq> g_inv ` g ` symbols M" by (fact image_mono)
  also have "... = symbols M" using g_inj unfolding g_inv_def by (intro the_inv_into_onto)
  finally show "g_inv ` set w \<subseteq> symbols M" .
qed

lemma natM_wf_state_inv: "pre_natM.wf_state q w \<Longrightarrow> wf_state (f_inv q) (map g_inv w)" 
proof (unfold pre_TM.wf_state_def, elim conjE, intro conjI)
  assume "q \<in> states natM"
  with f_inj show "f_inv q \<in> states M"
    unfolding natM_simps f_inv_def by (rule the_inv_into_into) simp

  assume "length w = tape_count natM" thus "length (map g_inv w) = tape_count M" by force
  assume "pre_natM.wf_word w" thus "wf_word (map g_inv w)" by (fact g_inv_word_wf)
qed


(* using the same name ("natM") for both sublocale and definition works,
 * since the sublocale is only used as namespace *)
sublocale natM: TM natM
  apply unfold_locales
  unfolding natM_def
  using at_least_one_tape apply force
  using state_axioms(1) apply simp
  using state_axioms(2) apply simp
  using state_axioms(3) apply auto[1]
  using state_axioms(4) apply auto[1]
  using symbol_axioms(1) apply auto[1]
  apply simp using g_Bk symbol_axioms(2) apply force
  using next_state natM_wf_state_inv using natM_def apply force
  using next_action_length natM_wf_state_inv apply simp

  apply (unfold pre_TM.wf_state_def)[1] apply simp
  using symbol_action_app[of g, OF g_Bk]
  apply (smt (verit, del_insts) TM.TM.select_convs(6) f_inj f_inv_def g_inv_word_wf image_iff image_mono length_map natM_def next_write_symbol pre_TM.wf_state_def subset_trans the_inv_into_f_f)

  apply (fold natM_def)

  using final_state natM_wf_state_inv
  apply (smt (z3) TM.TM.select_convs(4) TM.TM.select_convs(7) f_inj f_inv_def image_iff natM_def state_axioms(3) subsetD the_inv_into_f_f)
proof -
  fix q w
  assume wfn: "pre_TM.wf_state natM q w" and finn: "q \<in> final_states natM"
  from wfn have wf: "wf_state (f_inv q) (map g_inv w)" by (rule natM_wf_state_inv)
  from finn have fin: "f_inv q \<in> final_states M"
    by (smt (verit, del_insts) TM.TM.select_convs(4) f_inj f_inv_def image_iff natM_def state_axioms(3) subsetD the_inv_into_f_f)
  from final_action[OF wf fin] action_app.simps(4)[of g]
  show "set (next_action M\<^sub>\<nat> q w) \<subseteq> {Nop}"
    unfolding natM_def by auto
qed

lemma "\<And>w. halts w \<Longrightarrow> natM.halts (map g w)"
  and "\<And>w. accepts w \<Longrightarrow> natM.accepts (map g w)"
  and "\<And>w. rejects w \<Longrightarrow> natM.rejects (map g w)"
  sorry

end \<comment> \<open>\<^locale>\<open>nat_TM\<close>\<close>


typedef (overloaded) ('a, 'b::blank) wf_TM = "{M::('a, 'b) TM. TM M}"
  using exists_wf_TM by blast

end
