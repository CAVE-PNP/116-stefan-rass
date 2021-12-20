section\<open>Turing Machines\<close>

theory TM
  imports Main "Supplementary/Misc" "Supplementary/Lists" "Supplementary/Option_S"
    "Intro_Dest_Elim.IHOL_IDE" "HOL-Library.Countable_Set"
begin

section\<open>Turing Machines\<close>

subsection\<open>Prerequisites\<close>

type_synonym ('symbol) word = "'symbol list"
type_synonym ('symbol) lang = "'symbol word set"

text\<open>Symbols on the tape are represented by \<^typ>\<open>'symbol option\<close>,
  where \<^const>\<open>None\<close> represents a "blank" tape-cell.

  This enables clear distinction between the symbols used by TM computations
  and those for TM inputs. Allowing TM input terms to contain "blanks"
  makes reasoning about TM computations harder, since TMs could not reasonably
  differentiate between the end of the input and a sequence of blanks as part of the input.\<close>
type_synonym ('symbol) tp_symbol = "'symbol option"
abbreviation "Bk \<equiv> None"


subsection\<open>Actions\<close>

text\<open>We define TM actions (per tape) as either
  moving the TM head one cell (left \<open>L\<close>, right \<open>R\<close>),
  writing a symbol (\<open>W \<sigma>\<close>) to the cell currently under the TM head ("current cell"),
  or doing nothing (\<open>Nop\<close>).

  \<open>Nop\<close> is somewhat redundant, since it can be simulated by moving the head back-and-forth
  and for single-tape TMs, any step that performs \<open>Nop\<close> can just be left out.
  However, this\<close>
datatype ('symbol) action = L | R | W "'symbol tp_symbol" | Nop

fun symbol_of_write :: "'symbol action \<Rightarrow> 'symbol tp_symbol" where
  "symbol_of_write (W w) = w" | "symbol_of_write _ = None"

lemma symbol_of_write_def: "symbol_of_write a = (case a of W w \<Rightarrow> w | _ \<Rightarrow> None)"
  by (induction a) auto


fun action_app :: "('s1 tp_symbol \<Rightarrow> 's2 tp_symbol) \<Rightarrow> 's1 action \<Rightarrow> 's2 action" where
  "action_app _ L = L"
| "action_app _ R = R"
| "action_app f (W x) = W (f x)"
| "action_app _ Nop = Nop"

abbreviation action_map_app :: "('s1 \<Rightarrow> 's2) \<Rightarrow> 's1 action \<Rightarrow> 's2 action" where
  "action_map_app f \<equiv> action_app (map_option f)"

lemma action_map_app_same[simp]:
  fixes f :: "'s \<Rightarrow> 's"
  shows "action_map_app f a = (case a of W w \<Rightarrow> W (map_option f w) | _ \<Rightarrow> a)"
  by (induction a) auto

lemma symbol_action_app[simp]:
  fixes g :: "('s1 tp_symbol \<Rightarrow> 's2 tp_symbol)" and A :: "'s1 action set"
  assumes "g Bk = Bk"
  shows "symbol_of_write ` (action_app g ` A) = g ` symbol_of_write ` A"
proof -
  from assms have "symbol_of_write (action_app g a) = g (symbol_of_write a)" for a :: "'s1 action"
    by (induction a) simp_all
  then show ?thesis unfolding image_image by simp
qed

lemma symbol_action_map_app[simp]:
  fixes g :: "('s1 \<Rightarrow> 's2)" and A :: "'s1 action set"
  shows "symbol_of_write ` (action_map_app g ` A) = map_option g ` symbol_of_write ` A"
  by (intro symbol_action_app) simp


subsection\<open>Tapes\<close>

text\<open>We describe a TM tape as a record containing:
    \<open>head\<close>, the symbol currently under the TM head, and
    \<open>left\<close>/\<open>right\<close>, the lists of symbols currently left/right of the TM head.
  For both \<open>left\<close> and \<open>right\<close>, the \<open>n\<close>-th element represents the symbol reached
  by \<open>n\<close> consecutive moves left (\<^const>\<open>L\<close>) or right (\<^const>\<open>R\<close>) resp.
  The tape is assumed to be infinite in both directions (containing blanks),
  so blanks will be inserted into the record if the TM crosses the "ends".

  We chose this approach as compared to letting the symbol under the head
  be the first element of \<open>right\<close> (see Xu et al.), as it enables symmetry for move-actions.\<close>
record 's tape =
  left :: "'s tp_symbol list"
  head :: "'s tp_symbol"
  right :: "'s tp_symbol list"

fun tape_app :: "('s1 option \<Rightarrow> 's2 option) \<Rightarrow> 's1 tape \<Rightarrow> 's2 tape" where
  "tape_app f \<lparr> left = l, head = h, right = r \<rparr> = \<lparr> left = map f l, head = f h, right = map f r \<rparr>"

abbreviation tape_map_app :: "('s1 \<Rightarrow> 's2) \<Rightarrow> 's1 tape \<Rightarrow> 's2 tape" where
  "tape_map_app f \<equiv> tape_app (map_option f)"

lemma tape_app_def:
  "tape_app f tp = \<lparr> left = map f (left tp), head = f (head tp), right = map f (right tp) \<rparr>"
  by (induction tp) simp


text\<open>Our definition of tapes allows no completely empty tape (containing zero symbols),
  as the \<^const>\<open>head\<close> symbol is always set.
  However, this makes sense concerning space-complexity,
  as a TM (depending on the exact definition) always reads at least one cell
  (and thus matches Hopcroft's requirement for space-complexity-functions to be at least \<open>1\<close>).\<close>
abbreviation "empty_tape \<equiv> \<lparr> left=[], head = Bk, right=[] \<rparr>"


text\<open>The set of symbols that appear on a tape.
  \<^const>\<open>Bk\<close> (technically) appears (infinitely often) on any given tape
  and is therefore included by default.\<close>
definition set_of_tape :: "'s tape \<Rightarrow> 's tp_symbol set"
  where [simp]: "set_of_tape tp \<equiv> set (left tp) \<union> {head tp} \<union> set (right tp) \<union> {Bk}"

abbreviation the_set_of_tape :: "'s tape \<Rightarrow> 's set"
  where "the_set_of_tape tp \<equiv> Option.these (set_of_tape tp)"


lemma the_set_of_tape_def[simp]:
  "the_set_of_tape tp \<equiv> Option.these (set (left tp) \<union> {head tp} \<union> set (right tp))" by force

lemma set_of_tape_simps[simp]:
  "set_of_tape \<lparr> left = l, head = h, right = r \<rparr> \<equiv> (set l \<union> {h} \<union> set r \<union> {Bk})" by force

lemma set_of_tape_head: "head tp \<in> set_of_tape tp"
  and set_of_tape_Bk:        "Bk \<in> set_of_tape tp" by auto

lemma the_set_of_tape_head: "head tp \<noteq> Bk \<Longrightarrow> the (head tp) \<in> the_set_of_tape tp" by force


lemma tape_set_app: "set_of_tape (tape_app f tp) = f ` set_of_tape tp" if "f Bk = Bk"
proof (induction tp)
  case (fields l h r) show ?case
    unfolding tape_app.simps set_of_tape_simps tape.simps
    unfolding image_Un singleton_image set_map \<open>f Bk = Bk\<close> by simp
qed

lemma the_tape_set_app: "the_set_of_tape (tape_map_app f tp) = f ` the_set_of_tape tp"
  by (subst tape_set_app, unfold these_image) blast+


text\<open>TM execution begins with the head at the start of the input word.\<close>
fun input_tape ("<_>\<^sub>t\<^sub>p") where
  "<[]>\<^sub>t\<^sub>p = empty_tape"
| "<x # xs>\<^sub>t\<^sub>p = \<lparr> left=[], head = x, right = xs \<rparr>"

lemma input_tape_left[simp]: "left (<w>\<^sub>t\<^sub>p) = []"
  by (induction w) auto

lemma input_tape_right: "w \<noteq> [] \<longleftrightarrow> head <w>\<^sub>t\<^sub>p # right <w>\<^sub>t\<^sub>p = w"
  by (induction w) auto

lemma input_tape_app: "f Bk = Bk \<Longrightarrow> tape_app f <w>\<^sub>t\<^sub>p = <map f w>\<^sub>t\<^sub>p"
  by (induction w) auto

lemma input_tape_def:
  "<w>\<^sub>t\<^sub>p = (if w = [] then empty_tape else \<lparr> left=[], head = hd w, right = tl w \<rparr>)"
  by (induction w) auto

abbreviation tp_size :: "'b tape \<Rightarrow> nat" where
  "tp_size tp \<equiv> length (left tp) + length (right tp) + 1"

lemma input_tape_size: "w \<noteq> [] \<Longrightarrow> tp_size <w>\<^sub>t\<^sub>p = length w" by (induction w) force+

fun tp_update :: "('b::blank) action \<Rightarrow> 'b tape \<Rightarrow> 'b tape" where
  "tp_update L \<lparr>left=[],   head = h, right=rs  \<rparr> = \<lparr>left=[],   head = Bk, right=h#rs \<rparr>"
| "tp_update L \<lparr>left=l#ls, head = h, right=rs  \<rparr> = \<lparr>left=ls,   head = l,  right=h#rs \<rparr>"
| "tp_update R \<lparr>left=ls,   head = h, right=[]  \<rparr> = \<lparr>left=h#ls, head = Bk, right=[]   \<rparr>"
| "tp_update R \<lparr>left=ls,   head = h, right=r#rs\<rparr> = \<lparr>left=h#ls, head = r,  right=rs   \<rparr>"
| "tp_update (W h) tp = tp\<lparr> head := h \<rparr>"
| "tp_update Nop tp = tp"

lemma tp_update_set: "set_of_tape (tp_update a tp) \<subseteq> set_of_tape tp \<union> {symbol_of_write a}"
proof -
  obtain l h r where expand_tp: "tp = \<lparr>left=l, head=h, right=r\<rparr>" by (rule tape.cases)
  show ?thesis unfolding expand_tp
  proof (induction a)
    case L show ?case by (induction l) auto next
    case R show ?case by (induction r) auto next
    case (W x) show ?case by (induction r) auto
  qed simp
qed

record ('a, 'b) TM =
  tape_count :: nat

  states       :: "'a set"
  start_state  :: 'a
  final_states :: "'a set"
  accepting_states :: "'a set"

  symbols :: "'b set"

  next_state  :: "'a \<Rightarrow> 'b list \<Rightarrow> 'a"
  next_action :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b action list"

abbreviation "rejecting_states \<equiv> \<lambda>M. final_states M - accepting_states M"

record ('a, 'b) TM_config =
  state :: 'a
  tapes :: "'b tape list"


locale pre_TM =
  fixes M :: "('a, 'b::blank) TM" (structure)
begin

abbreviation "wf_word w \<equiv> set w \<subseteq> symbols M"

abbreviation "wf_words \<equiv> {w. wf_word w}"

lemma wf_words_altdef: "wf_words = lists (symbols M)"
  unfolding lists_eq_set ..

abbreviation "wf_lang X \<equiv> X \<subseteq> wf_words"

\<comment> \<open>A state \<open>q\<close> in combination with a vector \<open>hds\<close> (\<^typ>\<open>'b list\<close>) of symbols currently under the TM-heads,
  is considered a well-formed state w.r.t. a \<^typ>\<open>('a, 'b) TM\<close> \<open>M\<close>, iff
  \<open>q\<close> is a valid state for \<open>M\<close>,
  the number of elements of \<open>hds\<close> matches the number of tapes of \<open>M\<close>, and
  all elements of \<open>hds\<close> are valid symbols for \<open>M\<close> (members of \<open>M\<close>'s tape alphabet).\<close>
definition wf_state :: "'a \<Rightarrow> 'b list \<Rightarrow> bool" where
  "wf_state q hds \<equiv> q \<in> states M \<and> length hds = tape_count M \<and> wf_word hds"

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

lemma wf_config_simps: "wf_config \<lparr> state = q, tapes = tps \<rparr> = (
        q \<in> states M
      \<and> length tps = tape_count M
      \<and> list_all (\<lambda>tp. set_of_tape tp \<subseteq> symbols M) tps)"
  unfolding wf_config_def Let_def TM_config.simps ..

mk_ide wf_config_simps[unfolded list_all_iff]
  |intro wf_config_simpI| |elim wf_config_simpE| |dest wf_config_simpD|


end \<comment> \<open>\<^locale>\<open>pre_TM\<close>\<close>

locale TM = pre_TM +
  assumes at_least_one_tape: "1 \<le> tape_count M"
  and state_axioms: "finite (states M)" "start_state M \<in> states M"
                    "final_states M \<subseteq> states M" "accepting_states M \<subseteq> final_states M"
  and symbol_axioms: "finite (symbols M)" "Bk \<in> (symbols M)"
  and next_state: "\<And>q hds. wf_state q hds \<Longrightarrow> next_state M q hds \<in> states M"
  and next_action_length: "\<And>q hds. wf_state q hds \<Longrightarrow>
                                 length (next_action M q hds) = tape_count M"
  and next_write_symbol: "\<And>q hds. wf_state q hds \<Longrightarrow>
                                 symbol_of_write ` set (next_action M q hds) \<subseteq> symbols M"
  and final_state: "\<And>q hds. wf_state q hds \<Longrightarrow> q \<in> final_states M \<Longrightarrow>
                          next_state M q hds = q"
  and final_action: "\<And>q hds. wf_state q hds \<Longrightarrow> q \<in> final_states M \<Longrightarrow>
                           set (next_action M q hds) \<subseteq> {Nop}"
begin

abbreviation wf_state_of_config ("wf'_state\<^sub>c")
  where "wf_state\<^sub>c c \<equiv> wf_state (state c) (map head (tapes c))"

lemma wf_config_state: "wf_config c \<Longrightarrow> wf_state\<^sub>c c"
  by (intro wf_stateI) (blast, force, use set_of_tape_helpers in fast)

corollary wf_state_tape_count: "wf_state\<^sub>c c \<Longrightarrow> length (tapes c) = tape_count M"
  unfolding wf_state_def by simp

abbreviation is_final :: "('a, 'b) TM_config \<Rightarrow> bool" where
  "is_final c \<equiv> state c \<in> final_states M"

definition step :: "('a, 'b) TM_config \<Rightarrow> ('a, 'b) TM_config" where
  "step c = (let q=state c; w=map head (tapes c) in \<lparr>
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
  let ?q = "state c" and ?w = "map head (tapes c)" and ?ts = "tapes c"

  have ns: "next_state M ?q ?w = ?q" using wf fc by (rule final_state)
  have na: "next_action M ?q ?w = Nop\<^sub>k" using wf fc by (rule final_action_explicit)
  have tu: "map2 tp_update Nop\<^sub>k ?ts = ?ts" using all_Nop_update wf_state_tape_count wf .

  show "step c = c" unfolding step_def Let_def unfolding ns na tu by simp
qed

lemma final_steps: "wf_state\<^sub>c c \<Longrightarrow> is_final c \<Longrightarrow> (step^^n) c = c"
  by (intro funpow_fixpoint final_step_fixpoint)

lemma wf_config_step: "wf_config c \<Longrightarrow> wf_config (step c)"
proof
  let ?q = "state c" and ?w = "map head (tapes c)" and ?ts = "tapes c"
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

lemma wf_start_config[intro]: "wf_word w \<Longrightarrow> wf_config (start_config w)"
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
      and "n \<le> m"
      and "is_final ((step^^n) c)"
    shows "(step^^m) c = (step^^n) c"
proof -
  from \<open>n\<le>m\<close> obtain n' where "m = n' + n" by (metis add.commute less_eqE)
  have wf: "wf_state\<^sub>c ((step^^n) c)" using wf_config_state wf_config_steps \<open>wf_config c\<close> .
  have "(step^^m) c = (step^^n') ((step^^n) c)"
    unfolding \<open>m = n' + n\<close> funpow_add by (rule comp_apply)
  also have "... = (step^^n) c" using wf \<open>is_final ((step^^n) c)\<close> by (rule final_steps)
  finally show "(step^^m) c = (step^^n) c" .
qed

corollary final_mono:
  assumes "wf_config c"
    and "n \<le> m"
    and "is_final ((step^^n) c)"
  shows "is_final ((step^^m) c)"
  unfolding final_le_steps[OF assms] by fact

corollary final_mono':
  assumes "wf_config c"
  shows "mono (\<lambda>n. is_final ((step^^n) c))"
  using final_mono[OF assms] by (intro monoI le_boolI)


end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>

subsection \<open>Composition of Turing Machines\<close>

\<comment> \<open>Let M1 be a k1-tape TM, M2 a k2-tape TM. We define the composition of M1 and M2
    as a (k1+k2-1)-tape TM. First M1 operates on the tapes 0,1,...,k1-1.
    When M1 finishes, M2 operates on the tapes 0,k1,k1+1,...,k1+k2-2.
    Therefore, M1 is expected to write its output (M2's input) on the zeroth tape.\<close>

definition tm_comp :: "('a1, 'b::blank) TM \<Rightarrow> ('a2, 'b) TM \<Rightarrow> ('a1+'a2, 'b) TM" ("_ |+| _" [0, 0] 100)
  where "tm_comp M1 M2 = (let k = tape_count M1 + tape_count M2 - 1 in \<lparr>
    tape_count = k,
    states = states M1 <+> states M2,
    start_state = Inl (start_state M1),
    final_states = Inr ` final_states M2,
    accepting_states = Inr ` accepting_states M2,
    symbols = symbols M1 \<union> symbols M2,
    next_state = (\<lambda>q w. case q of
                        Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                  let q' = next_state M1 q1 w1 in
                                  if q' \<in> final_states M1
                                    then Inr (start_state M2)
                                    else Inl q'
                      | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k}) in
                                  Inr (next_state M2 q2 w2)
                 ),
    next_action = (\<lambda>q w. case q of
                         Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                   pad k Nop (next_action M1 q1 w1)
                       | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k}) in
                                   let a2 = next_action M2 q2 w2 in
                                   hd a2 # Nop \<up> (tape_count M1 - 1) @ tl a2
                        )
  \<rparr>)"

lemma tm_comp_simps[simp]:
  fixes M1 M2
  defines "M \<equiv> M1 |+| M2"
    and "k1 \<equiv> tape_count M1" and "k2 \<equiv> tape_count M2"
  defines "k \<equiv> k1 + k2 - 1"
  shows     "tape_count M = k"
                "states M = states M1 <+> states M2"
           "start_state M = Inl (start_state M1)"
          "final_states M = Inr ` final_states M2"
      "accepting_states M = Inr ` accepting_states M2"
               "symbols M = symbols M1 \<union> symbols M2"
   "next_state M (Inl q1) = (\<lambda>w. let q' = next_state M1 q1 (nths w {0..<k1}) in
                                   if q' \<in> final_states M1 then Inr (start_state M2) else Inl q')"
   "next_state M (Inr q2) = (\<lambda>w. Inr (next_state M2 q2 (nths w ({0} \<union> {k1..<k}))))"
  "next_action M (Inl q1) = (\<lambda>w. pad k Nop (next_action M1 q1 (nths w {0..<k1})))"
  "next_action M (Inr q2) = (\<lambda>w. let a2 = next_action M2 q2 (nths w ({0} \<union> {k1..<k})) in
                                   hd a2 # Nop \<up> (k1 - 1) @ tl a2)"
  unfolding M_def k_def k1_def k2_def
  unfolding tm_comp_def[unfolded Let_def] Let_def sum.case TM.TM.simps by (fact refl)+

lemma tm_comp_simps':
  fixes M1 M2
  defines "M \<equiv> M1 |+| M2"
    and "k \<equiv> tape_count M1 + tape_count M2 - 1"
  shows "next_state M = (\<lambda>q w. case q of
                              Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1};
                                            q' = next_state M1 q1 w1 in
                                          if q' \<in> final_states M1
                                            then Inr (start_state M2)
                                            else Inl q'
                            | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k}) in
                                          Inr (next_state M2 q2 w2) )"
       "next_action M = (\<lambda>q w. case q of
                          Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                      pad k Nop (next_action M1 q1 w1)
                        | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k});
                                        a2 = next_action M2 q2 w2 in
                                      hd a2 # Nop \<up> (tape_count M1 - 1) @ tl a2 )"
  unfolding M_def k_def tm_comp_def[unfolded Let_def] Let_def TM.TM.simps by (fact refl)+


lemma tm_comp_tape_count:
  fixes M1 M2
  defines "M \<equiv> M1 |+| M2"
  shows "TM M2 \<Longrightarrow> tape_count M1 \<le> tape_count M"
    and "TM M1 \<Longrightarrow> tape_count M2 \<le> tape_count M"
proof -
  assume "TM M2"
  from \<open>TM M2\<close>[THEN TM.at_least_one_tape] show "tape_count M1 \<le> tape_count M"
    unfolding M_def tm_comp_simps using le_add1 by (subst diff_add_assoc)
next
  assume "TM M1"
  from \<open>TM M1\<close>[THEN TM.at_least_one_tape] show "tape_count M2 \<le> tape_count M"
    unfolding M_def tm_comp_simps using le_add1 by (subst add.commute) (subst diff_add_assoc)
qed

lemma tm_comp_cases [consumes 4, case_names wfs1 wfs2]:
  fixes M1 M2 P
  defines "k1 \<equiv> tape_count M1" and "k2 \<equiv> tape_count M2"
  defines "k \<equiv> tape_count M1 + tape_count M2 - 1"
  defines "M \<equiv> M1 |+| M2"
  assumes wf: "TM M1" "TM M2"
    and symbols_eq: "symbols M1 = symbols M2"
  assumes wfs: "pre_TM.wf_state M q w"
  assumes q1: "\<And>q1 w. q = (Inl q1) \<Longrightarrow> pre_TM.wf_state M1 q1 (nths w {0..<k1}) \<Longrightarrow> P (Inl q1) w"
  assumes q2: "\<And>q2 w. q = (Inr q2) \<Longrightarrow> pre_TM.wf_state M2 q2 (nths w ({0} \<union> {k1..<k})) \<Longrightarrow> P (Inr q2) w"
  shows "P q w"
  using wfs
proof (cases q)
  case (Inl q1)
  from wfs show "P q w" unfolding \<open>q = Inl q1\<close>
  proof (intro q1[OF \<open>q = Inl q1\<close>], unfold pre_TM.wf_state_def, elim conjE, intro conjI)
    assume "Inl q1 \<in> states M"
    then show "q1 \<in> states M1" unfolding M_def tm_comp_simps by blast

    assume len_w: "length w = tape_count M"
    from tm_comp_tape_count(1)[OF wf(2)] show "length (nths w {0..<k1}) = tape_count M1"
      unfolding M_def length_nths_interval len_w k1_def by (subst min_absorb2) auto

    have "set (nths w {0..<k1}) \<subseteq> set w" by (fact set_nths_subset)
    also assume "... \<subseteq> symbols M"
    also have "... \<subseteq> symbols M1" unfolding M_def tm_comp_simps symbols_eq by blast
    finally show "set (nths w {0..<k1}) \<subseteq> symbols M1" .
  qed
next
  case (Inr q2)
  from wfs show "P q w" unfolding \<open>q = Inr q2\<close>
  proof (intro q2[OF \<open>q = Inr q2\<close>], unfold pre_TM.wf_state_def, elim conjE, intro conjI)
    assume "Inr q2 \<in> states M"
    then show "q2 \<in> states M2" unfolding M_def tm_comp_simps by blast

    assume len_w: "length w = tape_count M"

    have "1 \<le> length w" unfolding len_w M_def tm_comp_simps
      using wf[THEN TM.at_least_one_tape] by linarith
    have "1 \<le> k1" unfolding k1_def by (fact wf(1)[THEN TM.at_least_one_tape])
    have "1 \<le> k2" unfolding k2_def by (fact wf(2)[THEN TM.at_least_one_tape])

    have "length (nths w ({0} \<union> {k1..<k})) = min (length w) k - k1 + 1"
      unfolding nths_insert_interval_less[OF \<open>1 \<le> length w\<close> \<open>1 \<le> k1\<close>]
      unfolding length_Cons length_nths_interval by simp
    also have "... = k1 + k2 - 1 - k1 + 1"
      unfolding len_w M_def tm_comp_simps
      unfolding k_def k1_def k2_def min.idem ..
    also have "... = k2" using TM.at_least_one_tape[OF wf(2), folded k2_def] by simp
    finally show "length (nths w ({0} \<union> {k1..<k})) = tape_count M2" unfolding k2_def .

     have "set (nths w ({0} \<union> {k1..<k})) \<subseteq> set w" by (fact set_nths_subset)
    also assume "... \<subseteq> symbols M"
    also have "... \<subseteq> symbols M2" unfolding M_def tm_comp_simps symbols_eq by blast
    finally show "set (nths w ({0} \<union> {k1..<k})) \<subseteq> symbols M2" .
  qed
qed

lemma (in TM) sw_Nop_k: "symbol_of_write ` set (Nop \<up> n) \<subseteq> symbols M"
  using symbol_axioms(2) set_replicate_subset by force

lemma wf_tm_comp:
  fixes M1 :: "('a1, 'b::blank) TM" and M2 :: "('a2, 'b) TM"
  assumes wf: "TM M1" "TM M2"
    and symbols_eq[simp]: "symbols M1 = symbols M2"
  shows "TM (M1 |+| M2)" (is "TM ?M")
proof (intro TM.intro; (elim tm_comp_cases[OF assms])?)
  let ?k1 = "tape_count M1" and ?k2 = "tape_count M2"
  let ?k = "?k1 + ?k2 - 1"

  interpret M1: TM M1 by fact
  interpret M2: TM M2 by fact

  from M2.at_least_one_tape have "tape_count ?M \<ge> ?k1"
    unfolding tm_comp_simps using le_add1 by (subst diff_add_assoc)
  with M1.at_least_one_tape show "tape_count ?M \<ge> 1" by (fact le_trans)
  from M1.state_axioms(1) M2.state_axioms(1) show "finite (states ?M)" by simp
  from M1.state_axioms(2) show "start_state ?M \<in> states ?M" by auto
  from M2.state_axioms(3) show "final_states ?M \<subseteq> states ?M" by auto
  from M2.state_axioms(4) show "accepting_states ?M \<subseteq> final_states ?M" by auto
  from M1.symbol_axioms(1) show "finite (symbols ?M)" by simp
  from M1.symbol_axioms(2) show "Bk \<in> symbols ?M" by simp

  (* case distinction on q *)
  fix w :: "'b list" and q :: "'a1 + 'a2"
  {
    fix q1 (* case M1: "q = Inl q1" *)
    assume "q = Inl q1" and wfs1: "M1.wf_state q1 (nths w {0..<?k1})"

    show "next_state ?M (Inl q1) w \<in> states ?M" unfolding tm_comp_simps Let_def
    proof (rule if_cases)
      show "Inr (start_state M2) \<in> states M1 <+> states M2"
        using TM.state_axioms(2)[OF wf(2)] by blast
      show "Inl (next_state M1 q1 (nths w {0..<?k1})) \<in> states M1 <+> states M2"
        using TM.next_state[OF wf(1) wfs1] by blast
    qed

    show "length (next_action ?M (Inl q1) w) = tape_count ?M"
      using tm_comp_tape_count(1)[OF wf(2), of M1]
      unfolding tm_comp_simps pad_length
      unfolding M1.next_action_length[OF wfs1] by (fact max_absorb1)

    show "symbol_of_write ` set (next_action ?M (Inl q1) w) \<subseteq> symbols ?M"
      unfolding tm_comp_simps set_append image_Un
    proof (intro Un_mono)
      show "symbol_of_write ` set (next_action M1 q1 (nths w {0..<?k1})) \<subseteq> symbols M1"
        by (fact M1.next_write_symbol[OF wfs1])
      show "symbol_of_write ` set (Nop \<up> n) \<subseteq> symbols M2" for n by (fact M2.sw_Nop_k)
    qed

    assume "q \<in> final_states ?M" (* this is only ever true if q represents a state of M2 *)
    then have False unfolding \<open>q = Inl q1\<close> tm_comp_simps by blast
    then show "next_state ?M (Inl q1) w = Inl q1"
      and "set (next_action ?M (Inl q1) w) \<subseteq> {Nop}" by blast+
  }

  {
    fix q2 (* case M2: "q = Inr q2" *)
    assume "q = Inr q2" and wfs2: "M2.wf_state q2 (nths w ({0} \<union> {?k1..<?k}))"

    show "next_state ?M (Inr q2) w \<in> states ?M" unfolding tm_comp_simps
      using TM.next_state[OF wf(2) wfs2] by blast

    have "length (next_action ?M (Inr q2) w) = ?k1 - 1 + (?k2 - 1) + 1"
      unfolding tm_comp_simps Let_def
      unfolding list.size length_append length_replicate length_tl
      unfolding M2.next_action_length[OF wfs2]
      by presburger
    also have "... = ?k - 1 + 1"
      unfolding add_diff_assoc2[OF M1.at_least_one_tape] add_diff_assoc[OF M2.at_least_one_tape] ..
    also have "... = tape_count ?M"
      using \<open>tape_count ?M \<ge> 1\<close> unfolding tm_comp_simps by (fact diff_add)
    finally show "length (next_action ?M (Inr q2) w) = tape_count ?M" .

    define xs where xs: "xs \<equiv> next_action M2 q2 (nths w ({0} \<union> {?k1..<?k}))"
    define ys :: "'b action list" where ys: "ys \<equiv> Nop \<up> (?k1 - 1)"
    have sna: "set (next_action ?M (Inr q2) w) = set xs \<union> set ys"
    proof -
      have "length xs \<ge> 1" unfolding xs M2.next_action_length[OF wfs2]
        by (fact M2.at_least_one_tape)
      then have "xs \<noteq> []" by auto

      have "set (next_action ?M (Inr q2) w) = set (hd xs # ys @ tl xs)"
        unfolding tm_comp_simps Let_def set_append
        unfolding xs[symmetric] ys[symmetric] ..
      also have "set (hd xs # ys @ tl xs) = insert (hd xs) (set (ys @ tl xs))" by simp
      also have "... = insert (hd xs) (set (tl xs @ ys))" by force
      also have "... = set ((hd xs # tl xs) @ ys)" by force
      also have "... = set (hd xs # tl xs) \<union> set ys" by simp
      also have "... = set xs \<union> set ys" using \<open>xs \<noteq> []\<close> by force
      finally show "set (next_action ?M (Inr q2) w) = set xs \<union> set ys" .
    qed
    then have "symbol_of_write ` set (next_action ?M (Inr q2) w) = symbol_of_write ` (set xs \<union> set ys)"
      by (rule arg_cong)
    also have "... = symbol_of_write ` set xs \<union> symbol_of_write ` set ys" by (fact image_Un)
    also have "... \<subseteq> symbols ?M" unfolding tm_comp_simps symbols_eq
    proof (intro Un_mono)
      from wfs2 show "symbol_of_write ` set xs \<subseteq> symbols M2"
        unfolding xs by (fact M2.next_write_symbol)
      have "symbol_of_write ` set ys \<subseteq> {Bk}" unfolding ys by force
      also have "... \<subseteq> symbols M2" using M2.symbol_axioms(2) by blast
      finally show "symbol_of_write ` set ys \<subseteq> symbols M2" .
    qed
    finally show "symbol_of_write ` set (next_action ?M (Inr q2) w) \<subseteq> symbols ?M" .


    assume "q \<in> final_states ?M"
    then have qf: "q2 \<in> final_states M2" unfolding \<open>q = Inr q2\<close> tm_comp_simps by blast

    show "next_state ?M (Inr q2) w = Inr q2" unfolding tm_comp_simps M2.final_state[OF wfs2 qf] ..
    show "set (next_action ?M (Inr q2) w) \<subseteq> {Nop}" unfolding sna
    proof (intro Un_least)
      from wfs2 qf show "set xs \<subseteq> {Nop}" unfolding xs by (fact M2.final_action)
      show "set ys \<subseteq> {Nop}" unfolding ys by (fact set_replicate_subset)
    qed
  }
qed


definition simple_alphabet_lift where
  "simple_alphabet_lift M \<Sigma> \<equiv>
    M\<lparr>
          symbols := symbols M \<union> \<Sigma>,
       next_state := (\<lambda>q w. if set w \<subseteq> symbols M
                              then next_state M q w
                              else q),
      next_action := (\<lambda>q w. if set w \<subseteq> symbols M
                              then next_action M q w
                              else Nop \<up> tape_count M)
    \<rparr>"

lemma (in TM) wf_alphabet_lift:
  assumes "finite \<Sigma>'"
  shows "TM (simple_alphabet_lift M \<Sigma>')"
  unfolding simple_alphabet_lift_def using TM_axioms
proof (induction M)
  case (fields k Z q0 F Fa \<Sigma> \<delta>s \<delta>a)
  let ?M = "\<lparr>tape_count = k, states = Z, start_state = q0, final_states = F,
    accepting_states = Fa, symbols = \<Sigma>, next_state = \<delta>s, next_action = \<delta>a\<rparr>"
  interpret M: TM ?M by fact

  let ?M' = "\<lparr>tape_count = k, states = Z, start_state = q0, final_states = F,
    accepting_states = Fa, symbols = \<Sigma> \<union> \<Sigma>',
    next_state = \<lambda>q w. if set w \<subseteq> \<Sigma> then \<delta>s q w else q,
    next_action = \<lambda>q w. if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k\<rparr>"

  show ?case proof (intro TM.intro, unfold TM.TM.simps)
    show "1 \<le> k" using M.at_least_one_tape unfolding TM.TM.simps .
    show "finite Z" "q0 \<in> Z" "F \<subseteq> Z" "Fa \<subseteq> F" using M.state_axioms unfolding TM.TM.simps .
    show "finite (\<Sigma> \<union> \<Sigma>')" using M.symbol_axioms(1) assms unfolding TM.TM.simps by (fact finite_UnI)
    show "Bk \<in> \<Sigma> \<union> \<Sigma>'" using M.symbol_axioms(2) unfolding TM.TM.simps ..

    fix q w
    assume wfs: "pre_TM.wf_state ?M' q w"
    then have "q \<in> Z" "length w = k" "set w \<subseteq> \<Sigma> \<union> \<Sigma>'"
      unfolding pre_TM.wf_state_def TM.TM.simps by blast+
    then have wfI: "set w \<subseteq> \<Sigma> \<Longrightarrow> M.wf_state q w" unfolding M.wf_state_def TM.TM.simps by blast

    show "(if set w \<subseteq> \<Sigma> then \<delta>s q w else q) \<in> Z"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> \<delta>s q w \<in> Z" by (intro M.next_state[unfolded TM.TM.simps] wfI)
      show "q \<in> Z" by fact
    qed

    show "length (if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k) = k"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> length (\<delta>a q w) = k"
        by (intro M.next_action_length[unfolded TM.TM.simps] wfI)
      show "length (Nop \<up> k) = k" by (fact length_replicate)
    qed

    show "symbol_of_write ` set (if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k) \<subseteq> \<Sigma> \<union> \<Sigma>'"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> symbol_of_write ` set (\<delta>a q w) \<subseteq> \<Sigma> \<union> \<Sigma>'"
        using M.next_write_symbol[OF wfI] unfolding TM.TM.simps by blast
      show "symbol_of_write ` set (Nop \<up> k) \<subseteq> \<Sigma> \<union> \<Sigma>'"
        using M.sw_Nop_k unfolding TM.TM.simps by fast
    qed

    assume "q \<in> F"

    show "(if set w \<subseteq> \<Sigma> then \<delta>s q w else q) = q"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> \<delta>s q w = q"
        using M.final_state[OF wfI] \<open>q \<in> F\<close> unfolding TM.TM.simps by blast
      show "q = q" ..
    qed
    show "set (if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k) \<subseteq> {Nop}"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> set (\<delta>a q w) \<subseteq> {Nop}"
        using M.final_action[OF wfI] \<open>q \<in> F\<close> unfolding TM.TM.simps by blast
      show "set (Nop \<up> k) \<subseteq> {Nop}" by (fact set_replicate_subset)
    qed
  qed
qed

definition lift_tm_comp where
  "lift_tm_comp M1 M2 \<equiv> tm_comp (simple_alphabet_lift M1 (symbols M2))
                                (simple_alphabet_lift M2 (symbols M1))"

lemma wf_lift_tm_comp:
  assumes wf: "TM M1" "TM M2"
  shows "TM (lift_tm_comp M1 M2)"
  unfolding lift_tm_comp_def
proof (rule wf_tm_comp)
  let ?M1 = "simple_alphabet_lift M1 (symbols M2)"
  let ?M2 = "simple_alphabet_lift M2 (symbols M1)"

  interpret M1: TM M1 by fact
  interpret M2: TM M2 by fact

  show "TM (simple_alphabet_lift M1 (symbols M2))"
    using wf(1) M2.symbol_axioms(1) by (fact TM.wf_alphabet_lift)
  show "TM (simple_alphabet_lift M2 (symbols M1))"
    using wf(2) M1.symbol_axioms(1) by (fact TM.wf_alphabet_lift)

  show "symbols ?M1 = symbols ?M2" unfolding simple_alphabet_lift_def TM.TM.simps by auto
qed


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

  from wf \<open>n1 \<le> n\<close> fn1 have steps1: "((step^^n) c) = ((step^^n1) c)" by (fact final_le_steps)
  from wf \<open>n2 \<le> n\<close> fn2 have steps2: "((step^^n) c) = ((step^^n2) c)" by (fact final_le_steps)
  from fn1 q1 q2 have "let qn=(step^^n) c in is_final qn \<and> Q1 qn \<and> Q2 qn"
    by (fold steps1 steps2) simp
  thus "\<exists>n. let cn = (step ^^ n) c in is_final cn \<and> Q1 cn \<and> Q2 cn" ..
qed

abbreviation (input) init where "init w \<equiv> (\<lambda>c. c = start_config w)"

definition halts :: "'b list \<Rightarrow> bool"
  where "halts w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>_. True)"

lemma halts_I[intro]: "wf_word w \<Longrightarrow> \<exists>n. is_final (run n w) \<Longrightarrow> halts w"
  unfolding halts_def hoare_halt_def by simp

lemma halts_D[dest]:
  assumes "halts w"
  shows "wf_word w"
    and "\<exists>n. is_final (run n w)"
  using assms hoare_halt_def wf_start_config
  unfolding halts_def by fastforce+

lemma halts_altdef: "halts w \<longleftrightarrow> wf_word w \<and> (\<exists>n. is_final (run n w))" by blast

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

definition "input_assert (P::'b list \<Rightarrow> bool) \<equiv> \<lambda>c::('a, 'b::blank) TM_config.
              let tp = hd (tapes c) in P (head tp # right tp) \<and> left tp = []"

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

abbreviation "good_assert P \<equiv> \<forall>w. P (trim Bk w) = P w"

lemma good_assert_single: "good_assert P \<Longrightarrow> P [Bk] = P []"
proof -
  assume "good_assert P"
  hence "P (trim Bk [Bk]) = P [Bk]" ..
  thus ?thesis by simp
qed

lemma input_tp_assert:
  assumes "good_assert P"
  shows "P w \<longleftrightarrow> input_assert P (start_config w)"
proof (cases "w = []")
  case True
  then show ?thesis
    unfolding input_assert_def start_config_def apply simp
    using good_assert_single[OF assms] ..
next
  case False
  then show ?thesis
    unfolding input_assert_def start_config_def apply simp
    using input_tape_right by metis
qed

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

lemma acceptsE[elim]:
  assumes "accepts w"
  obtains n where "state (run n w) \<in> accepting_states M"
using accepts_def assms hoare_halt_def wf_start_config by fastforce

definition rejects :: "'b list \<Rightarrow> bool"
  where "rejects w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<in> rejecting_states M)"

lemma rejectsI[intro]:
  assumes "wf_word w"
    and "is_final (run n w)"
    and "state (run n w) \<in> rejecting_states M"
  shows "rejects w"
  using assms unfolding rejects_def hoare_halt_def
  by meson

lemma rejectsE[elim]:
  assumes "rejects w"
  obtains n where "is_final (run n w)"
    and "state (run n w) \<in> rejecting_states M"
by (smt (verit, ccfv_SIG) assms hoare_halt_def rejects_def wf_start_config)

lemma halts_iff: "halts w \<longleftrightarrow> accepts w \<or> rejects w"
proof (intro iffI)
  assume "halts w"
  then obtain n where fin: "is_final (run n w)" and wf: "wf_word w" by blast
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

  have "hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M)"
    using \<open>accepts w\<close> unfolding accepts_def by (rule conjunct2)
  moreover have "hoare_halt (init w) (\<lambda>c. state c \<in> rejecting_states M)"
    using \<open>rejects w\<close> unfolding rejects_def by (rule conjunct2)
  ultimately have "hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M
                                          \<and> state c \<in> rejecting_states M)"
    by (fact hoare_and)
  then have "hoare_halt (init w) (\<lambda>c. False)" by auto

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
  where "decides L \<equiv> wf_lang L \<and> (\<forall>w\<in>wf_words. decides_word L w)"

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

lemma decides_altdef4: "decides_word L w \<longleftrightarrow> (if w \<in> L then accepts w else rejects w)"
  unfolding decides_def using acc_not_rej by (cases "w \<in> L") auto

lemma decides_altdef3: "decides_word L w \<longleftrightarrow> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M \<longleftrightarrow> w\<in>L)"
  unfolding decides_altdef4 accepts_def rejects_def
  by (cases "w\<in>L") (simp add: hoare_halt_def del: start_config_def)+

end


subsection\<open>TM Languages\<close>

definition TM_lang :: "('a, 'b::blank) TM \<Rightarrow> 'b lang" ("L'(_')")
  where "L(M) \<equiv> if (\<forall>w\<in>pre_TM.wf_words M. TM.halts M w)
                then {w\<in>pre_TM.wf_words M. TM.accepts M w}
                else undefined"

context TM begin

lemma decides_TM_lang_accepts: "(\<And>w. wf_word w \<Longrightarrow> halts w) \<Longrightarrow> decides {w. accepts w}"
  unfolding decides_def rejects_altdef accepts_def
  by (simp add: Collect_mono)

lemma decides_TM_lang: "(\<And>w. wf_word w \<Longrightarrow> halts w) \<Longrightarrow> decides L(M)"
  unfolding TM_lang_def using decides_TM_lang_accepts by auto

lemma decidesE: "decides L \<Longrightarrow> L(M) = L"
proof safe
  assume dec: "\<forall>w\<in>wf_words. decides_word L w"
  assume wfl: \<open>wf_lang L\<close>
  from dec have "\<forall>w\<in>wf_words. halts w"
    using decides_halts by blast
  then have L_M: "L(M) = {w\<in>wf_words. accepts w}" unfolding TM_lang_def by presburger

  fix w
  show "w \<in> L(M)" if "w \<in> L" proof -
    from \<open>w\<in>L\<close> wfl have "wf_word w" by blast
    moreover from \<open>w\<in>L\<close> \<open>wf_word w\<close> dec have "accepts w" unfolding decides_def by blast
    ultimately show "w \<in> L(M)" unfolding L_M by fastforce
  qed
  show "w \<in> L" if "w \<in> L(M)" proof -
    from \<open>w \<in> L(M)\<close> have "accepts w" "wf_word w" unfolding L_M by blast+
    with dec show "w \<in> L" unfolding decides_def by blast
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


subsection\<open>The Rejecting TM\<close>


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

sublocale TM Rejecting_TM by (fact wf_rej_TM)

lemma rej_TM:
  assumes "set w \<subseteq> \<Sigma>"
  shows "rejects w"
  unfolding rejects_def
proof
  show "wf_word w" using assms by auto
next
  let ?rej = "rejecting_states Rejecting_TM"
  have final_rej: "?rej = final_states Rejecting_TM" by simp
  show "hoare_halt (init w) (\<lambda>c. state c \<in> ?rej)"
  proof
    fix c0
    assume "init w c0"
    then have "state c0 = start_state Rejecting_TM" by (fact init_state_start_state)
    then have "is_final ((step^^0) c0)" unfolding Rejecting_TM_def by simp
    then show "\<exists>n. let cn = (step ^^ n) c0 in is_final cn \<and> state cn \<in> ?rej"
      using final_rej by metis
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
  defines "f \<equiv> SOME f. inj_on f (states M)"  and "f_inv \<equiv> inv_into (states M) f"
    and   "g \<equiv> SOME g. inj_on g (symbols M) \<and> g Bk = Bk" and "g_inv \<equiv> inv_into (symbols M) g"
begin

lemma f_inj: "inj_on f (states M)" unfolding f_def
  using countable_finite[OF state_axioms(1)] unfolding countable_def ..

lemma g_inj: "inj_on g (symbols M)" and g_Bk[simp]: "g Bk = Bk"
proof -
  from symbol_axioms(1) have "\<exists>g::'b \<Rightarrow> nat. inj_on g (symbols M) \<and> g Bk = Bk"
    by (fact finite_imp_inj_to_nat_fix_one)
  then have "inj_on g (symbols M) \<and> g Bk = Bk" unfolding g_def by (fact someI_ex)
  then show "inj_on g (symbols M)" and "g Bk = Bk" by auto
qed

definition natM :: "(nat, nat) TM" ("M\<^sub>\<nat>")
  where "natM \<equiv> \<lparr>
    tape_count = tape_count M,
    states = f ` states M,
    start_state = f (start_state M),
    final_states = f ` (final_states M),
    accepting_states = f ` (accepting_states M),
    symbols = g ` (symbols M),
    next_state = \<lambda>q w. f (next_state M (f_inv q) (map g_inv w)),
    next_action = \<lambda>q w. map (action_app g) (next_action M (f_inv q) (map g_inv w))
  \<rparr>"

lemma natM_simps[simp]:
  "tape_count natM = tape_count M"
  "states natM = f ` states M"
  "symbols natM = g ` symbols M"
  "accepting_states natM = f ` accepting_states M"
  unfolding natM_def by auto

lemma natM_rejecting_states[simp]:
  "rejecting_states natM = f ` rejecting_states M"
  unfolding natM_def apply simp
  by (metis Diff_subset f_inj inj_on_image_set_diff state_axioms(3) state_axioms(4) subset_trans)

lemma f_bij: "bij_betw f (states M) (states natM)" unfolding natM_simps
  using f_inj by (fact inj_on_imp_bij_betw)
lemma f_inv_bij: "bij_betw f_inv (states natM) (states M)" unfolding f_inv_def
  using f_bij by (fact bij_betw_inv_into)
lemma f_inv: "q \<in> states M \<Longrightarrow> f_inv (f q) = q" unfolding f_inv_def
  using f_inj by (rule inv_into_f_f)
lemma f_inv_img: "f_inv ` states natM = states M"
  using f_inj unfolding natM_simps f_inv_def by (fact inv_into_onto)
lemma inv_f: "q \<in> states natM \<Longrightarrow> f (f_inv q) = q"
  unfolding natM_simps f_inv_def by (fact f_inv_into_f)

lemma g_bij: "bij_betw g (symbols M) (symbols natM)" unfolding natM_simps
  using g_inj by (fact inj_on_imp_bij_betw)
lemma g_inv_bij: "bij_betw g_inv (symbols natM) (symbols M)" unfolding g_inv_def
  using g_bij by (fact bij_betw_inv_into)
lemma g_inv: "\<sigma> \<in> symbols M \<Longrightarrow> g_inv (g \<sigma>) = \<sigma>" unfolding g_inv_def
  using g_inj by (rule inv_into_f_f)
lemma g_inv_img: "g_inv ` g ` symbols M = symbols M"
  using g_inj unfolding g_inv_def by (fact inv_into_onto)
lemma inv_g: "\<sigma> \<in> symbols natM \<Longrightarrow> g (g_inv \<sigma>) = \<sigma>"
  unfolding natM_simps g_inv_def by (fact f_inv_into_f)
lemma g_inv_mem_eq: "\<sigma> \<in> symbols natM \<Longrightarrow> g_inv \<sigma> \<in> symbols M"
  unfolding g_inv_def natM_simps by (fact inv_into_into)

lemma map_g_inj: "inj_on (map g) wf_words"
  using g_inj list.inj_map_strong
  by (smt (verit, best) inj_on_def mem_Collect_eq subsetD)

sublocale pre_natM: pre_TM natM .

lemma g_inv_word_wf: "pre_natM.wf_word w \<Longrightarrow> wf_word (map g_inv w)"
proof simp
  assume "set w \<subseteq> g ` symbols M"
  then have "g_inv ` set w \<subseteq> g_inv ` g ` symbols M" by (fact image_mono)
  also have "... = symbols M" using g_inj unfolding g_inv_def by (fact inv_into_onto)
  finally show "g_inv ` set w \<subseteq> symbols M" .
qed

lemma f_inv_states: "q \<in> states natM \<Longrightarrow> f_inv q \<in> states M"
  unfolding natM_simps f_inv_def by (fact inv_into_into)

lemma map_g_bij: "bij_betw (map g) wf_words pre_natM.wf_words"
proof (intro bij_betw_imageI)
  show "(map g) ` (wf_words) = pre_natM.wf_words"
    unfolding natM_simps lists_eq_set[symmetric] lists_image ..
qed (fact map_g_inj)

lemma map_g_g_inv: "pre_natM.wf_word w \<Longrightarrow> map g (map g_inv w) = w"
  using g_inj g_inv_def map_map_inv_into_id by auto
lemma map_g_inv_g: "wf_word w' \<Longrightarrow> map g_inv (map g w') = w'"
  using g_inj g_inv_def map_inv_into_map_id by blast

lemma natM_wf_state_inv: "pre_natM.wf_state q w \<Longrightarrow> wf_state (f_inv q) (map g_inv w)"
proof (unfold pre_TM.wf_state_def, elim conjE, intro conjI)
  assume "q \<in> states natM" thus "f_inv q \<in> states M" by (fact f_inv_states)
  assume "length w = tape_count natM" thus "length (map g_inv w) = tape_count M" by force
  assume "pre_natM.wf_word w" thus "wf_word (map g_inv w)" by (fact g_inv_word_wf)
qed

lemma natM_wf_word: "wf_word w \<Longrightarrow> pre_natM.wf_word (map g w)" by auto


lemma wf_natM: "TM natM"
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
  using next_action_length natM_wf_state_inv apply (simp add: natM_def)

  apply (unfold pre_TM.wf_state_def)[1] apply simp
  using symbol_action_app[of g, OF g_Bk] next_write_symbol
  apply (metis (no_types, lifting) f_inv_def g_inj g_inv_def inv_into_image_cancel inv_into_into length_map list.set_map pre_TM.wf_state_def subset_image_iff subset_trans)

  apply (fold natM_def)

  using final_state natM_wf_state_inv
  apply (smt (z3) TM.TM.select_convs(4) TM.TM.select_convs(7) f_inj f_inv_def image_iff natM_def state_axioms(3) subsetD inv_into_f_f)
proof -
  fix q w
  assume wfn: "pre_TM.wf_state natM q w" and finn: "q \<in> final_states natM"
  from wfn have wf: "wf_state (f_inv q) (map g_inv w)" by (rule natM_wf_state_inv)
  from finn have fin: "f_inv q \<in> final_states M"
    by (smt (verit, del_insts) TM.TM.select_convs(4) f_inj f_inv_def image_iff natM_def state_axioms(3) subsetD inv_into_f_f)
  from final_action[OF wf fin] action_app.simps(4)[of g]
  show "set (next_action M\<^sub>\<nat> q w) \<subseteq> {Nop}"
    unfolding natM_def by auto
qed

(* using the same name ("natM") for both sublocale and definition works,
 * since the sublocale is only used as namespace *)
sublocale natM: TM natM
  by (fact wf_natM)


fun config_conv :: "('a, 'b) TM_config \<Rightarrow> (nat, nat) TM_config" ("C") where
  "config_conv \<lparr> state = q, tapes = tps \<rparr> =
          \<lparr> state = f q, tapes = map (tape_app g) tps \<rparr>"

fun config_conv_inv :: "(nat, nat) TM_config \<Rightarrow> ('a, 'b) TM_config" ("C\<inverse>") where
  "config_conv_inv \<lparr> state = q, tapes = tps \<rparr> =
          \<lparr> state = f_inv q, tapes = map (tape_app g_inv) tps \<rparr>"

lemmas cc_simps = config_conv.simps config_conv_inv.simps

abbreviation config_conv_inv_and_conv ("CC") where "CC c \<equiv> C\<inverse> (C c)"
abbreviation config_conv_and_inv ("CC\<inverse>") where "CC\<inverse> c \<equiv> C (C\<inverse> c)"

lemma config_conv_state_inv:
  "q \<in> states M \<Longrightarrow> state (CC \<lparr> state = q, tapes = tps \<rparr>) = q"
  unfolding cc_simps TM.TM_config.simps(1) by (fact f_inv)

lemma tape_app_g_inv: "set_of_tape tp \<subseteq> symbols M \<Longrightarrow> (tape_app g_inv \<circ> tape_app g) tp = tp"
proof (induction tp)
  case (fields ls m rs)
  then have l: "set ls \<subseteq> symbols M" and m: "m \<in> symbols M" and r: "set rs \<subseteq> symbols M" by auto
  have *: "\<And>w. wf_word w \<Longrightarrow> map (\<lambda>x. g_inv (g x)) w = w" by (intro map_idI g_inv) blast
  show ?case unfolding comp_def tape_app.simps map_map unfolding *[OF l] *[OF r] g_inv[OF m] ..
qed

lemma config_conv_inv: "wf_config c \<Longrightarrow> CC c = c"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>"
  from \<open>wf_config ?c\<close> have "q \<in> states M"
    and tps_symbols: "list_all (\<lambda>tp. set_of_tape tp \<subseteq> symbols M) tps"
    unfolding wf_config_def Let_def TM_config.simps by blast+

  from \<open>q \<in> states M\<close> have "state (CC ?c) = state ?c" by (subst config_conv_state_inv) auto
  moreover have "tapes (CC ?c) = tapes ?c"
    unfolding cc_simps TM.TM_config.simps(2) map_map
  proof (intro map_idI)
    fix tp assume "tp \<in> set tps"
    with tps_symbols have "set_of_tape tp \<subseteq> symbols M" by blast
    then show "(tape_app g_inv \<circ> tape_app g) tp = tp" by (fact tape_app_g_inv)
  qed
  ultimately show ?case by (rule TM.TM_config.equality) simp
qed

lemma config_conv_state_inv':
  "q \<in> states natM \<Longrightarrow> state (CC\<inverse> \<lparr> state = q, tapes = tps \<rparr>) = q"
  unfolding cc_simps TM.TM_config.simps(1) f_inv_def
  using f_bij by (rule bij_betw_inv_into_right)

lemma config_conv_inv': "pre_natM.wf_config c \<Longrightarrow> CC\<inverse> c = c"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>"
  from \<open>pre_natM.wf_config ?c\<close> have "q \<in> states natM"
    and tps_symbols: "list_all (\<lambda>tp. set_of_tape tp \<subseteq> symbols natM) tps"
    unfolding pre_TM.wf_config_def Let_def TM_config.simps by blast+

  from \<open>q \<in> states natM\<close> have "state (CC\<inverse> ?c) = state ?c" by (subst config_conv_state_inv') auto
  moreover have "tapes (CC\<inverse> ?c) = tapes ?c"
    unfolding cc_simps TM.TM_config.simps(2) map_map
  proof (intro map_idI)
    fix tp assume "tp \<in> set tps"
    with tps_symbols have "set_of_tape tp \<subseteq> symbols natM" by blast
    then show "(tape_app g \<circ> tape_app g_inv) tp = tp"
    proof (induction tp)
      case (fields ls m rs)
      then have l: "set ls \<subseteq> symbols natM" and m: "m \<in> symbols natM" and r: "set rs \<subseteq> symbols natM" by auto
      have *: "\<And>w. pre_natM.wf_word w \<Longrightarrow> map (\<lambda>x. g (g_inv x)) w = w" by (intro map_idI inv_g) blast
      show ?case unfolding comp_def tape_app.simps map_map unfolding *[OF l] *[OF r] inv_g[OF m] ..
    qed
  qed
  ultimately show ?case by (rule TM.TM_config.equality) simp
qed

lemma wf_natM_config: "wf_config c \<Longrightarrow> pre_natM.wf_config (C c)"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>"
  from \<open>wf_config ?c\<close> show "pre_natM.wf_config (C ?c)"
  proof (elim wf_configE, intro pre_TM.wf_configI)
    assume "state ?c \<in> states M" thus "state (C ?c) \<in> states natM"
      unfolding cc_simps natM_simps TM_config.simps by (fact imageI)
    assume "length (tapes ?c) = tape_count M" thus "length (tapes (C ?c)) = tape_count natM"
      unfolding cc_simps natM_def TM.TM.simps TM_config.simps unfolding length_map .

    assume "\<forall>tp\<in>set (tapes ?c). set_of_tape tp \<subseteq> symbols M"
    then have wf_tp: "set_of_tape tp \<subseteq> symbols M" if "tp \<in> set tps" for tp
      unfolding TM_config.simps using that by blast
    show "\<forall>tp\<in>set (tapes (C ?c)). set_of_tape tp \<subseteq> symbols natM"
    proof (intro ballI)
      fix tp
      assume "tp \<in> set (tapes (C ?c))"
      then have "tp \<in> tape_app g ` set tps" unfolding cc_simps TM_config.simps set_map .
      then obtain tp' where tp': "tp = tape_app g tp'" and "tp' \<in> set tps" by blast

      have "set_of_tape tp = g ` set_of_tape tp'"
        unfolding \<open>tp = tape_app g tp'\<close> tape_set_app[of g, OF g_Bk] ..
      also have "... \<subseteq> g ` symbols M" using \<open>tp' \<in> set tps\<close> by (intro image_mono) (fact wf_tp)
      finally show "set_of_tape tp \<subseteq> symbols natM" unfolding natM_simps .
    qed
  qed
qed

lemma natM_step_eq: "wf_config c \<Longrightarrow> C\<inverse> (natM.step (C c)) = step c"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>" let ?c' = "C ?c"
  let ?q = "f q" and ?tps = "map (tape_app g) tps"
  let ?w = "map head tps"

  from \<open>wf_config ?c\<close> have "pre_natM.wf_config (C ?c)" by (fact wf_natM_config)
  from \<open>wf_config ?c\<close> have "q \<in> states M" using wf_configD(1)[of ?c] by simp
  with f_inv have ff_q: "f_inv (f q) = q" .
  from \<open>wf_config ?c\<close> have wf_ns: "next_state M q ?w \<in> states M"
    using wf_config_state[of ?c] by (intro next_state) simp
  from \<open>wf_config ?c\<close> have wf_step: "wf_config (step ?c)" by (fact wf_config_step)

  have tp_read_eq: "map (\<lambda>tp. g_inv (head (tape_app g tp))) tps = map head tps"
  proof (intro list.map_cong0)
    fix tp assume "tp \<in> set tps"
    with \<open>wf_config ?c\<close> have "set_of_tape tp \<subseteq> symbols M" by (fast dest: wf_config_simpD(3))
    then have "head tp \<in> symbols M" by force
    then show "g_inv (head (tape_app g tp)) = head tp"
      by (induction tp) (simp add: g_inv)
  qed

  have "state (natM.step ?c') = next_state M\<^sub>\<nat> ?q (map head ?tps)"
    unfolding natM.step_def Let_def cc_simps TM_config.simps ..
  also have "... = f (next_state M q ?w)"
    unfolding natM_def TM.TM.simps map_map unfolding ff_q comp_def tp_read_eq ..
  finally have state_step: "state (natM.step ?c') = f (next_state M q ?w)" .

  have tp_upd: "tp_update (action_app g a) (tape_app g tp) = tape_app g (tp_update a tp)" for a tp
  proof (induction tp)
    case (fields ls m rs) thus ?case
    proof (induction a)
      case L thus ?case by (induction ls) auto next
      case R thus ?case by (induction rs) auto
    qed (* cases "(W \<sigma>)" and "Nop" by *) auto
  qed

  let ?na = "next_action M q ?w"
  have "tapes (natM.step ?c') = map2 tp_update (next_action M\<^sub>\<nat> ?q (map head ?tps)) ?tps"
    unfolding natM.step_def Let_def cc_simps TM_config.simps ..
  also have "... = map2 tp_update (map (action_app g) ?na) ?tps"
    unfolding natM_def TM.TM.simps map_map comp_def tp_read_eq ff_q ..
  also have "... = map (tape_app g) (map2 tp_update ?na tps)"
    unfolding zip_map2 map_map zip_map1 unfolding comp_def case_prod_beta' fst_conv snd_conv
    unfolding tp_upd ..
  finally have "tapes (natM.step ?c') = map (tape_app g) (map2 tp_update ?na tps)" .

  with state_step have natM_step: "natM.step ?c' = \<lparr>
    state = f (next_state M q ?w),
    tapes = map (tape_app g) (map2 tp_update ?na tps)
  \<rparr>" using unit_eq by (intro TM_config.equality) (unfold TM_config.simps)

  have "C\<inverse> (natM.step (C ?c)) = CC (step ?c)"  unfolding natM_step step_def Let_def TM_config.simps
    unfolding config_conv.simps ..
  then show "C\<inverse> (natM.step (C ?c)) = step ?c" unfolding config_conv_inv[OF wf_step] .
qed

lemma natM_steps_eq:
  "wf_config c \<Longrightarrow> C\<inverse> ((natM.step ^^ n) (C c)) = (step ^^ n) c"
proof (induction n)
  case 0 thus ?case unfolding funpow_0 by (fact config_conv_inv)
next
  case (Suc n)
  then have IH: "C\<inverse> ((natM.step ^^ n) (C c)) = (step ^^ n) c" .

  from \<open>wf_config c\<close> have wf: "wf_config ((step ^^ n) c)" by (fact wf_config_steps)
  from \<open>wf_config c\<close> have "pre_natM.wf_config (C c)" by (fact wf_natM_config)
  then have wf': "pre_natM.wf_config ((natM.step ^^ n) (C c))" by (fact natM.wf_config_steps)

  have "C\<inverse> ((natM.step ^^ Suc n) (C c)) = C\<inverse> (natM.step ((natM.step ^^ n) (C c)))"
    unfolding funpow.simps comp_def ..
  also have "... = C\<inverse> (natM.step (CC\<inverse> ((natM.step ^^ n) (C c))))"
    unfolding config_conv_inv'[OF wf'] ..
  also have "... = (step ^^ Suc n) c" unfolding IH natM_step_eq[OF wf] by simp
  finally show ?case .
qed

lemma natM_start_config:
  shows "C (start_config w) = natM.start_config (map g w)"
unfolding start_config_def natM.start_config_def cc_simps
    unfolding list.map map_replicate tape_app.simps g_Bk
    unfolding natM_def TM.TM.simps input_tape_app[of g, OF g_Bk] ..

lemma c_inv_state: "state (C\<inverse> c) = f_inv (state c)" for c
  by (induction c) simp

lemma natM_state_eq:
  assumes "wf_word w"
  shows "state (natM.run n (map g w)) = f (state (run n w))"
proof -
  from assms have wfc: "wf_config (start_config w)" by (rule wf_start_config)
  hence "C\<inverse> (natM.run n (map g w)) = run n w"
    using natM_start_config natM_steps_eq by metis
  thus ?thesis using c_inv_state
    by (metis assms inv_f natM.wf_config_run natM_wf_word pre_natM.wf_configD(1))
qed

lemma final_eq:
  assumes "wf_word w"
  shows "is_final (run n w) \<longleftrightarrow> natM.is_final (natM.run n (map g w))"
proof - (* using natM_state_eq[OF assms] try *)
  let ?w = "map g w" and ?c0 = "start_config w"
  from \<open>wf_word w\<close> have wf_c0: "wf_config ?c0" by (fact wf_start_config)

  have "state ((step ^^ n) ?c0) = state (C\<inverse> ((natM.step ^^ n) (C ?c0)))"
    unfolding natM_steps_eq[OF wf_c0] ..
  also have "... = f_inv (state ((natM.step ^^ n) (C ?c0)))" unfolding c_inv_state ..
  also have "... = f_inv (state (natM.run n ?w))" unfolding natM_start_config ..
  finally have run_eq: "state (run n w) = f_inv (state (natM.run n ?w))" .

  have "pre_natM.wf_config (natM.start_config (map g w))"
    using wf_natM_config[of ?c0] and wf_c0 unfolding natM_start_config[symmetric] .
  then have "pre_natM.wf_config (natM.run n ?w)" by (fact natM.wf_config_steps)
  then have wf_run_state: "state (natM.run n ?w) \<in> states natM" by blast
  then have wf_run_state': "f_inv (state (natM.run n ?w)) \<in> states M" by (fact f_inv_states)

  let ?H = "final_states M"
  have H: "final_states natM = f ` ?H" unfolding natM_def TM.TM.simps ..
  have run_state_eq: "state (run n w) \<in> ?H \<longleftrightarrow> f_inv (state (natM.run n ?w)) \<in> ?H"
    unfolding run_eq ..
  also have "... \<longleftrightarrow> f (f_inv (state (natM.run n ?w))) \<in> f ` ?H"
    using f_inj wf_run_state' state_axioms(3) by (fact inj_on_image_mem_iff[symmetric])
  also have "... \<longleftrightarrow> state (natM.run n ?w) \<in> f ` ?H" unfolding inv_f[OF wf_run_state] ..
  finally show "is_final (run n w) \<longleftrightarrow> natM.is_final (natM.run n ?w)" unfolding H .
qed

lemma natM_halts': "wf_word w \<Longrightarrow> halts w \<longleftrightarrow> natM.halts (map g w)"
  unfolding halts_altdef natM.halts_altdef using final_eq natM_wf_word by presburger

lemma natM_halts: "halts w \<Longrightarrow> natM.halts (map g w)"
  unfolding halts_altdef using natM_halts' by blast

lemma natM_accepts: "accepts w \<Longrightarrow> natM.accepts (map g w)"
proof -
  assume acc: "accepts w"
  hence wwf: "wf_word w" unfolding accepts_def ..
  hence C1: "pre_natM.wf_word (map g w)" by auto

  from acc obtain n where "state (run n w) \<in> accepting_states M" by blast
  with natM_state_eq[OF wwf, of n] have C2: "\<exists>n. state (natM.run n (map g w)) \<in> accepting_states natM"
    using natM_simps(4) by force

  from C1 C2 show ?thesis using natM.acceptsI by blast
qed

lemma natM_rejects: "rejects w \<Longrightarrow> natM.rejects (map g w)"
proof -
  assume rej: "rejects w"
  hence wwf: "wf_word w" unfolding rejects_def ..
  hence C1: "pre_natM.wf_word (map g w)" by auto

  from rej obtain n where "is_final (run n w)" and "state (run n w) \<in> rejecting_states M" by blast
  with natM_state_eq[OF wwf, of n]
  have C2: "\<exists>n. state (natM.run n (map g w)) \<in> rejecting_states natM"
    using natM_rejecting_states by force

  from C1 C2 show ?thesis using natM.rejectsI by auto
qed

lemma natM_halts_all:
  assumes "\<forall>w\<in>wf_words. halts w"
    shows "\<forall>natw\<in>pre_natM.wf_words. natM.halts natw"
proof
  fix natw assume "natw \<in> pre_natM.wf_words"
  with map_g_bij obtain w where natw: "(map g) w = natw" and wwf: "w \<in> wf_words"
    using bij_betw_obtain_preimage by force
  from assms wwf have "halts w" ..
  with natM_halts have "natM.halts (map g w)" .
  thus "natM.halts natw" unfolding natw .
qed

lemma lemmy:
  assumes "wf_lang L" and "w \<in> wf_words"
      and "map g w \<in> map g ` L"
  shows "w \<in> L"
proof -
  from assms(3) obtain w' where "w'\<in>L" and "map g w = map g w'" by blast
  with assms(1-2) map_g_inj have "w = w'"
    unfolding inj_on_def by blast
  with \<open>w'\<in>L\<close> show "w \<in> L" by simp
qed

lemma rudy:
  assumes "w \<in> wf_words" and "halts w"
    and "natM.accepts (map g w)"
  shows "accepts w"
proof (rule ccontr)
  assume "\<not> accepts w"
  with \<open>halts w\<close> have "rejects w" by blast
  hence "natM.rejects (map g w)" by (rule natM_rejects)
  with natM.acc_not_rej assms(3) show "False" by blast
qed

lemma natM_decides:
  assumes dec: "decides L"
  shows "natM.decides (map g ` L)"
  unfolding natM.decides_altdef
proof
  from dec have Lwf: "wf_lang L" ..
  show "pre_natM.wf_lang (map g ` L)" proof
    fix w assume "w \<in> map g ` L"
    then obtain w' where "w'\<in>L" and "w = map g w'" by blast
    with Lwf show "w \<in> pre_natM.wf_words" by auto
  qed

  {
  fix w assume wwf: "w \<in> pre_natM.wf_words"

  let ?w' = "map g_inv w"
  from wwf g_inv_word_wf have w'wf: "?w' \<in> wf_words" by blast
  from wwf map_g_g_inv have w'inv: "map g ?w' = w" by blast
  from wwf map_g_g_inv have winv: "map g (map g_inv w) = w" by blast

  from dec natM_halts_all have "\<forall>w\<in>pre_natM.wf_words. natM.halts w"
    unfolding decides_altdef by simp
  with wwf have C1: "natM.halts w" by simp

  have C2: "(w \<in> map g ` L) \<longleftrightarrow> natM.accepts w" proof -
  have "(w \<in> map g ` L) \<longleftrightarrow> ?w' \<in> L" proof
      assume "w \<in> map g ` L"
      with lemmy[OF Lwf, OF w'wf] w'inv show "?w' \<in> L" by blast
    next
      assume "map g_inv w \<in> L"
      hence "map g (map g_inv w) \<in> map g ` L" by blast
      then show "w \<in> map g ` L" unfolding winv .
  qed
  also have "map g_inv w \<in> L \<longleftrightarrow> accepts ?w'"
    using dec decides_altdef w'wf by simp
  also have "accepts ?w' \<longleftrightarrow> natM.accepts w"
    using natM_accepts rudy C1
    by (metis dec decides_altdef w'wf winv)
  finally show ?thesis .
  qed
  from C1 C2 have "natM.halts w \<and> (w \<in> map g ` L) = natM.accepts w" ..
  }
  thus "\<forall>w\<in>{w. set w \<subseteq> symbols M\<^sub>\<nat>}. natM.halts w \<and> (w \<in> map g ` L) = natM.accepts w" ..
qed

end \<comment> \<open>\<^locale>\<open>nat_TM\<close>\<close>

typedef (overloaded) ('a, 'b::blank) wf_TM = "{M::('a, 'b) TM. TM M}"
  using exists_wf_TM by blast

end
