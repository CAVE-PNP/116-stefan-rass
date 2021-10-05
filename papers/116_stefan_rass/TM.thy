theory TM
  imports Main "Supplementary/Misc" "Supplementary/Lists"
begin

class blank =
  fixes Bk :: 'a

instantiation nat :: blank begin
definition Bk_nat :: nat where "Bk_nat = 0"
instance ..
end

datatype 'b action = L | R | W 'b | Nop

fun symbol_of_write :: "'b action \<Rightarrow> 'b::blank" where
  "symbol_of_write (W w) = w" | "symbol_of_write _ = Bk"

lemma symbol_of_write_def: "symbol_of_write a = (case a of W w \<Rightarrow> w | _ \<Rightarrow> Bk)"
  by (induction a) auto


record 'b tape =
  left :: "'b list"
  right :: "'b list"

abbreviation "empty_tape \<equiv> \<lparr>left=[], right=[]\<rparr>"

definition [simp]: "set_of_tape tp \<equiv> set (left tp) \<union> set (right tp) \<union> {Bk}"


text\<open>TM execution begins with the head at the start of the input word.\<close>
abbreviation input_tape ("<_>\<^sub>t\<^sub>p") where "<w>\<^sub>t\<^sub>p \<equiv> \<lparr>left=[], right=w\<rparr>"

abbreviation tp_size :: "'b tape \<Rightarrow> nat" where
  "tp_size tp \<equiv> length (left tp) + length (right tp)"

fun tp_update :: "('b::blank) action \<Rightarrow> 'b tape \<Rightarrow> 'b tape" where
  "tp_update  L     \<lparr>left=[]  , right=rs  \<rparr> = \<lparr>left=[]   , right=Bk#rs\<rparr>"
| "tp_update  L     \<lparr>left=l#ls, right=rs  \<rparr> = \<lparr>left=ls   , right=l#rs \<rparr>"
| "tp_update  R     \<lparr>left=ls  , right=[]  \<rparr> = \<lparr>left=Bk#ls, right=[]   \<rparr>"
| "tp_update  R     \<lparr>left=ls  , right=r#rs\<rparr> = \<lparr>left=r#ls , right=rs   \<rparr>"
| "tp_update (W w)  \<lparr>left=ls  , right=[]  \<rparr> = \<lparr>left=ls   , right=[w]  \<rparr>"
| "tp_update (W w)  \<lparr>left=ls  , right=r#rs\<rparr> = \<lparr>left=ls   , right=w#rs \<rparr>"
| "tp_update Nop tape = tape"


lemma tp_update_set: "set_of_tape (tp_update a tp) \<subseteq> set_of_tape tp \<union> {symbol_of_write a}"
proof -
  obtain l r where expand_tp: "tp = \<lparr>left=l,right=r\<rparr>" by (rule tape.cases)
  show ?thesis unfolding expand_tp
  proof (induction a)
    case L thus ?case by (induction l) auto next
    case R thus ?case by (induction r) auto next
    case (W x) thus ?case by (induction r) auto next
    case Nop thus ?case by simp
  qed
qed


fun tp_read :: "('b :: blank) tape \<Rightarrow> 'b" where
  "tp_read \<lparr>left=_, right=[]  \<rparr> = Bk"
| "tp_read \<lparr>left=_, right=r#rs\<rparr> = r"

lemma tp_read_def: "tp_read tp = (if right tp = [] then Bk else hd (right tp))"
proof (cases "right tp")
  case Nil
  then have expand_tp: "tp = \<lparr> left=left tp, right = [] \<rparr>" by simp
  from \<open>right tp = []\<close> show ?thesis by (subst expand_tp) simp
next
  case (Cons t ts)
  then have expand_tp: "tp = \<lparr> left=left tp, right = t#ts \<rparr>" by simp
  from \<open>right tp = t # ts\<close> show ?thesis by (subst expand_tp) simp
qed

corollary tp_read_symbol: "tp_read tp \<in> set (right tp) \<union> {Bk}" unfolding tp_read_def by simp


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


\<comment> \<open>A state \<open>q\<close> in combination with a vector (\<^typ>\<open>'b list\<close>) of symbols currently under the TM-heads \<open>w\<close>,
  is considered a well-formed state w.r.t. a \<^typ>\<open>('a, 'b) TM\<close> \<open>M\<close>, iff
  \<open>q\<close> is a valid state for \<open>M\<close>,
  the number of elements of \<open>w\<close> matches the number of tapes of \<open>M\<close>, and
  all elements of \<open>w\<close> are valid symbols for \<open>M\<close> (members of \<open>M\<close>'s tape alphabet).\<close>
definition wf_state_wrt_TM :: "('a, 'b) TM \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> bool" where
  "wf_state_wrt_TM M q w \<equiv> q \<in> states M \<and> length w = tape_count M \<and> set w \<subseteq> symbols M"

lemma wf_stateI[intro]:
  "\<lbrakk>q\<in>states M; length w = tape_count M; set w \<subseteq> symbols M\<rbrakk> \<Longrightarrow> wf_state_wrt_TM M q w"
  unfolding wf_state_wrt_TM_def by blast
lemma wf_stateE[elim]:
  assumes "wf_state_wrt_TM M q w" shows "q \<in> states M" "length w = tape_count M" "set w \<subseteq> symbols M"
  using assms unfolding wf_state_wrt_TM_def by blast+

\<comment> \<open>A \<^typ>\<open>('a, 'b) TM_config\<close> \<open>c\<close> is considered well-formed w.r.t. a \<^typ>\<open>('a, 'b) TM\<close> \<open>M\<close>, iff
  the \<^const>\<open>state\<close> of \<open>c\<close> is valid for \<open>M\<close>,
  the number of \<^const>\<open>tapes\<close> of \<open>c\<close> matches the number of tapes of \<open>M\<close>, and
  all symbols on all \<^const>\<open>tapes\<close> of \<open>c\<close> are valid symbols for \<open>M\<close>.\<close>
definition wf_config_wrt_TM :: "('a, 'b :: blank) TM \<Rightarrow> ('a, 'b) TM_config \<Rightarrow> bool" where
  "wf_config_wrt_TM M c \<equiv> let q = state c; ts = tapes c in
        q \<in> states M
      \<and> length ts = tape_count M
      \<and> \<Union> (set_of_tape ` set ts) \<subseteq> symbols M"

lemma wf_configI[intro]:
  assumes "state c \<in> states M"
    and "length (tapes c) = tape_count M"
    and "\<Union> (set_of_tape ` set (tapes c)) \<subseteq> symbols M"
  shows "wf_config_wrt_TM M c"
  unfolding wf_config_wrt_TM_def Let_def using assms by blast
lemma wf_configE[elim]:
  assumes "wf_config_wrt_TM M c"
  shows "state c \<in> states M"
    and "length (tapes c) = tape_count M"
    and "\<Union> (set_of_tape ` set (tapes c)) \<subseteq> symbols M"
  using assms unfolding wf_config_wrt_TM_def Let_def by blast+


locale wf_TM =
  fixes M :: "('a, 'b::blank) TM" (structure)
  assumes at_least_one_tape: "1 \<le> tape_count M"
  and state_axioms: "finite (states M)" "start_state M \<in> states M"
                    "final_states M \<subseteq> states M" "accepting_states M \<subseteq> final_states M"
  and symbols_axioms: "finite (symbols M)" "Bk \<in> (symbols M)"
  and next_state: "\<And>q w. wf_state_wrt_TM M q w \<Longrightarrow> next_state M q w \<in> states M"
  and next_action_length: "\<And>q w. wf_state_wrt_TM M q w \<Longrightarrow>
        length (next_action M q w) = tape_count M"
  and next_write_symbol: "\<And>q w. wf_state_wrt_TM M q w \<Longrightarrow>
        symbol_of_write ` set (next_action M q w) \<subseteq> symbols M"
  and final_state: "\<And>q w. wf_state_wrt_TM M q w \<Longrightarrow> q \<in> final_states M \<Longrightarrow>
        next_state M q w = q"
  and final_action: "\<And>q w. wf_state_wrt_TM M q w \<Longrightarrow> q \<in> final_states M \<Longrightarrow>
        set (next_action M q w) \<subseteq> {Nop}"
begin

abbreviation wf_state where "wf_state \<equiv> wf_state_wrt_TM M"
abbreviation wf_config where "wf_config \<equiv> wf_config_wrt_TM M"

abbreviation wf_state_of_config ("wf'_state\<^sub>c")
  where "wf_state\<^sub>c c \<equiv> wf_state (state c) (map tp_read (tapes c))"

lemma wf_config_state: "wf_config c \<Longrightarrow> wf_state\<^sub>c c"
proof
  let ?q = "state c" and ?ts = "tapes c"
  assume "wf_config c"
  then show "?q \<in> states M" ..

  from \<open>wf_config c\<close> have "length ?ts = tape_count M" ..
  then show "length (map tp_read (tapes c)) = tape_count M" by simp

  have "set (map tp_read ?ts) \<subseteq> \<Union> (set_of_tape ` set (tapes c))"
    unfolding set_map set_of_tape_def using tp_read_symbol by blast
  also have "... \<subseteq> symbols M" using \<open>wf_config c\<close> ..
  finally show "set (map tp_read (tapes c)) \<subseteq> symbols M" .
qed

corollary wf_state_tape_count: "wf_state\<^sub>c c \<Longrightarrow> length (tapes c) = tape_count M"
  unfolding wf_state_wrt_TM_def by simp


abbreviation is_final :: "('a, 'b) TM_config \<Rightarrow> bool" where
  "is_final c \<equiv> state c \<in> final_states M"

definition step :: "('a, 'b) TM_config \<Rightarrow> ('a, 'b) TM_config" where
  "step c = (let q=state c; w=map tp_read (tapes c) in \<lparr>
      state=next_state M q w,
      tapes=map2 tp_update (next_action M q w) (tapes c)
   \<rparr>)"

abbreviation all_Nop ("Nop\<^sub>k") where "Nop\<^sub>k \<equiv> replicate (tape_count M) Nop"


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
  by (intro funpow_fixpoint) (rule final_step_fixpoint)


lemma nth_map2:
  assumes "i < length xs" and "i < length ys"
  shows "map2 f xs ys ! i = f (xs ! i) (ys ! i)"
  using assms by (subst nth_map) auto

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
      from \<open>wf_config c\<close> have "\<Union> (set_of_tape ` set ?ts) \<subseteq> symbols M" ..
      then have "\<forall>tp \<in> set ?ts. set_of_tape tp \<subseteq> symbols M" by blast
      with \<open>i < length ?ts\<close> show "set_of_tape (?ts ! i) \<subseteq> symbols M" by (rule list_ball_nth)

      have "i < length ?na" unfolding lna by (fact \<open>i < tape_count M\<close>)
      from \<open>wf_state\<^sub>c c\<close> have "symbol_of_write ` set ?na \<subseteq> symbols M" by (rule next_write_symbol)
      then have "\<forall>tp \<in> set ?na. symbol_of_write tp \<in> symbols M" by blast
      with \<open>i < length ?na\<close> show "{symbol_of_write (?na ! i)} \<subseteq> symbols M"
        by (intro list_ball_nth) blast+
    qed
    finally show "set_of_tape (?ts' ! i) \<subseteq> symbols M" .
  qed
  then have "\<forall>tp \<in> set ?ts'. set_of_tape tp \<subseteq> symbols M" unfolding all_set_conv_all_nth .
  then show "\<Union> (set_of_tape ` set ?ts') \<subseteq> symbols M" by blast
qed

corollary wf_config_steps: "wf_config c \<Longrightarrow> wf_config ((step^^n) c)"
  using wf_config_step by (induction n) auto


definition start_config :: "'b list \<Rightarrow> ('a, 'b) TM_config" where [simp]:
  "start_config w = \<lparr>
    state = start_state M,
    tapes = <w>\<^sub>t\<^sub>p # replicate (tape_count M - 1) empty_tape
  \<rparr>"

abbreviation "run n w \<equiv> (step^^n) (start_config w)"


lemma wf_start_config: "set w \<subseteq> symbols M \<Longrightarrow> wf_config (start_config w)"
proof
  show "state (start_config w) \<in> states M" using state_axioms(2) by simp
  show "length (tapes (start_config w)) = tape_count M" using at_least_one_tape by simp

  assume "set w \<subseteq> symbols M"
  have "set (tapes (start_config w)) \<subseteq> {<w>\<^sub>t\<^sub>p, empty_tape}" by fastforce
  moreover have "set_of_tape empty_tape = {Bk}" by simp
  moreover have "set_of_tape <w>\<^sub>t\<^sub>p = set w \<union> {Bk}" by simp
  ultimately have "\<Union> (set_of_tape ` set (tapes (start_config w))) \<subseteq> set w \<union> {Bk}" by blast
  also have "... \<subseteq> symbols M" using \<open>set w \<subseteq> symbols M\<close> symbols_axioms(2) by blast
  finally show "\<Union> (set_of_tape ` set (tapes (start_config w))) \<subseteq> symbols M" .
qed

corollary wf_config_run: "set w \<subseteq> symbols M \<Longrightarrow> wf_config (run n w)"
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

end \<comment> \<open>\<^locale>\<open>wf_TM\<close>\<close>

subsection \<open>Composition of Turing Machines\<close>

\<comment> \<open>Let M1 be a k1-tape TM, M2 a k2-tape TM. We define the composition of M1 and M2
    as a (k1+k2-1)-tape TM. First M1 operates on the tapes 0,1,...,k1-1.
    When M1 finishes, M2 operates on the tapes 0,k1,k1+1,...,k1+k2-2.
    Therefore, M1 is expected to write its output (M2's input) on the zeroth tape.\<close>

fun tm_comp :: "('a1, 'b::blank) TM \<Rightarrow> ('a2, 'b) TM \<Rightarrow> ('a1+'a2, 'b) TM"
  ("_ |+| _" [0, 0] 100)
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
                                   hd a2 # replicate (tape_count M1 - 1) Nop @ tl a2
                        )
  \<rparr>)"

lemma "wf_TM M1 \<Longrightarrow> wf_TM M2 \<Longrightarrow> wf_TM (M1 |+| M2)"
  sorry


subsection \<open>Hoare Rules\<close>

type_synonym ('a, 'b) assert = "('a, 'b) TM_config \<Rightarrow> bool"

definition (in wf_TM) hoare_halt :: "('a, 'b) assert \<Rightarrow> ('a, 'b) assert \<Rightarrow> bool" where
  "hoare_halt P Q \<longleftrightarrow> (\<forall>c. P c \<longrightarrow>
    (\<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn))"

lemma (in wf_TM) hoare_haltI[intro]:
  fixes P Q
  assumes "\<And>c. P c \<Longrightarrow>
             \<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn"
  shows "hoare_halt P Q"
  unfolding hoare_halt_def using assms by blast

lemma (in wf_TM) hoare_haltE[elim]:
  fixes c
  assumes "P c"
      and "hoare_halt P Q"
    obtains n where "is_final ((step^^n) c)" and "Q ((step^^n) c)"
  using assms
  unfolding hoare_halt_def by meson


\<comment> \<open>Hide single letter constants outside this theory to avoid confusion.
  \<open>(open)\<close> allows access for fully or partially qualified names
  such as \<^const>\<open>action.L\<close>, \<^const>\<open>TM.action.L\<close> or \<^const>\<open>TM.L\<close>\<close>
hide_const (open) "TM.action.L" "TM.action.R" "TM.action.W"

end