theory TM_Hoare (* TODO find better name. maybe "TM_Computation" *)
  imports TM
begin

subsection\<open>Computation on TMs\<close>

text\<open>We follow the convention that TMs read their input from the first tape
  and write their output to the last tape.\<close>
  (* TODO is this *the* standard convention? what about output on the first tape? *)

context TM_abbrevs
begin

subsubsection\<open>Input\<close>

text\<open>TM execution begins with the head at the start of the input word.
  The remaining symbols of the word can be reached by shifting the tape head to the right.
  The end of the word is reached when the tape head first encounters \<^const>\<open>blank_symbol\<close>.\<close>

fun input_tape :: "'s word \<Rightarrow> 's tape" ("<_>\<^sub>t\<^sub>p") where
  "<[]>\<^sub>t\<^sub>p = \<langle>\<rangle>"
| "<x # xs>\<^sub>t\<^sub>p = \<langle>|Some x|map Some xs\<rangle>"

lemma input_tape_map[simp]: "map_tape f <w>\<^sub>t\<^sub>p = <map f w>\<^sub>t\<^sub>p" by (induction w) auto

lemma input_tape_left[simp]: "left <w>\<^sub>t\<^sub>p = []" by (induction w) auto
lemma input_tape_right: "w \<noteq> [] \<longleftrightarrow> head <w>\<^sub>t\<^sub>p # right <w>\<^sub>t\<^sub>p = map Some w" by (induction w) auto

lemma input_tape_def: "<w>\<^sub>t\<^sub>p = (if w = [] then \<langle>\<rangle> else \<langle>|Some (hd w)|map Some (tl w)\<rangle>)"
  by (induction w) auto

lemma input_tape_size: "w \<noteq> [] \<Longrightarrow> tape_size <w>\<^sub>t\<^sub>p = length w"
  unfolding tape_size_def by (induction w) auto


lemma input_tape_inj[dest]: "<w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p \<Longrightarrow> w = w'"
proof (cases "w = []"; cases "w' = []")
  show "w = [] \<Longrightarrow> w' = [] \<Longrightarrow> w = w'" by blast

  have *: False if "<w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p" and "w = []" and "w' \<noteq> []" for w w' :: "'x list"
  proof -
    from \<open><w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p\<close> have "<w'>\<^sub>t\<^sub>p = \<langle>\<rangle>" unfolding \<open>w = []\<close> by simp
    with \<open>w' \<noteq> []\<close> show False unfolding input_tape_def by auto
  qed

  assume "<w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p"
  from \<open><w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p\<close> show "w = [] \<Longrightarrow> w' \<noteq> [] \<Longrightarrow> w = w'" using * by blast
  from \<open><w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p\<close>[symmetric] show "w \<noteq> [] \<Longrightarrow> w' = [] \<Longrightarrow> w = w'" using * by blast

  assume "w \<noteq> []" and "w' \<noteq> []"

  with \<open><w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p\<close> have "\<langle>|Some (hd w)|map Some (tl w)\<rangle> = \<langle>|Some (hd w')|map Some (tl w')\<rangle>"
    unfolding input_tape_def by argo
  then have "hd w = hd w'" and "tl w = tl w'"
    unfolding tape.inject option.inject inj_map_eq_map[OF inj_Some] by blast+
  with \<open>w \<noteq> []\<close> and \<open>w' \<noteq> []\<close> show "w = w'" by (intro list.expand) blast+
qed

corollary input_tape_cong[cong]: "<w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p \<longleftrightarrow> w = w'" by blast

lemma input_tape_set[simp]: "set_tape <w>\<^sub>t\<^sub>p = set w" by (induction w) auto

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>


context TM
begin

text\<open>By convention, the initial configuration has the input word on the first tape
  with all other tapes being empty.\<close>

definition initial_config :: "'s list \<Rightarrow> ('q, 's) TM_config"
  where "initial_config w = TM_config q\<^sub>0 (<w>\<^sub>t\<^sub>p # empty_tape \<up> (k - 1))"

abbreviation "c\<^sub>0 \<equiv> initial_config"


lemma init_conf_len: "length (tapes (initial_config w)) = k"
  unfolding initial_config_def using at_least_one_tape by force
lemma init_conf_state: "state (initial_config w) = q\<^sub>0"
  unfolding initial_config_def by simp
lemmas init_conf_simps[simp] = init_conf_len init_conf_state

abbreviation "wf_input w \<equiv> set w \<subseteq> \<Sigma>\<^sub>i\<^sub>n"

lemma wf_initial_config[intro]: "wf_input w \<Longrightarrow> wf_config (initial_config w)"
proof (intro wf_configI)
  assume "set w \<subseteq> \<Sigma>\<^sub>i\<^sub>n"
  then show "list_all (\<lambda>tp. set_tape tp \<subseteq> \<Sigma>\<^sub>i\<^sub>n) (tapes (c\<^sub>0 w))"
    unfolding initial_config_def TM_config.sel list.pred_inject(2) by (intro conjI) (simp, force)
qed simp_all

lemma (in typed_TM) wf_initial_config[intro]: "wf_config (initial_config w)" by force


subsubsection\<open>Running a TM Program\<close>

definition run :: "nat \<Rightarrow> 's list \<Rightarrow> ('q, 's) TM_config"
  where "run n w \<equiv> steps n (initial_config w)"

lemma run_initial_config[simp]: "run 0 w = c\<^sub>0 w"
  unfolding run_def by simp

corollary wf_config_run[intro, simp]: "wf_input w \<Longrightarrow> wf_config (run n w)" unfolding run_def by blast
corollary (in typed_TM) wf_config_run[intro!, simp]: "wf_config (run n w)" by simp


corollary run_tapes_len[simp]: "length (tapes (run n w)) = k" by (simp add: run_def steps_l_tps)
corollary run_tapes_non_empty[simp, intro]: "tapes (run n w) \<noteq> []"
  using at_least_one_tape by (fold length_0_conv) simp

corollary steps_run[simp]: "steps n (run m w) = run (m + n) w"
  unfolding run_def add_ac[of m n] funpow_add comp_def ..

corollary run_final_mono[dest]:
  assumes "is_final (run n w)"
    and "n \<le> m"
  shows "is_final (run m w)"
using assms unfolding run_def by (fact final_mono)

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsection \<open>Hoare Rules\<close>

type_synonym ('q, 's) assert = "('q, 's) TM_config \<Rightarrow> bool"

definition hoare_halt :: "('q, 's) assert \<Rightarrow> ('q, 's) TM \<Rightarrow> ('q, 's) assert \<Rightarrow> bool"
  where "hoare_halt P M Q \<equiv>
    (\<forall>c. P c \<longrightarrow> (\<exists>n. let cn = TM.steps M n c in TM.is_final M cn \<and> Q cn))"

lemma hoare_haltI[intro]:
  fixes P Q
  assumes "\<And>c. P c \<Longrightarrow> \<exists>n. TM.is_final M (TM.steps M n c) \<and> Q (TM.steps M n c)"
  shows "hoare_halt P M Q"
  unfolding hoare_halt_def Let_def using assms by blast

lemma hoare_haltE[elim]:
  fixes c
  assumes "hoare_halt P M Q"
    and "P c"
  obtains n where "TM.is_final M (TM.steps M n c)" and "Q (TM.steps M n c)"
  using assms
  unfolding hoare_halt_def Let_def by blast

lemma hoare_haltE2[elim]:
  fixes c
  assumes "hoare_halt P M Q"
    and "P c"
  shows "\<exists>n. TM.is_final M (TM.steps M n c) \<and> Q (TM.steps M n c)"
  using assms unfolding hoare_halt_def Let_def by blast

lemma hoare_contr:
  assumes "hoare_halt P M (\<lambda>_. False)" and "P c"
  shows "False"
  using assms by (rule hoare_haltE)

lemma hoare_imp[elim]:
  assumes "hoare_halt P M Q"
    and P': "\<And>c. P' c \<Longrightarrow> P c"
    and Q': "\<And>c. Q c \<Longrightarrow> Q' c"
  shows "hoare_halt P' M Q'"
proof (intro hoare_haltI)
  fix c assume "P' c"
  with P' and \<open>hoare_halt P M Q\<close> obtain n
    where f: "TM.is_final M (TM.steps M n c)" and Q: "Q (TM.steps M n c)" by blast
  with Q' show "\<exists>n. TM.is_final M (TM.steps M n c) \<and> Q' (TM.steps M n c)" by blast
qed


lemma hoare_true: "hoare_halt P M Q \<Longrightarrow> hoare_halt P M (\<lambda>_. True)" by fast

lemma hoare_and[intro]:
  assumes h1: "hoare_halt P M Q1"
    and h2: "hoare_halt P M Q2"
  shows "hoare_halt P M (\<lambda>c. Q1 c \<and> Q2 c)"
proof
  fix c assume "P c"
  from h1 and \<open>P c\<close> obtain n1
    where fn1: "TM.is_final M (TM.steps M n1 c)" and q1: "Q1 (TM.steps M n1 c)" by (rule hoare_haltE)
  from h2 and \<open>P c\<close> obtain n2
    where fn2: "TM.is_final M (TM.steps M n2 c)" and q2: "Q2 (TM.steps M n2 c)" by (rule hoare_haltE)

  define n::nat where "n \<equiv> max n1 n2"
  hence "n1 \<le> n" "n2 \<le> n" by simp+
  let ?cn = "TM.steps M n c"
  from fn1 and \<open>n1 \<le> n\<close> have steps1: "?cn = TM.steps M n1 c" by (fact TM.final_le_steps)
  from fn2 and \<open>n2 \<le> n\<close> have steps2: "?cn = TM.steps M n2 c" by (fact TM.final_le_steps)
  from fn1 q1 q2 have "TM.is_final M ?cn \<and> Q1 ?cn \<and> Q2 ?cn" by (fold steps1 steps2) blast
  then show "\<exists>n. TM.is_final M (TM.steps M n c) \<and> Q1 (TM.steps M n c) \<and> Q2 (TM.steps M n c)" ..
qed


definition (in TM) "on_input w \<equiv> (\<lambda>c. c = initial_config w)"

lemma on_inputI[intro, simp]: "TM.on_input M w (TM.initial_config M w)"
  unfolding TM.on_input_def by blast


definition (in TM) halts_config :: "('q, 's) TM_config \<Rightarrow> bool"
  where "halts_config c \<equiv> hoare_halt (\<lambda>x. x = c) M (\<lambda>_. True)"

lemma halts_config_altdef: "TM.halts_config M c \<longleftrightarrow> (\<exists>n. TM.is_final M (TM.steps M n c))"
  unfolding TM.halts_config_def by fast

mk_ide (in -) halts_config_altdef |intro halts_confI[intro]| |dest halts_confD[dest]|


lemma (in TM) hoare_halt_init_conf:
  "hoare_halt (TM.on_input M w) M P \<longleftrightarrow> (\<exists>n. let cn = run n w in is_final cn \<and> P cn)"
  unfolding hoare_halt_def TM.on_input_def run_def by blast


definition (in TM) halts :: "'s list \<Rightarrow> bool"
  where "halts w \<equiv> halts_config (initial_config w)"
declare TM.halts_def[simp]

lemma halts_altdef: "TM.halts M w \<longleftrightarrow> hoare_halt (TM.on_input M w) M (\<lambda>_. True)"
  unfolding TM.halts_def TM.halts_config_def TM.on_input_def ..

lemma halts_altdef2: "TM.halts M w \<longleftrightarrow> (\<exists>n. TM.is_final M (TM.run M n w))"
  by (simp add: TM.run_def halts_config_altdef)


lemma haltsI[intro]:
  assumes "\<exists>n. TM.is_final M (TM.run M n w)"
  shows "TM.halts M w"
  using assms by (simp add: TM.run_def halts_config_altdef)

lemma haltsD[dest]: "TM.halts M w \<Longrightarrow> \<exists>n. TM.is_final M (TM.run M n w)"
  unfolding TM.halts_def TM.run_def by blast


lemma hoare_halt_neg:
  assumes "\<not> hoare_halt (TM.on_input M w) M Q"
    and "TM.halts M w"
  shows "hoare_halt (TM.on_input M w) M (\<lambda>tp. \<not> Q tp)"
  using assms unfolding hoare_halt_def TM.halts_def Let_def TM.on_input_def by fast

lemma halt_inj:
  assumes "hoare_halt (TM.on_input M w) M (\<lambda>c. f c = x)"
      and "hoare_halt (TM.on_input M w) M (\<lambda>c. f c = y)"
    shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have *: "a = x \<and> a = y \<longleftrightarrow> False" for a by blast

  from assms have "hoare_halt (TM.on_input M w) M (\<lambda>c. f c = x \<and> f c = y)" by (rule hoare_and)
  then have "hoare_halt (TM.on_input M w) M (\<lambda>_. False)" unfolding * .
  then show False by blast
qed


subsection\<open>Output\<close>

context TM
begin

text\<open>By convention, the \<^emph>\<open>output\<close> of a TM is found on its last tape
  when the computation has reached its end.
  The tape head is positioned over the first symbol of the word,
  and the \<open>n\<close>-th symbol of the word is reached by moving the tape head \<open>n\<close> cells to the right.
  As with input, the \<^const>\<open>blank_symbol\<close> is not part of the output,
  so only the symbols up to the first blank will be considered output.\<close> (* TODO does this make sense *)

definition output_of :: "('q, 's) TM_config \<Rightarrow> 's list"
  where "output_of c = (let o_tp = last (tapes c) in
    case head o_tp of Bk \<Rightarrow> [] | Some h \<Rightarrow> h # the (those (takeWhile (\<lambda>s. s \<noteq> Bk) (right o_tp))))"

lemma out_config_simps[simp, intro]: "last (tapes c) = <w>\<^sub>t\<^sub>p \<Longrightarrow> output_of c = w"
  unfolding output_of_def by (induction w) (auto simp add: takeWhile_map)

text\<open>The requirement that the output conforms to the input standard should simplify some parts.
  It is possible to construct a TM that produces clean output, simply by adding another tape.\<close>

definition "clean_output c \<equiv> \<exists>w. last (tapes c) = <w>\<^sub>t\<^sub>p"

lemma clean_outputD[dest]: "clean_output c \<Longrightarrow> output_of c = w \<Longrightarrow> last (tapes c) = <w>\<^sub>t\<^sub>p"
  unfolding clean_output_def by force

lemma clean_output_alt: "clean_output c \<and> output_of c = w \<longleftrightarrow> last (tapes c) = <w>\<^sub>t\<^sub>p"
  unfolding clean_output_def by force


(* TODO document, clean up *)

definition (in -) [simp]: "hoare_run w M P \<equiv> hoare_halt (TM.on_input M w) M P"

definition "computes_word w w' \<equiv> hoare_run w M (\<lambda>c. clean_output c \<and> output_of c = w')"

definition "computes f \<equiv> \<forall>w. computes_word w (f w)"
declare (in -) TM.computes_def[simp]

lemma hoare_run_halts[dest]: "hoare_run w M P \<Longrightarrow> halts w"
  unfolding halts_altdef hoare_run_def by (rule hoare_true)

lemma computes_word_halts[dest]: "computes_word w w' \<Longrightarrow> halts w"
  unfolding computes_word_def by (rule hoare_run_halts)

lemma computes_halts[dest]: "computes f \<Longrightarrow> halts w"
  unfolding halts_altdef2 by auto


definition "config_time c \<equiv> LEAST n. is_final (steps n c)"

lemma steps_conf_time[intro, simp]:
  assumes "is_final (steps n c)"
  shows "steps (config_time c) c = steps n c"
proof -
  from assms have "is_final (steps (config_time c) c)" unfolding config_time_def by (rule LeastI)
  then show ?thesis using assms by (rule final_steps_rev)
qed

lemma conf_time_lessD[dest, elim]: "n < config_time c \<Longrightarrow> \<not> is_final (steps n c)"
  unfolding config_time_def by (rule not_less_Least)

lemma conf_time_geD[dest, elim]:
  assumes "n \<ge> config_time c"
    and "halts_config c"
  shows "is_final (steps n c)"
proof -
  from assms(2) have "is_final (steps (LEAST n. is_final (steps n c)) c)"
    unfolding halts_config_altdef by (rule LeastI_ex)
  with assms(1) show ?thesis unfolding config_time_def by blast
qed

lemma conf_time_geI[intro]: "is_final (steps n c) \<Longrightarrow> config_time c \<le> n"
  unfolding config_time_def run_def by (fact Least_le)

lemma conf_time_ge_iff[intro]: "halts_config c \<Longrightarrow> is_final (steps n c) \<longleftrightarrow> n \<ge> config_time c"
  by blast

lemma conf_time_less_rev[intro]: "halts_config c \<Longrightarrow> \<not> is_final (steps n c) \<Longrightarrow> n < config_time c"
  by (subst (asm) conf_time_ge_iff) auto

lemma conf_time_finalI[intro]: "halts_config c \<Longrightarrow> is_final (steps (config_time c) c)"
  using conf_time_ge_iff by blast

lemma conf_time0[simp, intro]: "is_final c \<Longrightarrow> config_time c = 0" unfolding config_time_def by simp


lemma conf_time_steps_finalI: "\<exists>n. is_final (steps n c) \<and> P (steps n c) \<Longrightarrow>
  is_final (steps (config_time c) c) \<and> P (steps (config_time c) c)" by force

lemma conf_time_steps_final_iff:
  "(\<exists>n. is_final (steps n c) \<and> P (steps n c)) \<longleftrightarrow>
  (is_final (steps (config_time c) c) \<and> P (steps (config_time c) c))"
  by (intro iffI conf_time_steps_finalI) blast+


definition "time w \<equiv> config_time (initial_config w)"
declare (in -) TM.time_def[simp]

abbreviation "compute w \<equiv> run (time w) w"

lemma time_altdef: "time w = (LEAST n. is_final (run n w))"
  unfolding TM.run_def using config_time_def by simp

lemma time_leI[intro]:
  "is_final (run n w) \<Longrightarrow> time w \<le> n"
  unfolding run_def time_def by (rule conf_time_geI)

lemma computeI:
  assumes "\<exists>n. is_final (run n w) \<and> P (run n w)"
  shows "P (compute w)"
proof -
  from assms have "halts w" by blast
  then have "is_final (compute w)" unfolding run_def by auto
  from assms obtain n where "is_final (run n w)" and "P (run n w)" by blast
  with \<open>is_final (compute w)\<close> have "run n w = compute w" unfolding run_def by blast
  with \<open>P (run n w)\<close> show ?thesis by argo
qed


lemma final_steps_config_time[dest]:
  "is_final (steps n c) \<Longrightarrow> steps n c = steps (config_time c) c" by blast

lemma final_run_time[intro]: "is_final (run n w) \<Longrightarrow> run n w = compute w"
  unfolding time_def run_def by blast

corollary halts_compute_final[intro]: "halts w \<Longrightarrow> is_final (compute w)"
  unfolding run_def halts_def time_def by (fact conf_time_finalI)

lemma hoare_run_altdef: "hoare_run w M P \<longleftrightarrow> halts w \<and> P (compute w)"
proof (rule iffI)
  assume "hoare_run w M P"
  then have "\<exists>n. let cn = run n w in is_final cn \<and> P cn"
    unfolding hoare_run_def hoare_halt_init_conf .
  then obtain n where "is_final (run n w)" and "P (run n w)" unfolding Let_def by blast
  then show "halts w \<and> P (compute w)" using computeI by blast
next
  assume "halts w \<and> P (compute w)"
  then have "halts w" and "P (compute w)" by blast+
  from \<open>halts w\<close> have "is_final (compute w)" by blast
  with \<open>P (compute w)\<close> show "hoare_run w M P"
    unfolding hoare_run_def hoare_halt_init_conf Let_def by blast
qed

lemma hoare_run_run[dest]: "hoare_run w M P \<Longrightarrow> P (compute w)" unfolding hoare_run_altdef by blast

lemma run_hoare_run[simp]: "halts w \<Longrightarrow> hoare_run w M P = P (compute w)"
  unfolding hoare_run_altdef by blast


lemma computes_word_output[dest]:
  assumes "computes_word w w'"
  shows "last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p"
proof -
  let ?c = "run (time w) w"
  from assms have "clean_output ?c" and "output_of ?c = w'" unfolding computes_word_def by blast+
  then obtain x where "last (tapes ?c) = <x>\<^sub>t\<^sub>p" unfolding clean_output_def by blast
  then have "output_of ?c = x" by blast
  with \<open>output_of ?c = w'\<close> have "x = w'" by blast
  with \<open>last (tapes ?c) = <x>\<^sub>t\<^sub>p\<close> show ?thesis by blast
qed

lemma computes_output: "computes f \<Longrightarrow> last (tapes (compute w)) = <f w>\<^sub>t\<^sub>p"
  by (intro computes_word_output) simp

lemma output_computes_word:
  assumes "halts w"
    and "last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p"
  shows "computes_word w w'"
  unfolding computes_word_def run_hoare_run[OF \<open>halts w\<close>] clean_output_alt by (fact assms(2))


lemma config_time_offset:
  fixes c0
  defines "n \<equiv> config_time c0"
  assumes "halts_config c0"
  shows "config_time (steps n1 c0) = n - n1"
proof (cases "is_final (steps n1 c0)")
  assume f: "is_final (steps n1 c0)"
  then have "n1 \<ge> n" unfolding n_def by blast
  with f show ?thesis unfolding n_def by simp
next
  assume nf: "\<not> is_final (steps n1 c0)"

  let ?N = "{n2. is_final (steps n2 (steps n1 c0))}"

  have "{n. is_final (steps n c0)} = {n. \<exists>n2. n = n1 + n2 \<and> is_final (steps n2 (steps n1 c0))}"
    (is "{n. ?lhs n} = {n. ?rhs n}")
  proof (rule sym, intro Collect_eqI iffI)
    fix n assume "?lhs n"
    with nf have "n > n1" by blast
    then have "\<exists>n2. n = n1 + n2" by (intro le_Suc_ex less_imp_le_nat)
    then obtain n2 where "n = n1 + n2" ..
    from \<open>?lhs n\<close> have "is_final (steps n2 (steps n1 c0))" unfolding \<open>n = n1 + n2\<close> by simp
    with \<open>n = n1 + n2\<close> show "?rhs n" by blast
  next
    fix n assume "?rhs n"
    then obtain n2 where "n = n1 + n2" and "is_final (steps n2 (steps n1 c0))" by blast
    then show "?lhs n" by simp
  qed
  then have *: "{n. is_final (steps n c0)} = (\<lambda>n2. n1 + n2) ` ?N" unfolding image_Collect .

  have "n = (LEAST n. is_final (steps n c0))" unfolding n_def config_time_def ..
  also have "... = (LEAST n. n \<in> {n. is_final (steps n c0)})" by simp
  also have "... = n1 + (LEAST n. is_final (steps n (steps n1 c0)))" unfolding *
  proof (subst Least_mono, unfold mem_Collect_eq)
    show "mono (\<lambda>n2. n1 + n2)" by (intro monoI add_left_mono)

    let ?n = "config_time c0" let ?n2 = "?n - n1"
    have *: "x \<in> ?N \<longleftrightarrow> x \<ge> ?n2" for x
      unfolding mem_Collect_eq steps_plus le_diff_conv add.commute[of x n1]
      using \<open>halts_config c0\<close> by (fact conf_time_ge_iff)
    then show "\<exists>n\<in>?N. \<forall>n'\<in>?N. n \<le> n'" by blast
  qed blast
  also have "... = n1 + config_time (steps n1 c0)" unfolding config_time_def ..
  finally show ?thesis by presburger
qed

lemma computes_word_altdef: "computes_word w w' \<longleftrightarrow> halts w \<and> last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p"
  unfolding computes_word_def
  using TM.clean_output_alt TM.hoare_run_altdef  by blast

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>

lemma config_time_eqI[intro]:
  assumes "TM.halts_config M1 c1"
    and "\<And>n. TM.is_final M1 (TM.steps M1 (n1 + n) c1) \<longleftrightarrow> TM.is_final M2 (TM.steps M2 n c2)"
  shows "TM.config_time M1 c1 - n1 = TM.config_time M2 c2"
proof -
  from \<open>TM.halts_config M1 c1\<close> have "TM.config_time M1 c1 - n1 = TM.config_time M1 (TM.steps M1 n1 c1)"
    by (subst TM.config_time_offset) auto
  also have "... = TM.config_time M2 c2" unfolding TM.config_time_def TM.steps_plus unfolding assms ..
  finally show ?thesis .
qed

lemma time_eqI[intro]:
  assumes "TM.halts M1 w1"
    and "\<And>n. TM.is_final M1 (TM.run M1 (n1 + n) w1) \<longleftrightarrow> TM.is_final M2 (TM.run M2 n w2)"
  shows "TM.time M1 w1 - n1 = TM.time M2 w2"
  using assms unfolding TM.time_def TM.run_def TM.halts_def by (fact config_time_eqI)

locale Rej_TM =
  fixes q0 :: 'q and s :: 's and M :: "('q, 's) TM"
  defines "M \<equiv> rejecting_TM q0 s"
begin
sublocale TM M .

lemma M_rec: "M_rec = rejecting_TM_rec q0 s" using Abs_TM_inverse rejecting_TM_valid
  unfolding rejecting_TM_def M_def by fast
lemmas M_fields = TM_fields_defs[unfolded M_rec rejecting_TM_rec_def TM_record.simps]
lemmas [simp] = M_fields(1-6)

lemma rej_tm_time: "time w = 0" by simp
end

subsection\<open>Deciding Languages\<close>
context TM begin

definition accepts :: "'s list \<Rightarrow> bool"
  where "accepts w \<equiv> state (compute w) \<in> accepting_states"

definition rejects :: "'s list \<Rightarrow> bool"
  where "rejects w \<equiv> state (compute w) \<in> rejecting_states"

lemma halts_iff: "halts w \<longleftrightarrow> accepts w \<or> rejects w"
  unfolding accepts_def rejects_def
  using is_final_altdef by blast

lemma acc_not_rej: "accepts w \<Longrightarrow> \<not> rejects w"
  unfolding accepts_def rejects_def rejecting_states_def by simp

lemma rejects_altdef:
  "rejects w = (halts w \<and> \<not> accepts w)"
  using acc_not_rej halts_iff by blast

definition decides_word :: "'s lang \<Rightarrow> 's list \<Rightarrow> bool"
  where decides_def[simp]: "decides_word L w \<equiv> (w \<in> L \<longleftrightarrow> accepts w) \<and> (w \<notin> L \<longleftrightarrow> rejects w)"

lemma decides_halts: "decides_word L w \<Longrightarrow> halts w"
  using halts_iff by auto

abbreviation decides :: "'s lang \<Rightarrow> bool"
  where "decides L \<equiv> \<forall>w. decides_word L w"

corollary decides_halts_all: "decides L \<Longrightarrow> \<forall>w. halts w"
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

end

(* Note: having this much code commented out leads to errors when importing this theory sometimes.
         (Isabelle reports this theory as broken)
         My guess is that Isabelle tries to verify the theory, but does not look ahead far enough
         to find the end-comment, and therefore concludes that the theory is broken. *)

(*
definition "input_assert (P::'s list \<Rightarrow> bool) \<equiv> \<lambda>c::('q, 's::finite) TM_config.
              let tp = hd (tapes c) in P (head tp # right tp) \<and> left tp = []"

lemma hoare_comp:
  fixes M1 :: "('q1, 's) TM" and M2 :: "('q2, 's) TM"
    and Q :: "'s list \<Rightarrow> bool"
  assumes "TM.hoare_halt M1 (input_assert P) (input_assert Q)"
      and "TM.hoare_halt M2 (input_assert Q) (input_assert S)"
    shows "TM.hoare_halt (M1 |+| M2) (input_assert P) (input_assert S)"
sorry


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
  shows "P w \<longleftrightarrow> input_assert P (initial_config w)"
proof (cases "w = []")
  case True
  then show ?thesis
    unfolding input_assert_def initial_config_def apply simp
    using good_assert_single[OF assms] ..
next
  case False
  then show ?thesis
    unfolding input_assert_def initial_config_def apply simp
    using input_tape_right by metis
qed

lemma init_input: "init w c \<Longrightarrow> input w c"
  unfolding initial_config_def by simp

lemma init_state_initial_state: "init w c \<Longrightarrow> state c = initial_state M"
  unfolding initial_config_def by simp

end

subsection\<open>TM Languages\<close>

definition TM_lang :: "('q, 's) TM \<Rightarrow> 's lang" ("L'(_')")
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
*)
end
