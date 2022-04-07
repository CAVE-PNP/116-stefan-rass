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


lemma input_tape_cong[dest]: "<w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p \<Longrightarrow> w = w'"
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

corollary input_tape_cong'[simp]: "<w>\<^sub>t\<^sub>p = <w'>\<^sub>t\<^sub>p \<longleftrightarrow> w = w'" by blast

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>


context TM
begin

text\<open>By convention, the initial configuration has the input word on the first tape
  with all other tapes being empty.\<close>

definition initial_config :: "'s list \<Rightarrow> ('q, 's) TM_config"
  where "initial_config w = conf q\<^sub>0 (<w>\<^sub>t\<^sub>p # empty_tape \<up> (k - 1))"

abbreviation "c\<^sub>0 \<equiv> initial_config"

lemma wf_initial_config[intro]: "wf_config (initial_config w)"
  unfolding initial_config_def using at_least_one_tape by simp

lemma init_conf_len: "length (tapes (initial_config w)) = k" by blast
lemma init_conf_state: "state (initial_config w) = q\<^sub>0" unfolding initial_config_def by simp
lemmas init_conf_simps[simp] = init_conf_len init_conf_state


subsubsection\<open>Running a TM Program\<close>

definition run :: "nat \<Rightarrow> 's list \<Rightarrow> ('q, 's) TM_config"
  where "run n w \<equiv> steps n (initial_config w)"
declare (in -) TM.run_def[simp]

corollary wf_config_run: "wf_config (run n w)" by auto

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsection \<open>Hoare Rules\<close>

type_synonym ('q, 's) assert = "('q, 's) TM_config \<Rightarrow> bool"

definition hoare_halt :: "('q, 's::finite) assert \<Rightarrow> ('q, 's) TM \<Rightarrow> ('q, 's) assert \<Rightarrow> bool"
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

mk_ide halts_config_altdef |intro halts_confI[intro]| |dest halts_confD[dest]|


definition (in TM) halts :: "'s::finite list \<Rightarrow> bool"
  where "halts w \<equiv> halts_config (initial_config w)"
declare TM.halts_def[simp]

lemma halts_altdef: "TM.halts M w \<longleftrightarrow> hoare_halt (TM.on_input M w) M (\<lambda>_. True)"
  unfolding TM.halts_def TM.halts_config_def TM.on_input_def ..

lemma halts_altdef2: "TM.halts M w \<longleftrightarrow> (\<exists>n. TM.is_final M (TM.run M n w))"
  by (simp add: halts_config_altdef)


lemma haltsI[intro]:
  assumes "\<exists>n. TM.is_final M (TM.run M n w)"
  shows "TM.halts M w"
  using assms by (simp add: halts_config_altdef)

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

  from hoare_and assms have "hoare_halt (TM.on_input M w) M (\<lambda>c. f c = x \<and> f c = y)".
  then have "hoare_halt (TM.on_input M w) M (\<lambda>_. False)" unfolding * .
  then show False by blast
qed


subsubsection\<open>Output\<close>

context TM
begin

text\<open>By convention, the \<^emph>\<open>output\<close> of a TM is found on its last tape
  when the computation has reached its end.
  The tape head is positioned over the first symbol of the word,
  and the \<open>n\<close>-th symbol of the word is reached by moving the tape head \<open>n\<close> cells to the right.
  As with input, the \<^const>\<open>blank_symbol\<close> is not part of the output,
  so only the symbols up to the first blank will be considered output.\<close> (* TODO does this make sense *)

definition output_config :: "('q, 's) TM_config \<Rightarrow> 's list"
  where "output_config c = (let o_tp = last (tapes c) in
    case head o_tp of Bk \<Rightarrow> [] | Some h \<Rightarrow> h # the (those (takeWhile (\<lambda>s. s \<noteq> Bk) (right o_tp))))"

lemma out_config_simps[simp, intro]: "last (tapes c) = <w>\<^sub>t\<^sub>p \<Longrightarrow> output_config c = w"
  unfolding output_config_def by (induction w) (auto simp add: takeWhile_map)

text\<open>The requirement that the output conforms to the input standard should simplify some parts.
  It is possible to construct a TM that produces clean output, simply by adding another tape.\<close>

definition "clean_output c \<equiv> \<exists>w. last (tapes c) = <w>\<^sub>t\<^sub>p"


(* TODO document, clean up *)

definition (in -) [simp]: "hoare_run w M P \<equiv> hoare_halt (TM.on_input M w) M P"

definition "computes_word w w' \<equiv> hoare_run w M (\<lambda>c. clean_output c \<and> output_config c = w')"

definition "computes f \<equiv> \<forall>w. computes_word w (f w)"
declare (in -) TM.computes_def[simp]

lemma computes_halts[elim]: "computes f \<Longrightarrow> halts w"
  unfolding halts_altdef2 by (auto simp add: computes_word_def)


definition "config_time c \<equiv> LEAST n. is_final (steps n c)"

lemma steps_conf_time[intro, simp]:
  assumes "is_final (steps n c)"
  shows "steps (config_time c) c = steps n c"
    (is "steps ?n' c = steps n c")
proof -
  from assms have "is_final (steps ?n' c)" unfolding config_time_def by (rule LeastI)
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
  with assms(1) show ?thesis unfolding config_time_def by fast
qed

lemma conf_time_geI[intro]: "is_final (steps n c) \<Longrightarrow> config_time c \<le> n"
  unfolding config_time_def run_def by (fact Least_le)

lemma conf_time_ge_iff: "halts_config c \<Longrightarrow> is_final (steps n c) \<longleftrightarrow> n \<ge> config_time c" by blast

lemma conf_time_less_rev[intro]: "halts_config c \<Longrightarrow> \<not> is_final (steps n c) \<Longrightarrow> n < config_time c"
  by (subst (asm) conf_time_ge_iff) auto

lemma conf_time_finalI[intro]: "halts_config c \<Longrightarrow> is_final (steps (config_time c) c)"
  using conf_time_ge_iff by blast


definition "time w \<equiv> config_time (initial_config w)"
declare (in -) TM.time_def[simp]

lemma time_altdef: "time w = (LEAST n. is_final (run n w))" using config_time_def by simp


lemma hoare_run_run[dest]: "hoare_run w M P \<Longrightarrow> P (run (time w) w)" by fastforce

lemma hoare_config_run: 
  assumes "computes_word w w'"
  shows "last (tapes (run (time w) w)) = <w'>\<^sub>t\<^sub>p"
proof -
  let ?c = "run (time w) w"
  from assms have "clean_output ?c" and "output_config ?c = w'" unfolding computes_word_def by blast+
  then obtain x where "last (tapes ?c) = <x>\<^sub>t\<^sub>p" unfolding clean_output_def by blast
  then have "output_config ?c = x" by blast
  with \<open>output_config ?c = w'\<close> have "x = w'" by blast
  with \<open>last (tapes ?c) = <x>\<^sub>t\<^sub>p\<close> show ?thesis by blast
qed

lemma computes_output: "computes f \<Longrightarrow> last (tapes (run (time w) w)) = <f w>\<^sub>t\<^sub>p"
  by (intro hoare_config_run) simp

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


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

definition accepts :: "'s list \<Rightarrow> bool"
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
using accepts_def assms hoare_halt_def wf_initial_config by fastforce

definition rejects :: "'s list \<Rightarrow> bool"
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
by (smt (verit, ccfv_SIG) assms hoare_halt_def rejects_def wf_initial_config)

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

  moreover from assms have "wf_config (initial_config w)"
    unfolding accepts_def by (intro wf_initial_config) blast
  moreover have "init w (initial_config w)" ..
  ultimately show False by (intro hoare_contr)
qed

lemma rejects_altdef:
  "rejects w = (halts w \<and> \<not> accepts w)"
  using acc_not_rej halts_iff by blast

definition decides_word :: "'s lang \<Rightarrow> 's list \<Rightarrow> bool"
  where decides_def[simp]: "decides_word L w \<equiv> (w \<in> L \<longleftrightarrow> accepts w) \<and> (w \<notin> L \<longleftrightarrow> rejects w)"

abbreviation decides :: "'s lang \<Rightarrow> bool"
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
  by (cases "w\<in>L") (simp add: hoare_halt_def del: initial_config_def)+

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
