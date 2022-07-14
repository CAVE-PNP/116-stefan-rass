theory Computability
  imports TM Formal_Languages
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

(* TODO consider introducing: notation input_tape ("\<langle>_\<rangle>") *)

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

lemma (in typed_TM) wf_initial_config[intro!]: "wf_config (initial_config w)" by force


subsubsection\<open>Running a TM Program\<close>

definition run :: "nat \<Rightarrow> 's list \<Rightarrow> ('q, 's) TM_config"
  where [simp]: "run n w \<equiv> steps n (initial_config w)"

corollary wf_config_run[intro, simp]: "wf_input w \<Longrightarrow> wf_config (run n w)" by auto
corollary (in typed_TM) wf_config_run[intro!, simp]: "wf_config (run n w)" by auto

corollary run_tapes_len[simp]: "length (tapes (run n w)) = k" by (simp add: steps_l_tps)
corollary run_tapes_non_empty[simp, intro]: "tapes (run n w) \<noteq> []"
  using at_least_one_tape by (fold length_0_conv) (simp add: steps_l_tps)

lemma final_le_run[dest]: "is_final (run n w) \<Longrightarrow> n \<le> m \<Longrightarrow> run m w = run n w"
  unfolding run_def by (fact final_le_steps)

corollary final_mono_run[dest]: "is_final (run n w) \<Longrightarrow> n \<le> m \<Longrightarrow> is_final (run m w)"
  unfolding run_def by (fact final_mono)


definition "on_input w \<equiv> (\<lambda>c. c = initial_config w)"

lemma (in -) on_inputI[intro, simp]: "TM.on_input M w (TM.initial_config M w)"
  unfolding TM.on_input_def by blast


definition halts_config :: "('q, 's) TM_config \<Rightarrow> bool"
  where [simp]: "halts_config c \<equiv> \<exists>n. is_final (steps n c)"

mk_ide (in -) TM.halts_config_def |intro halts_confI[intro]| |dest halts_confD[dest]|


definition halts :: "'s list \<Rightarrow> bool"
  where [simp]: "halts w \<equiv> halts_config (c\<^sub>0 w)"

lemma halts_altdef: "halts w \<longleftrightarrow> (\<exists>n. is_final (run n w))" by simp

mk_ide (in -) TM.halts_altdef |intro haltsI[intro]| |dest haltsD[dest]|


subsubsection\<open>Output\<close>

text\<open>By convention, the \<^emph>\<open>output\<close> of a TM is found on its last tape
  when the computation has reached its end.
  The tape head is positioned over the first symbol of the word,
  and the \<open>n\<close>-th symbol of the word is reached by moving the tape head \<open>n\<close> cells to the right.
  As with input, the \<^const>\<open>blank_symbol\<close> is not part of the output,
  so only the symbols up to the first blank will be considered output.\<close> (* TODO does this make sense *)

definition output_of :: "('q, 's) TM_config \<Rightarrow> 's list"
  where [code]: "output_of c = (let o_tp = last (tapes c) in
    case head o_tp of Bk \<Rightarrow> [] | Some h \<Rightarrow> h # the (those (takeWhile (\<lambda>s. s \<noteq> Bk) (right o_tp))))"

lemma out_config_simps[simp, intro]: "last (tapes c) = <w>\<^sub>t\<^sub>p \<Longrightarrow> output_of c = w"
  unfolding output_of_def by (induction w) (auto simp add: takeWhile_map)


text\<open>The requirement that the output conforms to the input standard should simplify some parts.
  It is possible to construct a TM that produces clean output, simply by adding another tape.\<close>

definition "clean_output c \<equiv> \<exists>w. last (tapes c) = <w>\<^sub>t\<^sub>p" (* TODO change to allow trailing blanks. potentially define new tape equivalence relation *)

lemma clean_outputI[intro]: "last (tapes c) = <w>\<^sub>t\<^sub>p \<Longrightarrow> clean_output c"
  unfolding clean_output_def by blast
lemma clean_outputD[dest]: "clean_output c \<Longrightarrow> output_of c = w \<Longrightarrow> last (tapes c) = <w>\<^sub>t\<^sub>p"
  unfolding clean_output_def by force

lemma clean_output_alt: "clean_output c \<and> output_of c = w \<longleftrightarrow> last (tapes c) = <w>\<^sub>t\<^sub>p"
  unfolding clean_output_def by force

lemma clean_output_altdef[code]: "clean_output c \<longleftrightarrow> last (tapes c) = <output_of c>\<^sub>t\<^sub>p"
  using clean_output_alt unfolding clean_output_def by blast

definition clean_output_of :: "('q, 's) TM_config \<Rightarrow> 's list option"
  where "clean_output_of c = (if clean_output c then Some (output_of c) else None)"

lemma clean_output_of_altdef[code]: "clean_output_of c =
    (let w = output_of c in  if last (tapes c) = <w>\<^sub>t\<^sub>p then Some w else None)"
  unfolding clean_output_of_def Let_def clean_output_altdef ..


definition has_output :: "('q, 's) TM_config \<Rightarrow> 's list \<Rightarrow> bool"
  where "has_output c w \<equiv> clean_output_of c = Some w"

lemma has_output_altdef: "has_output c w \<longleftrightarrow> last (tapes c) = <w>\<^sub>t\<^sub>p"
  unfolding has_output_def clean_output_of_def by auto

mk_ide has_output_altdef |intro has_outputI[intro]| |dest has_outputD[dest]|


subsubsection\<open>\<open>compute\<close> Function\<close>

definition "compute_config c = steps (SOME n. is_final (steps n c)) c"

lemma halts_compute_config[iff?]: "halts_config c \<longleftrightarrow> is_final (compute_config c)"
  unfolding compute_config_def halts_config_def by (fact some_eq_ex[symmetric])


definition "compute w = compute_config (initial_config w)"

lemma halts_compute: "halts w \<longleftrightarrow> is_final (compute w)"
  unfolding compute_def halts_def by (fact halts_compute_config)

mk_ide (in -) TM.halts_compute |intro halts_compI[intro]| |dest halts_compD[dest]|

lemma compute_altdef: "compute w = run (SOME n. is_final (run n w)) w"
  unfolding compute_def compute_config_def run_def ..

lemma compute_altdef2[simp]: "is_final (steps n (c\<^sub>0 w)) \<Longrightarrow> compute w = run n w"
  unfolding compute_altdef run_def by (meson final_steps_rev someI)

lemma computeI[intro?]:
  assumes "\<exists>n. is_final (run n w) \<and> P (run n w)"
  shows "P (compute w)"
proof -
  from assms have "halts w" by auto
  then have "is_final (compute w)" ..
  from assms obtain n where "is_final (run n w)" and "P (run n w)" by blast
  with \<open>is_final (compute w)\<close> have "run n w = compute w" by simp
  with \<open>P (run n w)\<close> show "P (compute w)" by argo
qed

lemma final_run_compute[intro]: "is_final (run n w) \<Longrightarrow> run n w = compute w" by (blast intro: computeI)


subsubsection\<open>\<open>computes\<close> Predicate\<close>

definition computes_word :: "'s list \<Rightarrow> 's list \<Rightarrow> bool"
  where"computes_word w w' \<equiv> halts w \<and> has_output (compute w) w'"

mk_ide computes_word_def |intro computes_wordI[intro]| |dest computes_wordD[dest]|


definition "computes f \<equiv> \<forall>w. computes_word w (f w)"

lemma computes_haltsD[dest]: "computes f \<Longrightarrow> halts w" unfolding computes_def by force

mk_ide computes_def |intro computesI[intro]| |dest computesD[dest]|


subsection\<open>Deciding Languages\<close>

definition accepts :: "'s list \<Rightarrow> bool" where "accepts w \<equiv> state (compute w) \<in> F\<^sub>A"
definition rejects :: "'s list \<Rightarrow> bool" where "rejects w \<equiv> state (compute w) \<in> F\<^sub>R"

lemma halts_iff: "halts w \<longleftrightarrow> accepts w \<or> rejects w"
  unfolding accepts_def rejects_def using is_final_altdef by blast

lemma accepts_halts[dest]: "accepts w \<Longrightarrow> halts w" using halts_iff by blast
lemma rejects_halts[dest]: "rejects w \<Longrightarrow> halts w" using halts_iff by blast

lemma acc_not_rej: "accepts w \<Longrightarrow> \<not> rejects w"
  unfolding accepts_def rejects_def rejecting_states_def by simp

lemma rejects_accepts:
  "rejects w = (halts w \<and> \<not> accepts w)"
  using acc_not_rej halts_iff by blast

lemma accepts_altdef: "accepts w \<longleftrightarrow> (\<exists>n. state (run n w) \<in> F\<^sub>A)"
proof (rule iffI)
  assume "accepts w"
  then show "\<exists>n. state (run n w) \<in> F\<^sub>A" unfolding accepts_def compute_altdef by blast
next
  assume "\<exists>n. state (run n w) \<in> F\<^sub>A"
  then obtain n where "state (run n w) \<in> F\<^sub>A" ..
  then have "is_final (run n w)" ..
  with \<open>state (run n w) \<in> F\<^sub>A\<close> show "accepts w" unfolding accepts_def by simp
qed

lemma rejects_altdef: "rejects w \<longleftrightarrow> (\<exists>n. state (run n w) \<in> F\<^sub>R)"
proof (rule iffI)
  assume "rejects w"
  then show "\<exists>n. state (run n w) \<in> F\<^sub>R" unfolding rejects_def compute_altdef by blast
next
  assume "\<exists>n. state (run n w) \<in> F\<^sub>R"
  then obtain n where "state (run n w) \<in> F\<^sub>R" ..
  then have "is_final (run n w)" ..
  with \<open>state (run n w) \<in> F\<^sub>R\<close> show "rejects w" unfolding rejects_def by fastforce
qed


definition decides_word :: "'s lang \<Rightarrow> 's list \<Rightarrow> bool"
  where decides_def[simp]: "decides_word L w \<equiv> (w \<in>\<^sub>L L \<longleftrightarrow> accepts w) \<and> (w \<notin>\<^sub>L L \<longleftrightarrow> rejects w)"

lemma decides_halts: "decides_word L w \<Longrightarrow> halts w"
  using halts_iff by auto

abbreviation decides :: "'s lang \<Rightarrow> bool"
  where "decides L \<equiv> alphabet L \<subseteq> \<Sigma>\<^sub>i\<^sub>n \<and> (\<forall>w. set w \<subseteq> alphabet L \<longrightarrow> decides_word L w)"

corollary decides_halts_all: "decides L \<Longrightarrow> \<forall>w. set w \<subseteq> alphabet L \<longrightarrow> halts w"
  using decides_halts by blast

lemma decides_altdef: "decides_word L w \<longleftrightarrow> halts w \<and> (w \<in>\<^sub>L L \<longleftrightarrow> accepts w)"
proof (intro iffI)
  fix w
  assume "decides_word L w"
  hence "halts w" by (rule decides_halts)
  moreover have "w \<in>\<^sub>L L \<longleftrightarrow> accepts w" using \<open>decides_word L w\<close> by simp
  ultimately show "halts w \<and> (w \<in>\<^sub>L L \<longleftrightarrow> accepts w)" ..
next
  assume "halts w \<and> (w \<in>\<^sub>L L \<longleftrightarrow> accepts w)"
  then show "decides_word L w" by (simp add: rejects_accepts)
qed

lemma decides_altdef4: "decides_word L w \<longleftrightarrow> (if w \<in>\<^sub>L L then accepts w else rejects w)"
  unfolding decides_def using acc_not_rej by (cases "w \<in>\<^sub>L L") auto

end


subsubsection\<open>The Rejecting TM\<close>

text\<open>Based on the example TM \<^const>\<open>rejecting_TM_rec\<close> defined for \<^typ>\<open>('q, 's) TM\<close>.\<close>

locale Rej_TM = TM "rejecting_TM q0 s" for q0 :: 'q and s :: 's
begin

lemma M_rec: "M_rec = rejecting_TM_rec q0 s" unfolding rejecting_TM_def
  by (blast intro: Abs_TM_inverse rejecting_TM_valid)
lemmas M_fields = TM_fields_defs[unfolded M_rec rejecting_TM_rec_def TM_record.simps]
lemmas [simp] = M_fields(1-6)

lemma rejects: "rejects w" by (simp add: rejects_altdef)

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
