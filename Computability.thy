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

lemma input_tape_empty_hd_iff[iff]: "head <w>\<^sub>t\<^sub>p = None \<longleftrightarrow> w = []"
  unfolding input_tape_def by simp

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>


context TM
begin

text\<open>By convention, the initial configuration has the input word on the first tape
  with all other tapes being empty.\<close>

definition initial_config :: "'s list \<Rightarrow> ('q, 's) TM_config"
  where "initial_config w = TM_config q\<^sub>0 (<w>\<^sub>t\<^sub>p # empty_tape \<up> (k - 1))"

abbreviation "c\<^sub>0 \<equiv> initial_config"

lemma init_conf_len: "length (tapes (initial_config w)) = k"
  using at_least_one_tape by (simp add: initial_config_def)
lemma init_conf_state: "state (initial_config w) = q\<^sub>0" by (simp add: initial_config_def)
lemmas init_conf_simps[simp] = init_conf_len init_conf_state

lemma init_conf_last[simp, intro]:
  shows "k = 1 \<Longrightarrow> last (tapes (c\<^sub>0 w)) = <w>\<^sub>t\<^sub>p"
    and "k \<noteq> 1 \<Longrightarrow> last (tapes (c\<^sub>0 w)) = \<langle>\<rangle>"
  using at_least_one_tape' by (simp_all add: initial_config_def)

lemma all_initial_tapes_helperI[intro]:
  assumes "P <w>\<^sub>t\<^sub>p" and "P \<langle>\<rangle>"
  shows "\<forall>tp\<in>set (tapes (c\<^sub>0 w)). P tp"
  unfolding initial_config_def TM_config.sel
  unfolding list.pred_inject(2)[unfolded list_all_iff]
  unfolding Ball_set_replicate using assms by blast

lemma one_tape_initial_config: "TM.tape_count M = 1 \<Longrightarrow>
                                initial_config w = TM_config q\<^sub>0 [<w>\<^sub>t\<^sub>p]"
  unfolding initial_config_def by simp

lemma same_tape_count_same_init_tapes: "tapes (TM.initial_config M1 w) =
    tapes (TM.initial_config M2 w) \<longleftrightarrow> TM.tape_count M1 = TM.tape_count M2"
  unfolding TM.initial_config_def apply auto
  by (metis Suc_pred TM.at_least_one_tape)

lemma no_right_shift_left_empty:
       "(\<And>st n hds. TM.next_move M st hds n \<noteq> Shift_Right) \<Longrightarrow>
       (\<And>w n. n < length ((tapes ((TM.step M^^m) (TM.initial_config M w)))) \<Longrightarrow>
        left ((tapes ((TM.step M^^m) (TM.initial_config M w))) ! n) = [])"
proof (induction m, auto)
  have 1: "\<And>w. tapes (c\<^sub>0 w) ! 0 = <w>\<^sub>t\<^sub>p" unfolding initial_config_def by simp
  fix w :: "'s list" and n :: nat
  assume "n < k"
  moreover have "left (tapes (c\<^sub>0 w) ! 0) = []" unfolding 1 by simp
  moreover have "\<And>n. Suc n < k \<Longrightarrow> left (tapes (c\<^sub>0 w) ! (Suc n)) = []"
    unfolding initial_config_def by simp
  ultimately show "left (tapes (c\<^sub>0 w) ! n) = []" unfolding 1
    by (metis 1 lessI less_Suc_eq_0_disj)
next
  fix m n :: nat and w :: "'s list"
  assume a1: "(\<And>w n. n < length (tapes (steps m (c\<^sub>0 w))) \<Longrightarrow>
               left (tapes (steps m (c\<^sub>0 w)) ! n) = [])" and
         a2: "(\<And>st n hds. \<delta>\<^sub>m st hds n \<noteq> Shift_Right)" and
         a3: "n < length (tapes (step (steps m (c\<^sub>0 w))))"
  moreover have "\<And>w. length (tapes (c\<^sub>0 w)) = k" by simp
  hence 2: "length (tapes (step (steps m (c\<^sub>0 w)))) = k" and
        "length (tapes (steps m (c\<^sub>0 w))) = k"
    using tape_count_step_equal step_l_tps steps_l_tps by blast+
  moreover from this have "left (tapes (steps m (c\<^sub>0 w)) ! n) = []" using a1 a3
    by presburger
  moreover have "\<And>tmc n. n < k \<Longrightarrow> k = length (tapes tmc) \<Longrightarrow>
                 left (tapes tmc ! n) = [] \<Longrightarrow>
                 left (tapes (step tmc) ! n) = []"
  proof (unfold step_def, unfold step_not_final_def, unfold Let_def, auto)
    fix tmc :: "('q, 's) TM_config" and n :: nat
    assume "n < length (tapes tmc)" and "left (tapes tmc ! n) = []" and "state tmc \<notin> F"
    have 3: "\<And>n. \<delta>\<^sub>m (state tmc) (heads tmc) n \<noteq> Shift_Right" using a2 .
    show "left (tape_action (\<delta>\<^sub>w (state tmc) (heads tmc) n, \<delta>\<^sub>m (state tmc) (heads tmc) n)
          (tapes tmc ! n)) = []"
    proof (rule head_move.exhaust [of "\<delta>\<^sub>m (state tmc) (heads tmc) n"], auto)
      show "left (tape_action (\<delta>\<^sub>w (state tmc) (heads tmc) n, Shift_Left) (tapes tmc ! n))
            = []" unfolding tape_action_def
        by (simp add: \<open>left (tapes tmc ! n) = []\<close> tape_write_def)
    next
      assume "\<delta>\<^sub>m (state tmc) (heads tmc) n = Shift_Right"
      hence "False" using 3 by simp
      thus "left (tape_action (\<delta>\<^sub>w (state tmc) (heads tmc) n, Shift_Right)
            (tapes tmc ! n)) = []" ..
    next
      show "\<delta>\<^sub>m (state tmc) (heads tmc) n = No_Shift \<Longrightarrow> left (tapes tmc ! n) = []"
        by (simp add: \<open>left (tapes tmc ! n) = []\<close> tape_write_def)
    qed
  qed
  ultimately show "left (tapes (step (steps m (c\<^sub>0 w))) ! n) = []" by simp
qed

lemma
  shows 
    initial_config_heads_0: "w \<noteq> [] \<Longrightarrow> heads (initial_config w) ! 0 = Some (w ! 0)"
                    and heads_empty_none [simp]: "heads (initial_config []) ! 0 = None"
  unfolding initial_config_def input_tape_def by (simp_all add: hd_conv_nth)

lemma heads_of_cons_input [simp]: "heads (initial_config (h # t)) =
                                   (Some h) # (replicate (k - 1) None)"
  unfolding head_def initial_config_def input_tape_def by simp

lemma initial_tapes_empty [simp]: "i > 0 \<Longrightarrow> i < length (tapes (initial_config w)) \<Longrightarrow>
       tapes (initial_config w) ! i = Tape [] None []"
  unfolding initial_config_def by simp

lemma initial_tapes_non_empty_Nil [simp]: "tapes (initial_config []) ! 0 = Tape [] None []"
  unfolding initial_config_def by simp

lemma initial_tapes_non_empty_Cons [simp]: "tapes (initial_config (h#t)) ! 0 =
                                            Tape [] (Some h) (map Some t)"
  unfolding initial_config_def by simp

lemma initial_first_tape_right: "Suc i < length w \<Longrightarrow>
       right (tapes (initial_config w) ! 0) ! i = Some (w ! Suc i)"
  unfolding initial_config_def TM_abbrevs.input_tape_def apply auto
  by (induction i) (simp_all add: nth_tl)

lemma None_not_in_input: "None \<notin> set (right ((tapes (initial_config l)) ! 0))"
  unfolding initial_config_def input_tape_def by simp

lemma head_input_None_iff [iff]: "head (((tapes (initial_config l)) ! 0)) = None \<longleftrightarrow>
                                  l = []"
  unfolding initial_config_def input_tape_def by simp

abbreviation "wf_input w \<equiv> w \<in> \<Sigma>*"

lemma wf_initial_config: "wf_input w \<Longrightarrow> wf_config (initial_config w)"
  by (intro wf_configI all_initial_tapes_helperI) auto
declare TM.wf_initial_config[simp, intro]

lemma (in typed_TM) wf_initial_config[intro!]: "wf_config (initial_config w)" by simp

subsubsection\<open>Running a TM Program\<close>

definition run :: "nat \<Rightarrow> 's list \<Rightarrow> ('q, 's) TM_config"
  where [simp]: "run n w \<equiv> steps n (initial_config w)"

corollary wf_config_run[intro, simp]: "wf_input w \<Longrightarrow> wf_config (run n w)" by auto
corollary (in typed_TM) wf_config_run[intro!, simp]: "wf_config (run n w)" by auto

corollary run_tapes_len[simp]: "length (tapes (steps n (c\<^sub>0 w))) = k" by (simp add: steps_l_tps)
corollary run_tapes_non_empty[simp, intro]: "tapes (run n w) \<noteq> []"
  using run_tapes_len by (fold length_0_conv) simp

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

lemma halts_config_final[simp, dest?]: "is_final c \<Longrightarrow> halts_config c" by blast


definition halts :: "'s list \<Rightarrow> bool"
  where "halts w \<equiv> halts_config (c\<^sub>0 w)"

lemma halts_altdef: "halts w \<longleftrightarrow> (\<exists>n. is_final (run n w))" by (simp add: halts_def)

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

lemma output_of_initial_config: "k = 1 \<Longrightarrow> output_of (initial_config w) = w" by simp


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

lemma initial_state_final_output:
  assumes "TM.initial_state M \<in> TM.final_states M" and "k = 1"
  shows "has_output (initial_config w) w"
  unfolding has_output_def clean_output_of_def
proof (rule ifI)
  show "Some (output_of (c\<^sub>0 w)) = Some w" using assms(2) by simp
next
  assume "\<not> clean_output (c\<^sub>0 w)"
  moreover have "clean_output (c\<^sub>0 w)" using assms(2) by auto
  ultimately show "None = Some w" ..
qed

mk_ide has_output_altdef |intro has_outputI[intro]| |dest has_outputD[dest]|


subsubsection\<open>\<open>compute\<close> Function\<close>

definition "compute_config c = steps (LEAST n. is_final (steps n c)) c"

lemma halts_compute_config[iff?]: "halts_config c \<longleftrightarrow> is_final (compute_config c)"
  unfolding compute_config_def halts_config_def by (rule iffI) (fact LeastI_ex, fact exI)

definition "compute w = compute_config (initial_config w)"

lemma halts_compute: "halts w \<longleftrightarrow> is_final (compute w)"
  unfolding compute_def halts_def by (fact halts_compute_config)

mk_ide (in -) TM.halts_compute |intro halts_compI[intro]| |dest halts_compD[dest]|

lemma compute_altdef2: "compute w = run (LEAST n. is_final (run n w)) w"
  unfolding compute_def compute_config_def run_def ..

lemma compute_run_eqI[simp]: "is_final (steps n (c\<^sub>0 w)) \<Longrightarrow> compute w = run n w"
  unfolding compute_altdef2 run_def by (rule final_steps_rev, rule LeastI_ex) blast+

lemma computeI:
  assumes "\<exists>n. is_final (run n w) \<and> P (run n w)"
  shows "P (compute w)"
proof -
  from assms have "halts w" by auto
  then have "is_final (compute w)" ..
  from assms obtain n where "is_final (run n w)" and "P (run n w)" by blast
  with \<open>is_final (compute w)\<close> have "run n w = compute w" by simp
  with \<open>P (run n w)\<close> show "P (compute w)" by argo
qed

lemma wf_config_compute[intro, dest]: "wf_input w \<Longrightarrow> wf_config (compute w)"
  unfolding compute_altdef2 by blast

lemma final_run_compute[intro]: "is_final (run n w) \<Longrightarrow> run n w = compute w"
  by (blast intro: computeI)


subsubsection\<open>\<open>computes\<close> Predicate\<close>

definition computes_word :: "'s list \<Rightarrow> 's list \<Rightarrow> bool"
  where"computes_word w w' \<equiv> halts w \<and> has_output (compute w) w'"

mk_ide computes_word_def |intro computes_wordI[intro]| |dest computes_wordD[dest]|


definition "computes f \<equiv> \<forall>w. computes_word w (f w)"

lemma computes_haltsD[dest]: "computes f \<Longrightarrow> halts w" unfolding computes_def by force

mk_ide computes_def |intro computesI[intro]| |dest computesD[dest]|

lemma is_final_states_eq: "is_final (steps k1 (initial_config w)) \<Longrightarrow>
                           is_final (steps k2 (initial_config w)) \<Longrightarrow>
                           state (steps k1 (initial_config w)) =
                           state (steps k2 (initial_config w))"
  unfolding is_final_def by (metis run_def is_finalI compute_run_eqI)
end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>

lemma left_length_eq_after_step: "i < TM.tape_count M1 \<Longrightarrow> i < TM.tape_count M2 \<Longrightarrow>
       length (left (tapes (TM.steps M1 n (TM.initial_config M1 w)) ! i)) =
       length (left (tapes (TM.steps M2 n (TM.initial_config M2 w)) ! i)) \<Longrightarrow>
       TM.next_move M1 (state (TM.steps M1 n (TM.initial_config M1 w)))
       (heads (TM.steps M1 n (TM.initial_config M1 w))) i =
       TM.next_move M2 (state (TM.steps M2 n (TM.initial_config M2 w)))
       (heads (TM.steps M2 n (TM.initial_config M2 w))) i \<Longrightarrow>
       TM.is_final M1 (TM.steps M1 n (TM.initial_config M1 w)) \<longleftrightarrow>
       TM.is_final M2 (TM.steps M2 n (TM.initial_config M2 w)) \<Longrightarrow>
       length (left (tapes (TM.steps M1 (Suc n) (TM.initial_config M1 w)) ! i)) =
       length (left (tapes (TM.steps M2 (Suc n) (TM.initial_config M2 w)) ! i))"
  apply (cases "TM.TM.next_move M1 (state ((TM.step M1 ^^ n) (TM.initial_config M1 w)))
     (heads ((TM.step M1 ^^ n) (TM.initial_config M1 w))) i") apply simp_all
  apply (metis TM.run_tapes_len TM.step_final length_left_Shift_Left)
  apply (metis TM.run_tapes_len TM.step_final length_left_Shift_Right)
  by (simp add: TM.run_tapes_len no_move_same_left)

lemma right_length_eq_after_step: "i < TM.tape_count M1 \<Longrightarrow> i < TM.tape_count M2 \<Longrightarrow>
       length (right (tapes (TM.steps M1 n (TM.initial_config M1 w)) ! i)) =
       length (right (tapes (TM.steps M2 n (TM.initial_config M2 w)) ! i)) \<Longrightarrow>
       TM.next_move M1 (state (TM.steps M1 n (TM.initial_config M1 w)))
       (heads (TM.steps M1 n (TM.initial_config M1 w))) i =
       TM.next_move M2 (state (TM.steps M2 n (TM.initial_config M2 w)))
       (heads (TM.steps M2 n (TM.initial_config M2 w))) i \<Longrightarrow>
       TM.is_final M1 (TM.steps M1 n (TM.initial_config M1 w)) \<longleftrightarrow>
       TM.is_final M2 (TM.steps M2 n (TM.initial_config M2 w)) \<Longrightarrow>
       length (right (tapes (TM.steps M1 (Suc n) (TM.initial_config M1 w)) ! i)) =
       length (right (tapes (TM.steps M2 (Suc n) (TM.initial_config M2 w)) ! i))"
  apply (cases "TM.TM.next_move M1 (state ((TM.step M1 ^^ n) (TM.initial_config M1 w)))
     (heads ((TM.step M1 ^^ n) (TM.initial_config M1 w))) i") apply simp_all
  apply (metis TM.run_tapes_len TM.step_final length_right_Shift_Left)
  apply (metis TM.run_tapes_len TM.step_final length_right_Shift_Right)
  by (simp add: TM.run_tapes_len no_move_same_right)

lemma init_conf_ext: shows "state (TM.initial_config tm w) =
                            state (TM.initial_config (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w))"
                     and "map tm_tape_ext (tapes (TM.initial_config tm w)) =
                          tapes (TM.initial_config (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w))"
   apply (metis TM.init_conf_state ext_initial_state ext_tm_valid valid_tm_initial_state)
proof -
  have "\<And>tm w. tapes
       (TM_config (TM.TM.initial_state tm) (TM_abbrevs.input_tape w # Tape [] None [] \<up> (TM.TM.tape_count tm - 1))) =
       TM_abbrevs.input_tape w # Tape [] None [] \<up> (TM.TM.tape_count tm - 1)" by simp
  moreover have "\<And>tm w. map tm_tape_ext (TM_abbrevs.input_tape w # Tape [] None [] \<up> (TM.TM.tape_count tm - 1)) =
                TM_abbrevs.input_tape (map (\<lambda>x. [x]) w) # Tape [] None [] \<up> (TM.TM.tape_count tm - 1)"
  proof -
    have "\<And>w.  w = [] \<longleftrightarrow> map (\<lambda>x. [x]) w = []" by simp
    moreover have "\<And>w. w \<noteq> [] \<Longrightarrow> tm_tape_ext (Tape [] (Some (hd w)) (map Some (tl w))) =
                  Tape [] (Some (hd (map (\<lambda>x. [x]) w))) (map Some (tl (map (\<lambda>x. [x]) w)))"
    proof (auto, metis hd_map)
      have "\<And>l f. map (map_option f \<circ> Some) l = map Some (map f l)" by simp
      thus "\<And>w. w \<noteq> [] \<Longrightarrow> map (map_option (\<lambda>xo. [xo]) \<circ> Some) (tl w) = map Some (tl (map (\<lambda>x. [x]) w))"
        by (simp add: list.map_sel(2))
    qed
    ultimately have "\<And>w. tm_tape_ext (TM_abbrevs.input_tape w) = TM_abbrevs.input_tape (map (\<lambda>x. [x]) w)"
      unfolding TM_abbrevs.input_tape_def by auto
    thus "\<And>tm w. map tm_tape_ext (TM_abbrevs.input_tape w # Tape [] None [] \<up> (TM.TM.tape_count tm - 1)) =
                TM_abbrevs.input_tape (map (\<lambda>x. [x]) w) # Tape [] None [] \<up> (TM.TM.tape_count tm - 1)" by auto
  qed
  thus "map tm_tape_ext (tapes (TM.initial_config tm w)) =
        tapes (TM.initial_config (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w))"
    by (metis TM.initial_config_def TM_config.sel(2) ext_tape_count ext_tm_valid valid_tm_tape_count)
qed

lemma tm_ext_state_run: "state (TM.run (Abs_TM (tm_to_ext_tm tm)) n (map (\<lambda>x. [x]) w)) = state (TM.run tm n w)"
  by (metis TM.run_def init_conf_ext(1) init_conf_ext(2) tm_ext_steps_eq(1))

lemma tm_ext_tapes_run: "tapes (TM.run (Abs_TM (tm_to_ext_tm tm)) n (map (\<lambda>x. [x]) w)) =
                         map tm_tape_ext (tapes (TM.run tm n w))"
  by (metis TM.run_def init_conf_ext(1) init_conf_ext(2) tm_ext_steps_eq(2))

lemma tm_ext_halts_config:
  fixes tm :: "('a, 'b, 'c) TM" and c :: "('a, 'b) TM_config" and ext_c :: "('a, 'b list) TM_config"
  assumes "state c = state ext_c" and "map tm_tape_ext (tapes c) = tapes ext_c"
  shows "TM.halts_config (Abs_TM (tm_to_ext_tm tm)) ext_c \<longleftrightarrow> TM.halts_config tm c"
  by (metis assms(1) assms(2) ext_final_states ext_tm_valid halts_confD halts_confI is_finalD is_finalI
      tm_ext_steps_eq(1) valid_tm_final_states)

lemma tm_ext_halts: "TM.halts (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w) \<longleftrightarrow> TM.halts tm w"
  apply (unfold TM.halts_def)
proof
  assume "TM.halts_config (Abs_TM (tm_to_ext_tm tm)) (TM.initial_config (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w))"
  thus "TM.halts_config tm (TM.initial_config tm w)"
    by (metis TM.compute_altdef2 TM.compute_def TM.halts_compute_config TM.halts_def TM.is_final_def
        ext_final_states ext_tm_valid haltsI tm_ext_state_run valid_tm_final_states)
next
  assume "TM.halts_config tm (TM.initial_config tm w)"
  thus "TM.halts_config (Abs_TM (tm_to_ext_tm tm)) (TM.initial_config (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w))"
    unfolding TM.halts_config_def
    by (metis \<open>TM.halts_config tm (TM.initial_config tm w)\<close> halts_confD init_conf_ext(1)
        init_conf_ext(2) tm_ext_halts_config)
qed

lemma computes_word_unique: "TM.computes_word M wi wo1 \<Longrightarrow> TM.computes_word M wi wo2 \<Longrightarrow> wo1 = wo2"
  unfolding TM.computes_word_def apply (drule conjunct2)+
  unfolding TM.has_output_def by simp

(* "Proper" TMs inspect the whole input first. During this process they can however
   already start their main computation. Maybe they will replace "normal" TMs in the
   future. *)
locale proper_TM = valid_TM +
  assumes inspect_input_first: "\<And>n w. n < length w \<Longrightarrow> TM.next_move (Abs_TM M)
          (state (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w)))
          (heads (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w))) 0 =
          Shift_Right" and
          inspect_input_not_stop: "\<And>n w. n < length w \<Longrightarrow>
       \<not>TM.is_final (Abs_TM M) (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w))"

lemma proper_TM_from_valid:  "valid_TM M \<Longrightarrow>
          (\<And>n w. valid_TM M \<Longrightarrow> n < length w \<Longrightarrow> TM.next_move (Abs_TM M)
          (state (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w)))
          (heads (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w))) 0 =
          Shift_Right) \<Longrightarrow> (\<And>n w. valid_TM M \<Longrightarrow> n < length w \<Longrightarrow>
          \<not>TM.is_final (Abs_TM M) (TM.steps (Abs_TM M) n
          (TM.initial_config (Abs_TM M) w))) \<Longrightarrow> proper_TM M"
  apply intro_locales
   apply assumption
  by (unfold_locales)

lemmas proper_TM_from_validI [intro!] = proper_TM_from_valid [OF valid_TM.intro]

typedef ('q, 's, 'l) PTM = "{M::('q, 's, 'l) TM_record. proper_TM M}"
proof (auto, standard)
  define symbol :: 's where "symbol \<equiv> (SOME _. True)"
  define init_state :: 'q where "init_state \<equiv> (SOME _. True)"
  define M_rec :: "('q, 's, 'l) TM_record" where
    "M_rec \<equiv> TM (Suc 0) {symbol} {init_state} init_state {} (\<lambda>_. (SOME _. True))
      (\<lambda>_ _. init_state) (\<lambda>_ _ _. Some symbol) (\<lambda>_ _ _. Shift_Right)"
  show "proper_TM M_rec"
    apply standard
    unfolding M_rec_def valid_tm_next_move TM.is_final_def valid_tm_final_states
    by simp_all
qed

definition valid_PTM :: "('q, 's, 'l) PTM \<Rightarrow> ('q, 's, 'l) TM" where
  "valid_PTM \<equiv> Abs_TM \<circ> Rep_PTM"

definition PTM_valid :: "('q, 's, 'l) TM \<Rightarrow> ('q, 's, 'l) PTM" where
  "PTM_valid \<equiv> Abs_PTM \<circ> Rep_TM"

lemma PTM_valid_inv [simp]: "PTM_valid (valid_PTM M) = M"
  unfolding valid_PTM_def PTM_valid_def apply auto
  by (metis Abs_TM_inverse Rep_PTM Rep_PTM_inverse mem_Collect_eq proper_TM.axioms(1))

lemma valid_PTM_inv [simp]: "proper_TM (Rep_TM M) \<Longrightarrow> valid_PTM (PTM_valid M) = M"
  unfolding valid_PTM_def PTM_valid_def by (simp add: Abs_PTM_inverse Rep_TM_inverse)

lemma valid_PTM_inj [intro]: "inj valid_PTM"
  unfolding valid_PTM_def by (metis PTM_valid_inv inj_def valid_PTM_def)

lemma PTM_valid_surj [intro]: "surj PTM_valid"
  unfolding PTM_valid_def by (metis PTM_valid_def PTM_valid_inv surjI)

lemma valid_Abs_PTM [simp]: "proper_TM M \<Longrightarrow> valid_PTM (Abs_PTM M) = Abs_TM M"
  by (simp add: Abs_PTM_inverse valid_PTM_def)

lemma non_empty_input_initial_heads: "length w > n \<Longrightarrow>
    heads (TM.initial_config M w) ! 0 = Some (hd w)"
  by (metis TM.initial_config_heads_0 hd_conv_nth less_nat_zero_code list.size(3))

subsection\<open>Deciding Languages\<close>

type_synonym ('q, 's) TM_decider = "('q, 's, bool) TM"
type_synonym ('q, 's) PTM_decider = "('q, 's, bool) PTM"

locale TM_decider = TM M for M :: "('q, 's) TM_decider"
begin

definition accepting_states ("F\<^sup>+") where acc_def: "accepting_states \<equiv> {q\<in>F. label q = True}"
definition rejecting_states ("F\<^sup>-") where rej_def: "rejecting_states \<equiv> {q\<in>F. label q = False}"

abbreviation "F\<^sub>A \<equiv> accepting_states"
abbreviation "F\<^sub>R \<equiv> rejecting_states"

lemma
  shows final_states_acc_rej[simp]: "F\<^sub>A \<union> F\<^sub>R = F"
    and acc_rej_states_disjoint: "F\<^sub>A \<inter> F\<^sub>R = {}"
    and acc_final[dest]: "q \<in> F\<^sub>A \<Longrightarrow> q \<in> F"
    and rej_final[dest]: "q \<in> F\<^sub>R \<Longrightarrow> q \<in> F"
    and accI[intro]: "label q = True  \<Longrightarrow> q \<in> F \<Longrightarrow> q \<in> F\<^sub>A"
    and rejI[intro]: "label q = False \<Longrightarrow> q \<in> F \<Longrightarrow> q \<in> F\<^sub>R"
  unfolding acc_def rej_def by blast+

lemma (in -)
  assumes "TM.F M1 = TM.F M2"
    and "\<And>q. q \<in> TM.F M1 \<Longrightarrow> TM.label M1 q = TM.label M2 q"
  shows acc_eqI: "TM_decider.F\<^sub>A M1 = TM_decider.F\<^sub>A M2"
    and rej_eqI: "TM_decider.F\<^sub>R M1 = TM_decider.F\<^sub>R M2"
proof -
  from assms have *: "{q\<in>TM.F M1. TM.label M1 q = l} = {q\<in>TM.F M2. TM.label M2 q = l}" for l by blast
  show "TM_decider.F\<^sub>A M1 = TM_decider.F\<^sub>A M2" and "TM_decider.F\<^sub>R M1 = TM_decider.F\<^sub>R M2"
    unfolding TM_decider.acc_def TM_decider.rej_def * by blast+
qed


definition accepts :: "'s list \<Rightarrow> bool" where "accepts w \<equiv> state (compute w) \<in> F\<^sub>A"
definition rejects :: "'s list \<Rightarrow> bool" where "rejects w \<equiv> state (compute w) \<in> F\<^sub>R"

lemma halts_iff[iff?]: "halts w \<longleftrightarrow> accepts w \<or> rejects w"
  unfolding accepts_def rejects_def using final_states_acc_rej by blast

mk_ide halts_iff |dest halts_acc_rejD[dest]|

lemma accepts_halts[dest]: "accepts w \<Longrightarrow> halts w" using halts_iff by blast
lemma rejects_halts[dest]: "rejects w \<Longrightarrow> halts w" using halts_iff by blast

lemma acc_not_rej: "accepts w \<Longrightarrow> \<not> rejects w"
  unfolding accepts_def rejects_def acc_def rej_def by simp

lemma rejects_accepts:
  "rejects w = (halts w \<and> \<not> accepts w)"
  using acc_not_rej halts_iff by blast

lemma accepts_altdef: "accepts w \<longleftrightarrow> (\<exists>n. state (run n w) \<in> F\<^sub>A)"
proof (rule iffI)
  assume "accepts w"
  then show "\<exists>n. state (run n w) \<in> F\<^sub>A" unfolding accepts_def compute_altdef2 by blast
next
  assume "\<exists>n. state (run n w) \<in> F\<^sub>A"
  then obtain n where "state (run n w) \<in> F\<^sub>A" ..
  then have "is_final (run n w)" unfolding is_final_def using final_states_acc_rej by blast
  with \<open>state (run n w) \<in> F\<^sub>A\<close> show "accepts w" unfolding accepts_def by force
qed

lemma rejects_altdef: "rejects w \<longleftrightarrow> (\<exists>n. state (run n w) \<in> F\<^sub>R)"
proof (rule iffI)
  assume "rejects w"
  then show "\<exists>n. state (run n w) \<in> F\<^sub>R" unfolding rejects_def compute_altdef2 by blast
next
  assume "\<exists>n. state (run n w) \<in> F\<^sub>R"
  then obtain n where "state (run n w) \<in> F\<^sub>R" ..
  then have "is_final (run n w)" unfolding is_final_def ..
  with \<open>state (run n w) \<in> F\<^sub>R\<close> show "rejects w" unfolding rejects_def by force
qed


definition decides_word :: "'s lang \<Rightarrow> 's list \<Rightarrow> bool"
  where decides_def[simp]: "decides_word L w \<equiv> (w \<in>\<^sub>L L \<longleftrightarrow> accepts w) \<and> (w \<notin>\<^sub>L L \<longleftrightarrow> rejects w)"

lemma decides_wordI: "halts w \<Longrightarrow> (w \<in>\<^sub>L L \<Longrightarrow> accepts w) \<Longrightarrow>
                      (accepts w \<Longrightarrow> w \<in>\<^sub>L L) \<Longrightarrow> decides_word L w"
  by (auto simp add: rejects_accepts)

lemma decides_halts: "decides_word L w \<Longrightarrow> halts w"
  using halts_iff by auto

abbreviation decides :: "'s lang \<Rightarrow> bool"
  where "decides L \<equiv> alphabet L \<subseteq> \<Sigma> \<and> (\<forall>w\<in>(alphabet L)*. decides_word L w)"

corollary decides_halts_all: "decides L \<Longrightarrow> \<forall>w\<in>(alphabet L)*. halts w"
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

text\<open>Based on the example TM \<^const>\<open>halting_TM_rec\<close> defined for \<^typ>\<open>('q, 's, 'l) TM\<close>.\<close>

definition rejecting_TM :: "'q \<Rightarrow> 's set \<Rightarrow> ('q, 's) TM_decider"
  where "rejecting_TM q0 \<Sigma> \<equiv> Abs_TM (halting_TM_rec q0 \<Sigma> False)"

locale Rej_TM = TM_decider "rejecting_TM q0 \<Sigma>" for q0 :: 'q and \<Sigma> :: "'s set" +
  assumes finite_symbols: "finite \<Sigma>"
    and nonempty_symbols: "\<Sigma> \<noteq> {}"
begin

lemma M_rec: "M_rec = halting_TM_rec q0 \<Sigma> False" unfolding rejecting_TM_def
  using finite_symbols nonempty_symbols
  by (blast intro: Abs_TM_inverse halting_TM_valid)
lemmas M_fields = TM_fields_defs[unfolded M_rec halting_TM_rec_def TM_record.simps]
lemmas [simp] = M_fields(1-6)

lemma rejects: "rejects w" by (auto simp: rejects_altdef is_final_def)

end

definition map_states_tmrec :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's, 'l) TM \<Rightarrow> ('b, 's, 'l) TM_record" where
  "inj_on f (TM.states M) \<Longrightarrow>
             map_states_tmrec f M \<equiv> TM (TM.tape_count M) (TM.symbols M)
             {s'. \<exists>s\<in>TM.states M. s' = f s} (f (TM.initial_state M))
             {s'. \<exists>s\<in>TM.final_states M. s' = f s}
             (\<lambda>s. TM.label M (THE y::'a. y \<in> TM.states M \<and> f y = s))
             (\<lambda>s hds. f (TM.next_state M (THE y::'a. y \<in> TM.states M \<and> f y = s) hds))
             (\<lambda>s hds k. TM.next_write M (THE y::'a. y \<in> TM.states M \<and> f y = s) hds k)
             (\<lambda>s hds k. TM.next_move M (THE y::'a. y \<in> TM.states M \<and> f y = s) hds k)"

lemma map_states_tmrec_valid: "inj_on f (TM.states M) \<Longrightarrow>
    valid_TM (map_states_tmrec f M)"
  unfolding map_states_tmrec_def apply standard
  apply auto
   apply (smt (verit, del_insts) TM.next_state_valid inv_into_f_f the_equality)
  by (smt (verit) TM.next_write_valid inj_on_def theI_unique)

lemma map_states_tmrec_step:
  fixes c :: "('a, 's) TM_config" and f :: "'a \<Rightarrow> 'b" and M :: "('a, 's, 'l) TM" and
        c' :: "('b, 's) TM_config"
  assumes f_inj: "inj_on f (TM.states M)" and state_c_in_M: "state c \<in> TM.states M"
  defines "c' \<equiv> TM_config (f (state c)) (tapes c)" and "step \<equiv> TM.step M c" and
          "step' \<equiv> TM.step (Abs_TM (map_states_tmrec f M)) c'"
        shows map_states_tmrec_step_state [simp]: "state step' = f (state step)" and
              map_states_tmrec_step_tapes [simp]: "tapes step' = tapes step"
  unfolding step_def step'_def c'_def
proof -
  have 1: "\<And>s. s \<in> TM.final_states M \<Longrightarrow> s \<in> TM.states M"
    by (rule TM.final_states_valid)
  have 2: "\<And>s. s \<in> TM.final_states M \<Longrightarrow>
           f s \<in> TM.final_states (Abs_TM (map_states_tmrec f M))"
    apply (frule 1)
    using f_inj by (smt (verit, ccfv_SIG) map_states_tmrec_def map_states_tmrec_valid
        mem_Collect_eq select_convs(5) valid_tm_final_states)
  show "state (TM.step (Abs_TM (map_states_tmrec f M))
        (TM_config (f (state c)) (tapes c))) = f (state (TM.step M c))"
    unfolding TM.step_def apply auto
    unfolding valid_tm_final_states [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] apply auto
    apply (metis 1 f_inj inj_onD state_c_in_M)
    unfolding map_states_tmrec_def [OF f_inj, symmetric]
    unfolding valid_tm_next_state [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] apply auto
    by (smt (verit, best) f_inj inj_onD state_c_in_M the_equality)
next
  show "tapes (TM.step (Abs_TM (map_states_tmrec f M))
        (TM_config (f (state c)) (tapes c))) = tapes (TM.step M c)"
    unfolding TM.step_def apply auto
    unfolding valid_tm_final_states [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] apply auto
    apply (metis TM.final_states_valid f_inj inj_onD state_c_in_M)
    unfolding map_states_tmrec_def [OF f_inj, symmetric]
    unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
    unfolding valid_tm_next_write [OF map_states_tmrec_valid [OF f_inj]]
      valid_tm_next_move [OF map_states_tmrec_valid [OF f_inj]]
      valid_tm_tape_count [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] apply auto
    by (smt (verit, best) f_inj inj_onD state_c_in_M the_equality)
qed

lemma map_states_tmrec_steps:
  fixes c :: "('a, 's) TM_config" and f :: "'a \<Rightarrow> 'b" and M :: "('a, 's, 'l) TM" and
        c' :: "('b, 's) TM_config" and n :: nat
      assumes f_inj: "inj_on f (TM.states M)" and
        state_c_in_M: "state c \<in> TM.states M" and
        wf_hds: "wf_hds_rec (Rep_TM M) (heads c)" and
        wf_left: "\<Union>(set (map (set\<circ>left) (tapes c))) \<subseteq> options (TM.symbols M)" and
        wf_right: "\<Union>(set (map (set\<circ>right) (tapes c))) \<subseteq> options (TM.symbols M)"
  defines "c' \<equiv> TM_config (f (state c)) (tapes c)" and "steps \<equiv> TM.steps M n c" and
          "steps' \<equiv> TM.steps (Abs_TM (map_states_tmrec f M)) n c'"
        shows map_states_tmrec_steps_state [simp]: "state steps' = f (state steps)"
          and map_states_tmrec_steps_tapes [simp]: "tapes steps' = tapes steps"
  unfolding steps_def steps'_def c'_def
proof -
  have 1: "state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
       (TM_config (f (state c)) (tapes c))) = f (state ((TM.step M ^^ n) c)) \<and>
       tapes ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
       (TM_config (f (state c)) (tapes c))) = tapes ((TM.step M ^^ n) c)"
    apply (induction n)
  proof auto
    fix n :: nat
    assume a1: "state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
                (TM_config (f (state c)) (tapes c))) = f (state ((TM.step M ^^ n) c))"
       and a2: "tapes ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
                (TM_config (f (state c)) (tapes c))) =
                tapes ((TM.step M ^^ n) c)"
    have 1: "(TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
             (TM_config (f (state c)) (tapes c)) =
             TM_config (f (state (TM.steps M n c)))
             (tapes (TM.steps M n c))" using a1 a2
      by (metis TM_config.collapse)
    have 2: "\<And>n. wf_hds_rec (Rep_TM M) (heads (TM.steps M n c)) \<and>
        \<Union>(set (map (set\<circ>left) (tapes (TM.steps M n c)))) \<subseteq> options (TM.symbols M) \<and>
        \<Union>(set (map (set\<circ>right) (tapes (TM.steps M n c)))) \<subseteq> options (TM.symbols M) \<and>
        state (TM.steps M n c) \<in> TM.states M"
    proof -
      fix n :: nat
      show "wf_hds_rec (Rep_TM M) (heads (TM.steps M n c)) \<and>
        \<Union>(set (map (set\<circ>left) (tapes (TM.steps M n c)))) \<subseteq> options (TM.symbols M) \<and>
        \<Union>(set (map (set\<circ>right) (tapes (TM.steps M n c)))) \<subseteq> options (TM.symbols M) \<and>
        state (TM.steps M n c) \<in> TM.states M"
        apply (induction n)
        using assms apply simp
        apply (erule conjE)+
        apply (rule conjI)
         apply (erule wf_hds_recE)
         apply (rule wf_hds_recI)
          apply (metis TM.steps_l_tps TM.wf_hds_M_rec length_map wf_hds)
         apply simp
         apply (subst TM.step_def)
         apply auto
        unfolding TM.next_actions_def
       proof (erule in_set_zipE)+
         fix n :: nat and a and b and ba
         assume a1: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (left a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a2: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (right a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a3: "length (tapes ((TM.step M ^^ n) c)) = tape_count (Rep_TM M)" and
                a4: "head ` set (tapes ((TM.step M ^^ n) c)) \<subseteq>
                     tape_symbols_rec (Rep_TM M)" and
                a5: "ba \<in> set (tapes ((TM.step M ^^ n) c))" and
                a6: "a \<in> set (TM.next_writes M (state ((TM.step M ^^ n) c))
                     (heads ((TM.step M ^^ n) c)))" and
                a7: "b \<in> set (TM.next_moves M (state ((TM.step M ^^ n) c))
                     (heads ((TM.step M ^^ n) c)))" and
                a8: "state ((TM.step M ^^ n) c) \<in> TM.TM.states M"
         have 1: "\<And>x.
          x < TM.TM.tape_count M \<Longrightarrow> TM.TM.next_write M (state ((TM.step M ^^ n) c))
          (heads ((TM.step M ^^ n) c)) x \<in> options (TM.symbols M)"
           apply standard
              apply (rule a8)
           using a3 apply (simp add: TM.TM.tape_count_def)
           by (metis TM.wf_hds_M_rec a3 a4 length_map list.set_map wf_hds_recI)
         show "head (TM_abbrevs.tape_action (a, b) ba) \<in> tape_symbols_rec (Rep_TM M)"
           unfolding TM_abbrevs.tape_action_def apply simp
           apply (cases b)
           apply simp_all
             apply (smt (verit, ccfv_threshold) None_in_options TM.TM.symbols_def
               UnionI a1 a5 head_in_left_tape head_left_empty image_iff
               left_after_write subset_eq)
            apply (smt (verit, ccfv_SIG) None_in_options TM.TM.symbols_def UnionI
               a2 a5 head_in_right_tape head_right_empty image_iff in_mono
               right_after_write)
           unfolding TM_abbrevs.tape_shift.simps(5)
           using a6 [unfolded TM.next_writes_def, simplified] apply auto
           using 1 by (simp add: TM.TM.symbols_def TM_abbrevs.tape_write_hd)
       next
         fix n::nat and x and xa
         assume a1: "wf_hds_rec (Rep_TM M) (heads ((TM.step M ^^ n) c))" and
                a2: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (left a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a3: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (right a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a4: "state ((TM.step M ^^ n) c) \<in> TM.TM.states M" and
                a5: "xa \<in> set (tapes (TM.step M ((TM.step M ^^ n) c)))" and
                a6: "x \<in> set (left xa)"
         show "x \<in> options (TM.TM.symbols M)"
           apply (cases "state ((TM.step M ^^ n) c) \<in> TM.TM.final_states M")
            apply (metis (no_types, lifting) TM.step_def UN_upper a2 a5 a6 in_mono)
           apply (insert a5)
           apply (subst (asm) TM.step_def)
           apply auto
           unfolding TM.next_actions_def
           apply (erule in_set_zipE)+
           unfolding TM.next_writes_def TM.next_moves_def apply auto
           unfolding TM_abbrevs.tape_action_def apply auto
         proof -
           fix ba and xb and xaa
           assume a7: "xa = TM_abbrevs.tape_shift
    (TM.TM.next_move M (state ((TM.step M ^^ n) c)) (heads ((TM.step M ^^ n) c)) xaa)
    (TM_abbrevs.tape_write
    (TM.TM.next_write M (state ((TM.step M ^^ n) c)) (heads ((TM.step M ^^ n) c)) xb)
    ba)" and
                 a8: "ba \<in> set (tapes ((TM.step M ^^ n) c))" and
                 a9: "xb < TM.TM.tape_count M" and a10: "xaa < TM.TM.tape_count M"
           show "x \<in> options (TM.TM.symbols M)"
             using a6 [unfolded a7]
             apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) c))
                     (heads ((TM.step M ^^ n) c)) xaa")
             apply auto
             apply (metis SUP_le_iff a2 a8 list.sel(2) list.set_sel(2) subset_code(1))
               apply (metis TM.next_write_valid TM.wf_hds_M_rec
                 TM_abbrevs.tape_write_hd a1 a4 a9)
             using a2 a8 apply auto
             by (simp add: SUP_le_iff TM_abbrevs.tape_shift.simps(5) subset_code(1))
         qed
       next
        fix n::nat and x and xa
         assume a1: "wf_hds_rec (Rep_TM M) (heads ((TM.step M ^^ n) c))" and
                a2: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (left a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a3: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (right a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a4: "state ((TM.step M ^^ n) c) \<in> TM.TM.states M" and
                a5: "xa \<in> set (tapes (TM.step M ((TM.step M ^^ n) c)))" and
                a6: "x \<in> set (right xa)"
         show "x \<in> options (TM.TM.symbols M)"
           apply (cases "state ((TM.step M ^^ n) c) \<in> TM.TM.final_states M")
           apply (metis (no_types, lifting) SUP_le_iff TM.step_def a3 a5 a6 subsetD)
           apply (insert a5)
           apply (subst (asm) TM.step_def)
           apply auto
           unfolding TM.next_actions_def
           apply (erule in_set_zipE)+
           unfolding TM.next_writes_def TM.next_moves_def apply auto
           unfolding TM_abbrevs.tape_action_def apply auto
         proof -
           fix ba and xb and xaa
           assume a7: "xa = TM_abbrevs.tape_shift
    (TM.TM.next_move M (state ((TM.step M ^^ n) c)) (heads ((TM.step M ^^ n) c)) xaa)
    (TM_abbrevs.tape_write
    (TM.TM.next_write M (state ((TM.step M ^^ n) c)) (heads ((TM.step M ^^ n) c)) xb)
    ba)" and
                 a8: "ba \<in> set (tapes ((TM.step M ^^ n) c))" and
                 a9: "xb < TM.TM.tape_count M" and a10: "xaa < TM.TM.tape_count M"
           show "x \<in> options (TM.TM.symbols M)"
             using a6 [unfolded a7]
             apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) c))
                     (heads ((TM.step M ^^ n) c)) xaa")
             apply auto
                apply (metis TM.next_write_valid TM.wf_hds_M_rec
                 TM_abbrevs.tape_write_hd a1 a4 a9)
             using a3 a8 apply auto
              apply (metis (no_types, lifting) SUP_le_iff list.sel(2) list.set_sel(2)
                 subsetD)
             by (simp add: SUP_le_iff TM_abbrevs.tape_shift.simps(5) subset_code(1))
         qed
       next
         fix n :: nat
         assume a1: "wf_hds_rec (Rep_TM M) (heads ((TM.step M ^^ n) c))" and
                a2: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (left a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a3: "(\<Union>a\<in>set (tapes ((TM.step M ^^ n) c)). set (right a))
                     \<subseteq> options (TM.TM.symbols M)" and
                a4: "state ((TM.step M ^^ n) c) \<in> TM.TM.states M"
         show "state (TM.step M ((TM.step M ^^ n) c)) \<in> TM.TM.states M"
           apply (subst TM.step_def)
           apply auto
           by (meson TM.wf_hds_M_rec TM_axioms(10) a1 a4)
       qed
     qed
    have "state (TM.steps M n c) \<in> TM.states M"
      using 2 by blast
    show "state (TM.step (Abs_TM (map_states_tmrec f M))
          ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
          (TM_config (f (state c)) (tapes c)))) =
          f (state (TM.step M ((TM.step M ^^ n) c)))"
      unfolding 1 by (rule map_states_tmrec_step_state) fact+
    show "tapes (TM.step (Abs_TM (map_states_tmrec f M))
          ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
          (TM_config (f (state c)) (tapes c)))) =
          tapes (TM.step M ((TM.step M ^^ n) c))"
      unfolding 1 by (rule map_states_tmrec_step_tapes) fact+
  qed
  show "state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
       (TM_config (f (state c)) (tapes c))) = f (state ((TM.step M ^^ n) c))"
    using 1 by simp
  show "tapes ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
       (TM_config (f (state c)) (tapes c))) = tapes ((TM.step M ^^ n) c)"
    using 1 by simp
qed

lemma map_states_tmrec_run:
  fixes f :: "'a \<Rightarrow> 'b" and M :: "('a, 's, 'l) TM" and w :: "'s list" and n :: nat
  assumes f_inj: "inj_on f (TM.states M)" and w_wf: "set w \<subseteq> TM.symbols M"
  defines "run \<equiv> TM.run M n w" and
          "run' \<equiv> TM.run (Abs_TM (map_states_tmrec f M)) n w"
        shows map_states_tmrec_run_state [simp]: "state run' = f (state run)"
          and map_states_tmrec_run_tapes [simp]: "tapes run' = tapes run"
  unfolding run_def run'_def
proof -
  have state_init_conf_in_M: "state (TM.initial_config M w) \<in> TM.states M"
    by (simp add: TM.init_conf_state)
  have 1: "state (TM.initial_config (Abs_TM (map_states_tmrec f M)) w) =
           f (state (TM.initial_config M w))" unfolding TM.init_conf_state
    unfolding valid_tm_initial_state [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] by simp
  have 2: "tapes (TM.initial_config (Abs_TM (map_states_tmrec f M)) w) =
           tapes (TM.initial_config M w)"
    unfolding TM.same_tape_count_same_init_tapes
      valid_tm_tape_count [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] by simp
  have 3: "TM.initial_config (Abs_TM (map_states_tmrec f M)) w =
           TM_config (f (state (TM.initial_config M w)))
           (tapes (TM.initial_config M w))" using 1 2 by (metis TM_config.collapse)
  show "state (TM.run (Abs_TM (map_states_tmrec f M)) n w) = f (state (TM.run M n w))"
    unfolding TM.run_def 3
    apply (rule map_states_tmrec_steps_state)
        apply fact+
      apply (rule wf_hds_recI)
    apply (simp add: TM.TM.tape_count_def TM.init_conf_len)
      apply (meson TM.wf_config_iff TM.wf_hds_M_rec TM.wf_initial_config lists_member
        w_wf wf_hds_recD(2)) apply auto
     apply (metis TM.wf_configD(3) TM.wf_initial_config lists_member set_options_eq
        subsetD subsetI tape.set_sel(1) w_wf)
    by (metis TM.wf_configD(3) TM.wf_initial_config lists_member set_options_eq
        subsetD subsetI tape.set_sel(3) w_wf)
  show "tapes (TM.run (Abs_TM (map_states_tmrec f M)) n w) = tapes (TM.run M n w)"
    unfolding TM.run_def 3
    apply (rule map_states_tmrec_steps_tapes)
        apply fact+
      apply (rule wf_hds_recI)
    apply (simp add: TM.TM.tape_count_def TM.init_conf_len)
      apply (meson TM.wf_config_iff TM.wf_hds_M_rec TM.wf_initial_config lists_member
        w_wf wf_hds_recD(2)) apply auto
     apply (metis TM.wf_configD(3) TM.wf_initial_config lists_member set_options_eq
        subsetD subsetI tape.set_sel(1) w_wf)
    by (metis TM.wf_configD(3) TM.wf_initial_config lists_member set_options_eq
        subsetD subsetI tape.set_sel(3) w_wf)
qed

lemma map_states_tmrec_halts_iff:
  fixes f :: "'a \<Rightarrow> 'b" and M :: "('a, 's, 'l) TM" and w :: "'s list" and n :: nat
  assumes f_inj: "inj_on f (TM.states M)" and w_wf: "set w \<subseteq> TM.symbols M"
  shows "TM.halts (Abs_TM (map_states_tmrec f M)) w \<longleftrightarrow>
         TM.halts M w"
  unfolding TM.halts_def TM.halts_config_def apply auto
proof
  fix n :: nat
  have 1: "\<And>s. s \<in> TM.final_states M \<Longrightarrow> f s \<in> final_states (map_states_tmrec f M)"
    unfolding map_states_tmrec_def [OF f_inj] using f_inj by auto
  have 2: "\<And>s. f s \<in> final_states (map_states_tmrec f M) \<Longrightarrow> s \<in> TM.states M \<Longrightarrow>
           s \<in> TM.final_states M"
    unfolding map_states_tmrec_def [OF f_inj] apply auto
    by (metis TM.final_states_valid f_inj inj_onD)
  have 3: "state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
           (TM.initial_config (Abs_TM (map_states_tmrec f M)) w)) =
           f (state ((TM.step M ^^ n) (TM.initial_config M w)))"
    by (metis TM.run_def f_inj map_states_tmrec_run_state w_wf)
  show "TM.is_final (Abs_TM (map_states_tmrec f M))
          ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
            (TM.initial_config (Abs_TM (map_states_tmrec f M)) w)) \<Longrightarrow>
         TM.is_final M ((TM.step M ^^ n) (TM.initial_config M w))"
    unfolding TM.is_final_def valid_tm_final_states
      [OF map_states_tmrec_valid [OF f_inj]] 3
    apply (erule 2)
    by (simp add: TM.wf_configD(1) TM.wf_initial_config TM.wf_steps w_wf)
  show "TM.is_final M ((TM.step M ^^ n) (TM.initial_config M w)) \<Longrightarrow>
         \<exists>n. TM.is_final (Abs_TM (map_states_tmrec f M))
         ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
         (TM.initial_config (Abs_TM (map_states_tmrec f M)) w))"
    apply (rule exI [where x=n])
    unfolding TM.is_final_def valid_tm_final_states
      [OF map_states_tmrec_valid [OF f_inj]]
    apply (drule 1)
    by (fold 3)
qed

lemma map_states_tmrec_decides_iff:
  assumes f_inj: "inj_on f (TM.states M)"
  shows "TM_decider.decides (Abs_TM (map_states_tmrec f M)) L \<longleftrightarrow>
         TM_decider.decides M L"
  apply auto unfolding valid_tm_symbols [OF map_states_tmrec_valid [OF f_inj]]
     apply (simp add: f_inj in_mono map_states_tmrec_def)
proof (rule TM_decider.decides_wordI)
  fix w :: "'c list"
  assume a1: "alphabet L \<subseteq> symbols (map_states_tmrec f M)" and
         a2: "\<forall>w\<in>(alphabet L)*.
              TM_decider.decides_word (Abs_TM (map_states_tmrec f M)) L w" and
         a3: "set w \<subseteq> alphabet L"
  hence "TM_decider.decides_word (Abs_TM (map_states_tmrec f M)) L w" by simp
  hence "TM.halts (Abs_TM (map_states_tmrec f M)) w"
    by (rule TM_decider.decides_halts)
  thus "TM.halts M w"
    by (smt (verit, best) a1 a3 f_inj map_states_tmrec_def map_states_tmrec_halts_iff
        order_trans select_convs(2))
next
  fix w :: "'c list"
  assume a1: "alphabet L \<subseteq> symbols (map_states_tmrec f M)" and
         a2: "\<forall>w\<in>(alphabet L)*.
              TM_decider.decides_word (Abs_TM (map_states_tmrec f M)) L w" and
         a3: "set w \<subseteq> alphabet L" and a4: "w \<in>\<^sub>L L"
  hence 1: "TM_decider.accepts (Abs_TM (map_states_tmrec f M)) w"
    using TM_decider.decides_def by blast
  have states_eq: "\<And>n. state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
        (TM.initial_config (Abs_TM (map_states_tmrec f M)) w)) =
        f (state (TM.steps M n (TM.initial_config M w)))"
    apply (rule map_states_tmrec_run_state [unfolded TM.run_def])
     apply fact
    using a1 a3 f_inj map_states_tmrec_def by fastforce
  have 2: "\<And>n. TM.is_final (Abs_TM (map_states_tmrec f M))
             ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
             (TM.initial_config (Abs_TM (map_states_tmrec f M)) w)) \<longleftrightarrow>
             TM.is_final M ((TM.step M ^^ n) (TM.initial_config M w))"
    apply auto unfolding TM.is_final_def states_eq
  proof -
    fix n :: nat
    assume "f (state ((TM.step M ^^ n) (TM.initial_config M w)))
            \<in> TM.TM.final_states (Abs_TM (map_states_tmrec f M))"
    moreover have "state ((TM.step M ^^ n) (TM.initial_config M w)) \<in> TM.states M"
      apply (rule TM.wf_config_run [unfolded TM.wf_config_def, THEN conjunct1,
          unfolded TM.run_def]) using a1 a3
      unfolding map_states_tmrec_def [OF f_inj] by simp
    ultimately show "state ((TM.step M ^^ n) (TM.initial_config M w)) \<in>
                     TM.TM.final_states M"
      by (smt (verit, ccfv_SIG) TM.final_states_valid f_inj inj_onD
          map_states_tmrec_def map_states_tmrec_valid mem_Collect_eq select_convs(5)
          valid_tm_final_states)
  next
    fix n :: nat
    assume a1: "state ((TM.step M ^^ n) (TM.initial_config M w)) \<in>
                TM.TM.final_states M"
    thus "f (state ((TM.step M ^^ n) (TM.initial_config M w)))
          \<in> TM.TM.final_states (Abs_TM (map_states_tmrec f M))"
      by (metis (no_types, opaque_lifting) 1 TM.final_le_run TM.halts_altdef
          TM.is_final_def TM.run_def TM_decider.accepts_halts nle_le states_eq)
  qed
  hence Leasts_eq: "(LEAST n. TM.is_final M ((TM.step M ^^ n)
                   (TM.initial_config M w))) =
                   (LEAST n. TM.is_final (Abs_TM (map_states_tmrec f M))
                   ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
                   (TM.initial_config (Abs_TM (map_states_tmrec f M)) w)))"
    by simp
  have "f (state ((TM.step M ^^ (LEAST n. TM.is_final M ((TM.step M ^^ n)
           (TM.initial_config M w)))) (TM.initial_config M w))) =
           state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^
            (LEAST n. TM.is_final (Abs_TM (map_states_tmrec f M))
            ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
           (TM.initial_config (Abs_TM (map_states_tmrec f M)) w))))
           (TM.initial_config (Abs_TM (map_states_tmrec f M)) w))"
    unfolding Leasts_eq [symmetric]
    apply (rule sym)
    apply (rule map_states_tmrec_run_state [unfolded TM.run_def])
     apply fact
    using a1 a3 f_inj map_states_tmrec_def by fastforce
  hence 2: "state ((TM.step M ^^ (LEAST n. TM.is_final M ((TM.step M ^^ n)
           (TM.initial_config M w)))) (TM.initial_config M w)) =
           (THE s. f s = (state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^
            (LEAST n. TM.is_final (Abs_TM (map_states_tmrec f M))
            ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
           (TM.initial_config (Abs_TM (map_states_tmrec f M)) w))))
           (TM.initial_config (Abs_TM (map_states_tmrec f M)) w))) \<and> s \<in> TM.states M)"
    unfolding Leasts_eq [symmetric] using f_inj
    by (smt (verit, best) 1 LeastI TM.final_states_valid TM.halts_altdef
        TM.run_def TM_decider.accepts_halts 2 inj_on_contraD is_finalD the_equality)
  have 3: "\<And>s. s \<in> TM_decider.accepting_states (Abs_TM (map_states_tmrec f M)) \<Longrightarrow>
        (THE y. f y = s \<and> y \<in> TM.states M) \<in> TM_decider.accepting_states M"
    unfolding TM_decider.acc_def valid_tm_final_states 
      [OF map_states_tmrec_valid [OF f_inj]] valid_tm_label
      [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] apply auto
    by (smt (verit, ccfv_threshold) TM.final_states_valid f_inj inj_on_def theI')+
  show "TM_decider.accepts M w" unfolding TM_decider.accepts_def
      TM.compute_def TM.compute_config_def 2
    apply (rule 3)
    using 1 by (simp add: TM.compute_config_def TM.compute_def TM_decider.accepts_def)
next
  fix w :: "'c list"
  assume a1: "alphabet L \<subseteq> symbols (map_states_tmrec f M)" and
         a2: "\<forall>w\<in>(alphabet L)*.
              TM_decider.decides_word (Abs_TM (map_states_tmrec f M)) L w" and
         a3: "set w \<subseteq> alphabet L" and a4: "TM_decider.accepts M w"
  hence 1: "TM_decider.decides_word (Abs_TM (map_states_tmrec f M)) L w" by simp
  have 2: "\<And>s. s \<in> TM_decider.accepting_states M \<Longrightarrow>
           f s \<in> TM_decider.accepting_states (Abs_TM (map_states_tmrec f M))"
    unfolding TM_decider.acc_def apply auto
    unfolding valid_tm_final_states [OF map_states_tmrec_valid [OF f_inj]]
      valid_tm_label [OF map_states_tmrec_valid [OF f_inj]]
    unfolding map_states_tmrec_def [OF f_inj] apply auto
    by (smt (verit, ccfv_threshold) TM.final_states_valid f_inj inj_on_contraD
        theI_unique)
  have "TM_decider.accepts (Abs_TM (map_states_tmrec f M)) w"
    unfolding TM_decider.accepts_def TM.compute_def TM.compute_config_def
    using a4 2
    by (smt (verit, best) 1 Least_eqD TM.final_run_compute TM.run_def
        TM_decider.accepts_altdef TM_decider.accepts_def TM_decider.decides_halts
        a1 a3 dual_order.trans f_inj haltsD map_states_tmrec_def
        map_states_tmrec_run_state select_convs(2))
  thus "w \<in>\<^sub>L L" using 1 TM_decider.decides_def by blast
next
  fix s :: 'c
  show "alphabet L \<subseteq> TM.TM.symbols M \<Longrightarrow>
        \<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w \<Longrightarrow>
        s \<in> alphabet L \<Longrightarrow> s \<in> symbols (map_states_tmrec f M)"
    by (simp add: f_inj in_mono map_states_tmrec_def)
next
  fix w :: "'c list"
  assume a1: "alphabet L \<subseteq> TM.TM.symbols M" and
         a2: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w" and
         a3: "set w \<subseteq> alphabet L"
  show "TM_decider.decides_word (Abs_TM (map_states_tmrec f M)) L w"
    apply (rule TM_decider.decides_wordI)
      apply (meson TM_decider.decides_halts a1 a2 a3 f_inj lists_member
        map_states_tmrec_halts_iff order.trans)
  proof -
    assume a4: "w \<in>\<^sub>L L"
    hence "TM_decider.accepts M w" using a2 a3
      by (simp add: TM_decider.decides_altdef4)
    moreover have "\<And>s. s \<in> TM_decider.accepting_states M \<Longrightarrow>
                   f s \<in> TM_decider.accepting_states (Abs_TM (map_states_tmrec f M))"
      unfolding TM_decider.acc_def apply auto
      unfolding valid_tm_final_states [OF map_states_tmrec_valid [OF f_inj]]
        valid_tm_label [OF map_states_tmrec_valid [OF f_inj]]
       apply (smt (verit, ccfv_SIG) f_inj map_states_tmrec_def mem_Collect_eq
          select_convs(5))
      unfolding map_states_tmrec_def [OF f_inj] apply auto
      by (smt (verit, del_insts) TM.final_states_valid f_inj inj_on_contraD theI)
    ultimately show "TM_decider.accepts (Abs_TM (map_states_tmrec f M)) w"
      by (metis (mono_tags, lifting) TM_decider.accepts_altdef a1 a3 dual_order.trans
          f_inj map_states_tmrec_run_state)
  next
    assume a4: "TM_decider.accepts (Abs_TM (map_states_tmrec f M)) w"
    have "\<And>s. f s \<in> TM_decider.accepting_states (Abs_TM (map_states_tmrec f M)) \<Longrightarrow>
              s \<in> TM.states M \<Longrightarrow> s \<in> TM_decider.accepting_states M"
      unfolding TM_decider.acc_def apply auto
      unfolding valid_tm_final_states [OF map_states_tmrec_valid [OF f_inj]]
        valid_tm_label [OF map_states_tmrec_valid [OF f_inj]]
       apply (smt (verit, ccfv_threshold) TM.final_states_valid f_inj inj_onD
          map_states_tmrec_def mem_Collect_eq select_convs(5))
      unfolding map_states_tmrec_def [OF f_inj] apply auto
      by (smt (verit, del_insts) f_inj inv_into_f_f theI_unique)
    hence "TM_decider.accepts M w" using a4
      by (smt (verit, ccfv_threshold) TM.wf_configD(1) TM.wf_config_run
          TM_decider.accepts_altdef a1 a3 dual_order.trans f_inj lists_member
          map_states_tmrec_run_state)
    thus "w \<in>\<^sub>L L" using a2 a3 TM_decider.decides_def by blast
  qed
qed

lemma map_states_tmrec_comp:
  assumes f_inj: "inj_on f (TM.states M)" and w_wf: "set w \<subseteq> TM.symbols M"
  shows map_states_tmrec_comp_state:
    "state (TM.compute (Abs_TM (map_states_tmrec f M)) w) =
     f (state (TM.compute M w))" and
        map_states_tmrec_comp_tapes:
    "tapes (TM.compute (Abs_TM (map_states_tmrec f M)) w) = tapes (TM.compute M w)"
proof -
  have states_eq: "\<And>n. state ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
        (TM.initial_config (Abs_TM (map_states_tmrec f M)) w)) =
        f (state (TM.steps M n (TM.initial_config M w)))"
    apply (rule map_states_tmrec_run_state [unfolded TM.run_def])
     apply fact
    using w_wf by blast
  have 1: "\<And>n. TM.is_final (Abs_TM (map_states_tmrec f M))
             ((TM.step (Abs_TM (map_states_tmrec f M)) ^^ n)
             (TM.initial_config (Abs_TM (map_states_tmrec f M)) w)) \<longleftrightarrow>
             TM.is_final M ((TM.step M ^^ n) (TM.initial_config M w))"
    apply auto unfolding TM.is_final_def states_eq
  proof -
    fix n :: nat
    assume "f (state ((TM.step M ^^ n) (TM.initial_config M w)))
            \<in> TM.TM.final_states (Abs_TM (map_states_tmrec f M))"
    moreover have "state ((TM.step M ^^ n) (TM.initial_config M w)) \<in> TM.states M"
      apply (rule TM.wf_config_run [unfolded TM.wf_config_def, THEN conjunct1,
          unfolded TM.run_def]) using w_wf
      unfolding map_states_tmrec_def [OF f_inj] by simp
    ultimately show "state ((TM.step M ^^ n) (TM.initial_config M w)) \<in>
                     TM.TM.final_states M"
      by (smt (verit, ccfv_SIG) TM.final_states_valid f_inj inj_onD
          map_states_tmrec_def map_states_tmrec_valid mem_Collect_eq select_convs(5)
          valid_tm_final_states)
  next
    fix n :: nat
    assume a1: "state ((TM.step M ^^ n) (TM.initial_config M w)) \<in>
                TM.TM.final_states M"
    thus "f (state ((TM.step M ^^ n) (TM.initial_config M w)))
          \<in> TM.TM.final_states (Abs_TM (map_states_tmrec f M))"
      by (smt (verit, del_insts) f_inj map_states_tmrec_def map_states_tmrec_valid
          mem_Collect_eq select_convs(5) valid_tm_final_states)
  qed
  show "state (TM.compute (Abs_TM (map_states_tmrec f M)) w) =
        f (state (TM.compute M w))" unfolding TM.compute_def TM.compute_config_def
    1 apply (rule map_states_tmrec_run_state [unfolded TM.run_def])
    by fact+
  show "tapes (TM.compute (Abs_TM (map_states_tmrec f M)) w) = tapes (TM.compute M w)"
    unfolding TM.compute_def TM.compute_config_def 1
    apply (rule map_states_tmrec_run_tapes [unfolded TM.run_def])
    by fact+
qed

lemma map_states_tmrec_comp_word_iff:
  assumes f_inj: "inj_on f (TM.states M)" and wi_wf: "set wi \<subseteq> TM.symbols M"
  shows "TM.computes_word (Abs_TM (map_states_tmrec f M)) wi wo \<longleftrightarrow>
         TM.computes_word M wi wo"
  unfolding TM.computes_word_def apply auto
  using f_inj wi_wf apply (simp add: map_states_tmrec_halts_iff)
    apply (rule TM.has_outputI)
    apply (drule TM.has_outputD)
    apply (simp add: f_inj wi_wf map_states_tmrec_comp_tapes)
   apply (simp add: f_inj wi_wf map_states_tmrec_halts_iff)
  by (simp add: TM.has_output_altdef f_inj wi_wf map_states_tmrec_comp_tapes)

lemma no_final_states_not_decides: "TM.final_states M = {} \<Longrightarrow>
                                    \<not>TM_decider.decides M L"
proof (rule notI, erule conjE)
  assume a1: "TM.TM.final_states M = {}" and
         a2: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w"
  have "\<not>TM.halts M w" for w
    unfolding TM.halts_def TM.halts_config_def TM.is_final_def a1 by blast
  thus False using a2 TM_decider.decides_halts by blast
qed

definition tm_extra_symbols :: "('q, 's, 'l) TM \<Rightarrow> 's set \<Rightarrow> ('q, 's, 'l) TM_record"
  where "tm_extra_symbols M S \<equiv> TM (TM.tape_count M) (TM.symbols M \<union> S) (TM.states M)
         (TM.initial_state M) (TM.final_states M) (TM.label M)
         (\<lambda>st hds. if (\<exists>so\<in>set hds. \<exists>s. so = Some s \<and> s \<in> S \<and> s \<notin> TM.symbols M) then
            (if TM.final_states M = {} then TM.initial_state M else
            (SOME fs. fs \<in> TM.final_states M)) else TM.next_state M st hds)
         (\<lambda>st hds k. if (\<exists>so\<in>set hds. \<exists>s. so = Some s \<and> s \<in> S \<and> s \<notin> TM.symbols M)
            then hds ! 0 else TM.next_write M st hds k)
         (\<lambda>st hds k. if (\<exists>so\<in>set hds. \<exists>s. so = Some s \<and> s \<in> S \<and> s \<notin> TM.symbols M)
            then No_Shift else TM.next_move M st hds k)"

lemma tm_extra_symbols_valid: "finite S \<Longrightarrow> valid_TM (tm_extra_symbols M S)"
  apply standard
  unfolding tm_extra_symbols_def apply auto
     apply standard
       apply auto
proof -
  fix q :: 'b and hds :: "'a option list" and x :: "'a option"
  assume a1: "finite S" and a2: "q \<in> TM.TM.states M" and
         a3: "length hds = TM.TM.tape_count M" and
         a4: "set hds \<subseteq> options (TM.TM.symbols M \<union> S)" and
         a5: "TM.TM.final_states M = {}" and
         a6: "\<forall>so\<in>set hds. \<forall>s. s \<in> S \<longrightarrow> so = Some s \<longrightarrow> s \<in> TM.TM.symbols M" and
         a7: "x \<in> set hds"
  show "x \<in> options (TM.TM.symbols M)"
    apply (cases x)
     apply auto
    using a4 a7 a6 by auto
next
  fix x :: 'b
  assume a1: "x \<in> TM.TM.final_states M"
  hence "(SOME fs. fs \<in> TM.TM.final_states M) \<in> TM.TM.final_states M" by (rule someI)
  thus "(SOME fs. fs \<in> TM.TM.final_states M) \<in> TM.TM.states M" by auto
next
  fix q x :: 'b and hds :: "'a option list"
  assume a1: "finite S" and a2: "q \<in> TM.TM.states M" and
         a3: "length hds = TM.TM.tape_count M" and
         a4: "set hds \<subseteq> options (TM.TM.symbols M \<union> S)" and
         a5: "x \<in> TM.TM.final_states M" and
         a6: "\<forall>so\<in>set hds. \<forall>s. s \<in> S \<longrightarrow> so = Some s \<longrightarrow> s \<in> TM.TM.symbols M"
  hence 1: "\<And>so s. so \<in> set hds \<Longrightarrow> s \<in> S \<Longrightarrow> so = Some s \<Longrightarrow> s \<in> TM.symbols M"
    by simp
  hence 2: "\<And>so s. so \<in> set hds \<Longrightarrow> s \<in> S \<Longrightarrow> so = Some s \<Longrightarrow> s \<notin> S - TM.symbols M"
    by simp
  have 3: "\<And>so s. so \<in> set hds \<Longrightarrow> so = Some s \<Longrightarrow> s \<notin> S \<Longrightarrow> s \<in> TM.symbols M"
    using a4 by auto
  have 4: "set hds \<subseteq> options (TM.TM.symbols M)" using 1 2 3 a4 apply auto
    apply (drule subsetD) apply assumption
    using set_options_eq by force
  show "TM.TM.next_state M q hds \<in> TM.TM.states M" using a2 a3 4 by simp
next
  fix q :: 'b and hds :: "'a option list" and i :: nat
  assume a1: "finite S" and a2: "q \<in> TM.TM.states M" and
         a3: "i < TM.TM.tape_count M" and a4: "length hds = TM.TM.tape_count M" and
         a5: "set hds \<subseteq> options (TM.TM.symbols M \<union> S)" and
         a6: "\<forall>so\<in>set hds. \<forall>s. s \<in> S \<longrightarrow> so = Some s \<longrightarrow> s \<in> TM.TM.symbols M"
  hence 1: "\<And>so s. so \<in> set hds \<Longrightarrow> s \<in> S \<Longrightarrow> so = Some s \<Longrightarrow> s \<in> TM.symbols M"
    by simp
  hence 2: "\<And>so s. so \<in> set hds \<Longrightarrow> s \<in> S \<Longrightarrow> so = Some s \<Longrightarrow> s \<notin> S - TM.symbols M"
    by simp
  have 3: "\<And>so s. so \<in> set hds \<Longrightarrow> so = Some s \<Longrightarrow> s \<notin> S \<Longrightarrow> s \<in> TM.symbols M"
    using a5 by auto
  have 4: "set hds \<subseteq> options (TM.TM.symbols M)" using 1 2 3 a5 apply auto
    apply (drule subsetD) apply assumption
    using set_options_eq by force
  have "TM.TM.next_write M q hds i \<in> options (TM.TM.symbols M)"
    using a2 a3 a4 4 by simp
  thus "TM.TM.next_write M q hds i \<in> options (TM.TM.symbols M \<union> S)"
    by (simp add: options_union)
qed

definition tm_extra_states :: "('q, 's, 'l) TM \<Rightarrow> 'q set \<Rightarrow> ('q, 's, 'l) TM_record"
  where "tm_extra_states M S \<equiv> TM (TM.tape_count M) (TM.symbols M) (TM.states M \<union> S)
         (TM.initial_state M) (TM.final_states M) (TM.label M)
         (\<lambda>st hds. if st \<in> S \<and> st \<notin> TM.states M then
            (if TM.final_states M = {} then TM.initial_state M else
            (SOME fs. fs \<in> TM.final_states M)) else TM.next_state M st hds)
         (\<lambda>st hds k. if st \<in> S \<and> st \<notin> TM.states M
            then hds ! 0 else TM.next_write M st hds k)
         (\<lambda>st hds k. if st \<in> S \<and> st \<notin> TM.states M
            then No_Shift else TM.next_move M st hds k)"

lemma tm_extra_states_valid: "finite S \<Longrightarrow> valid_TM (tm_extra_states M S)"
  apply standard
  unfolding tm_extra_states_def apply auto
  by (meson TM.final_states_valid someI_ex)

lemma tm_extra_symbols_step:
  fixes M :: "('q, 's, 'l) TM" and S :: "'s set" and c :: "('q, 's) TM_config"
  assumes c_symbols: "\<And>s. s \<in> TM.symbols_in_config c \<Longrightarrow> s \<in> TM.symbols M" and
          finite_S: "finite S"
        shows "TM.step (Abs_TM (tm_extra_symbols M S)) c = TM.step M c"
proof -
  have valid [simp, intro]: "valid_TM (tm_extra_symbols M S)"
    by (rule tm_extra_symbols_valid) fact
  have [simp]: "TM.tape_count (Abs_TM (tm_extra_symbols M S)) = TM.tape_count M"
    unfolding valid_tm_tape_count [OF valid]
    unfolding tm_extra_symbols_def by simp
    show ?thesis
  unfolding TM.step_def apply auto
    apply (smt (verit) finite_S select_convs(5) tm_extra_symbols_def
      tm_extra_symbols_valid valid_tm_final_states)+
  unfolding TM.step_not_final_def Let_def apply auto
  unfolding valid_tm_next_state [OF valid]
   apply (subst tm_extra_symbols_def) apply auto
  using c_symbols [unfolded TM.symbols_in_config_def]
    apply (metis (no_types, lifting) Some_options_iff TM.set_tape_valid
      mem_Collect_eq subsetI)+
  apply (rule nth_equalityI)
   apply auto unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
   apply auto unfolding valid_tm_next_write [OF valid] valid_tm_next_move [OF valid]
  apply (subst (1 2) tm_extra_symbols_def) apply auto
  by (metis (no_types, lifting) Some_options_iff TM.set_tape_valid
      c_symbols [unfolded TM.symbols_in_config_def] mem_Collect_eq subsetI)
qed

lemma tm_extra_symbols_syms: "finite S \<Longrightarrow>
                              TM.symbols (Abs_TM (tm_extra_symbols M S)) =
                              TM.symbols M \<union> S"
  by (metis (no_types, lifting) select_convs(2) tm_extra_symbols_def
      tm_extra_symbols_valid valid_tm_symbols)

lemma tm_extra_symbols_steps:
  fixes M :: "('q, 's, 'l) TM" and S :: "'s set" and c :: "('q, 's) TM_config"
  assumes c_symbols: "\<And>s. s \<in> TM.symbols_in_config c \<Longrightarrow> s \<in> TM.symbols M" and
          finite_S: "finite S" and state_c: "state c \<in> TM.states M" and
          length_hds: "length (heads c) = TM.tape_count M"
        shows "TM.steps (Abs_TM (tm_extra_symbols M S)) n c = TM.steps M n c"
proof -
  have 1: "s \<in> TM.symbols_in_config (TM.steps M n c) \<Longrightarrow> s \<in> TM.symbols M"
    for n :: nat and s :: 's
  proof (induction n arbitrary: s)
    case 0
    then show ?case by (simp add: c_symbols)
  next
    case (Suc n)
    then show ?case apply simp
      apply (erule TM.symbols_in_config_after_step)
        apply auto using state_c length_hds
       apply (smt (verit, best) TM.symbols_in_config_def TM.wf_configD(1)
          TM.wf_configI TM.wf_steps c_symbols length_map mem_Collect_eq subset_eq)
      using TM.steps_l_tps length_hds by auto
  qed
  show ?thesis
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case IH: (Suc n)
    then show ?case apply (simp add: IH)
      apply (rule tm_extra_symbols_step)
       apply (erule 1)
      by fact
  qed
qed

lemma tm_extra_symbols_run:
  fixes M :: "('q, 's, 'l) TM" and S :: "'s set"
  assumes finite_S: "finite S" and w_in_S: "set w \<subseteq> TM.symbols M"
  shows "TM.run (Abs_TM (tm_extra_symbols M S)) n w = TM.run M n w"
proof (unfold TM.run_def)
  have 1: "TM.initial_config (Abs_TM (tm_extra_symbols M S)) w =
           TM.initial_config M w"
    by (smt (verit, ccfv_threshold) TM.initial_config_def finite_S select_convs(1)
        select_convs(4) tm_extra_symbols_def tm_extra_symbols_valid
        valid_tm_initial_state valid_tm_tape_count)
  show "(TM.step (Abs_TM (tm_extra_symbols M S)) ^^ n)
        (TM.initial_config (Abs_TM (tm_extra_symbols M S)) w) =
        (TM.step M ^^ n) (TM.initial_config M w)"
    unfolding 1
    apply (rule tm_extra_symbols_steps)
    unfolding TM.symbols_in_config_def apply auto
       apply (subst (asm) TM.initial_config_def)
       apply auto unfolding TM_abbrevs.input_tape_def
       apply (cases w)
    using w_in_S apply auto
      apply (rule finite_S)
     apply (simp add: TM.init_conf_state)
    using TM.init_conf_len by blast
qed

lemma tm_extra_symbols_init_conf: "set w \<subseteq> TM.symbols M \<Longrightarrow> finite S \<Longrightarrow>
           TM.initial_config (Abs_TM (tm_extra_symbols M S)) w =
           TM.initial_config M w"
  by (smt (verit, ccfv_threshold) TM.initial_config_def select_convs(1)
        select_convs(4) tm_extra_symbols_def tm_extra_symbols_valid
        valid_tm_initial_state valid_tm_tape_count)

lemma tm_extra_symbols_is_final:
  fixes M :: "('q, 's, 'l) TM" and S :: "'s set"
  assumes "finite S"
  shows "TM.is_final (Abs_TM (tm_extra_symbols M S)) c \<longleftrightarrow>
         TM.is_final M c"
  unfolding TM.is_final_def using assms
  by (smt (verit, ccfv_SIG) select_convs(5) tm_extra_symbols_def
      tm_extra_symbols_valid valid_tm_final_states)

lemma tm_extra_symbols_compute:
  fixes M :: "('q, 's, 'l) TM" and S :: "'s set"
  assumes finite_S: "finite S" and w_in_S: "set w \<subseteq> TM.symbols M"
  shows "TM.compute (Abs_TM (tm_extra_symbols M S)) w = TM.compute M w"
  unfolding TM.compute_def TM.compute_config_def
  tm_extra_symbols_run [unfolded TM.run_def, OF finite_S w_in_S]
  tm_extra_symbols_is_final [OF finite_S] ..

lemma tm_extra_symbols_decides:
  fixes M :: "('q, 's) TM_decider" and S :: "'s set" and L :: "'s lang"
  assumes finite_S: "finite S" and M_decides: "TM_decider.decides M L"
  shows "TM_decider.decides (Abs_TM (tm_extra_symbols M S)) L"
proof
  have 1: "TM.symbols M \<subseteq> TM.symbols (Abs_TM (tm_extra_symbols M S))"
    by (smt (verit, del_insts) Un_upper1 finite_S select_convs(2) tm_extra_symbols_def
        tm_extra_symbols_valid valid_tm_symbols)
  thus "alphabet L \<subseteq> TM.TM.symbols (Abs_TM (tm_extra_symbols M S))"
    using M_decides by auto
  show "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word (Abs_TM (tm_extra_symbols M S)) L w"
  proof auto
    fix w :: "'s list"
    assume a1: "set w \<subseteq> alphabet L"
    hence 2: "set w \<subseteq> TM.symbols (Abs_TM (tm_extra_symbols M S))"
      using M_decides 1 by blast
    have "TM.halts (Abs_TM (tm_extra_symbols M S)) w"
    proof
      have 3: "TM.is_final M (TM.compute M w)" using M_decides
        by (simp add: TM_decider.decides_halts_all a1 halts_compD)
      have 4: "TM.compute (Abs_TM (tm_extra_symbols M S)) w =
               TM.compute M w" apply (rule tm_extra_symbols_compute)
        apply fact
        using M_decides a1 by blast
      show "TM.is_final (Abs_TM (tm_extra_symbols M S))
            (TM.compute (Abs_TM (tm_extra_symbols M S)) w)"
        unfolding 4 apply (rule tm_extra_symbols_is_final [THEN iffD2])
        by fact+
    qed
    moreover have "w \<in>\<^sub>L L \<Longrightarrow> TM_decider.accepts (Abs_TM (tm_extra_symbols M S)) w"
    proof -
      assume a2: "w \<in>\<^sub>L L"
      hence 3: "TM_decider.accepts M w" using M_decides apply auto
        using TM_decider.decides_def a1 by blast
      have 4: "TM.final_states (Abs_TM (tm_extra_symbols M S)) =
               TM.final_states M"
        by (smt (verit, del_insts) finite_S select_convs(5) tm_extra_symbols_def
            tm_extra_symbols_valid valid_tm_final_states)
      have 5: "TM.label (Abs_TM (tm_extra_symbols M S)) = TM.label M"
        by (smt (verit) finite_S select_convs(6) tm_extra_symbols_def
            tm_extra_symbols_valid valid_tm_label)
      have 6: "TM_decider.accepting_states (Abs_TM (tm_extra_symbols M S)) =
               TM_decider.accepting_states M"
        unfolding TM_decider.acc_def 4 5 ..
      have 7: "set w \<subseteq> TM.symbols M"
        using M_decides a1 by blast
      show "TM_decider.accepts (Abs_TM (tm_extra_symbols M S)) w"
        unfolding TM_decider.accepts_def 6 tm_extra_symbols_compute [OF finite_S 7]
        using 3 TM_decider.accepts_def by blast
    qed
    moreover have "TM_decider.accepts (Abs_TM (tm_extra_symbols M S)) w \<Longrightarrow> w \<in>\<^sub>L L"
    proof -
      assume a3: "TM_decider.accepts (Abs_TM (tm_extra_symbols M S)) w"
      have 3: "TM.final_states (Abs_TM (tm_extra_symbols M S)) =
               TM.final_states M"
        by (smt (verit, del_insts) finite_S select_convs(5) tm_extra_symbols_def
            tm_extra_symbols_valid valid_tm_final_states)
      have 4: "TM.label (Abs_TM (tm_extra_symbols M S)) = TM.label M"
        by (smt (verit) finite_S select_convs(6) tm_extra_symbols_def
            tm_extra_symbols_valid valid_tm_label)
      have 5: "TM_decider.accepting_states (Abs_TM (tm_extra_symbols M S)) =
               TM_decider.accepting_states M"
        unfolding TM_decider.acc_def 3 4 ..
      have 6: "set w \<subseteq> TM.symbols M"
        using M_decides a1 by blast
      have "TM_decider.accepts M w"
        using a3 unfolding TM_decider.accepts_def 5
          tm_extra_symbols_compute [OF finite_S 6] .
      thus "w \<in>\<^sub>L L" using M_decides TM_decider.decides_def a1 by blast
    qed
    ultimately show "TM_decider.decides_word (Abs_TM (tm_extra_symbols M S)) L w"
      by (rule TM_decider.decides_wordI)
  qed
qed

lemma tm_ext_accepts: "TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w) \<longleftrightarrow> TM_decider.accepts tm w"
proof
  assume "TM_decider.accepts tm w"
  hence "(\<exists>n. state (TM.run tm n w) \<in> {q\<in>TM.final_states tm. TM.label tm q = True})"
    by (simp add: TM_decider.acc_def TM_decider.accepts_altdef)
  hence "(\<exists>n. state (TM.run (Abs_TM (tm_to_ext_tm tm)) n (map (\<lambda>x. [x]) w)) \<in>
          {q\<in>TM.final_states (Abs_TM (tm_to_ext_tm tm)). TM.label (Abs_TM (tm_to_ext_tm tm)) q = True})"
    by (metis (mono_tags, lifting) ext_final_states ext_label ext_tm_valid mem_Collect_eq tm_ext_state_run
        valid_tm_final_states valid_tm_label)
  thus "TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w)"
    by (metis (no_types, lifting) TM_decider.accI TM_decider.accepts_altdef mem_Collect_eq)
next
  assume "TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w)"
  hence "(\<exists>n. state (TM.run (Abs_TM (tm_to_ext_tm tm)) n (map (\<lambda>x. [x]) w)) \<in>
          {q\<in>TM.final_states (Abs_TM (tm_to_ext_tm tm)). TM.label (Abs_TM (tm_to_ext_tm tm)) q = True})"
    by (metis (no_types, lifting) TM_decider.acc_final TM_decider.acc_not_rej TM_decider.accepts_altdef
        TM_decider.rejI TM_decider.rejects_altdef mem_Collect_eq)
  hence "(\<exists>n. state (TM.run tm n w) \<in> {q\<in>TM.final_states tm. TM.label tm q = True})"
    by (metis TM_decider.acc_def ext_final_states ext_label ext_tm_valid tm_ext_state_run
        valid_tm_final_states valid_tm_label)
  thus "TM_decider.accepts tm w"
    by (simp add: TM_decider.acc_def TM_decider.accepts_altdef)
qed

lemma tm_ext_rejects: "TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w) \<longleftrightarrow> TM_decider.rejects tm w"
  by (metis TM_decider.rejects_accepts tm_ext_accepts tm_ext_halts)

lemma tm_ext_decides_word: "TM_decider.decides_word (Abs_TM (tm_to_ext_tm tm)) (ext_lang L) (map (\<lambda>x. [x]) w) \<longleftrightarrow>
                            TM_decider.decides_word tm L w"
  by (metis TM_decider.decides_altdef ext_lang_eq tm_ext_accepts tm_ext_halts)

lemma tm_ext_decides: "TM_decider.decides (Abs_TM (tm_to_ext_tm tm)) (ext_lang L) \<longleftrightarrow>
                       TM_decider.decides tm L"
  apply (unfold TM_decider.decides_def)
proof
  assume a1: "alphabet (ext_lang L) \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<and>
    (\<forall>w\<in>(alphabet (ext_lang L))*.
        (w \<in>\<^sub>L ext_lang L) = TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) w \<and>
        (w \<notin> words (ext_lang L)) = TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w)"
  hence "alphabet L \<subseteq> TM.TM.symbols tm"
  proof
    assume "alphabet (ext_lang L) \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))"
    and "\<forall>w\<in>(alphabet (ext_lang L))*.
       (w \<in>\<^sub>L ext_lang L) = TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) w \<and>
       (w \<notin> words (ext_lang L)) = TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w"
    have "\<And>s. [s] \<in> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<longleftrightarrow> s \<in> TM.TM.symbols tm"
      by (metis ext_symbols ext_tm_valid valid_tm_symbols)
    moreover have "\<And>s. [s] \<in> alphabet (ext_lang L) \<longleftrightarrow> s \<in> alphabet L" by (induction L) simp
    ultimately show "alphabet L \<subseteq> TM.TM.symbols tm"
      using \<open>alphabet (ext_lang L) \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))\<close> by blast
  qed
  moreover have "(\<forall>w\<in>(alphabet L)*. (w \<in>\<^sub>L L) = TM_decider.accepts tm w \<and> (w \<notin> words L) = TM_decider.rejects tm w)"
  proof auto
    fix w
    assume "set w \<subseteq> alphabet L" and "w \<in>\<^sub>L L"
    hence "((map (\<lambda>x. [x]) w) \<in>\<^sub>L ext_lang L) = TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w)"
      using a1 ext_lang_eq by blast
    moreover have "(map (\<lambda>x. [x]) w) \<in>\<^sub>L ext_lang L"
      by (simp add: \<open>w \<in>\<^sub>L L\<close> ext_lang_eq)
    ultimately show "TM_decider.accepts tm w"
      using tm_ext_accepts by auto
  next
    fix w
    assume "set w \<subseteq> alphabet L" and "TM_decider.accepts tm w"
    hence "map (\<lambda>x. [x]) w \<in> (alphabet (ext_lang L))*" by (induction L) auto
    hence "(map (\<lambda>x. [x]) w) \<in>\<^sub>L ext_lang L"
      using \<open>TM_decider.accepts tm w\<close> a1 tm_ext_accepts by blast
    thus "w \<in>\<^sub>L L"
      by (simp add: ext_lang_eq)
  next
    fix w
    assume "set w \<subseteq> alphabet L" and "w \<notin> words L"
    hence "set (map (\<lambda>x. [x]) w) \<subseteq> alphabet (ext_lang L)" by (induction L) auto
    hence "((map (\<lambda>x. [x]) w) \<notin>\<^sub>L ext_lang L) = TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w)"
      using a1 by blast
    moreover have "(map (\<lambda>x. [x]) w) \<notin>\<^sub>L ext_lang L"
      by (simp add: \<open>w \<notin>\<^sub>L L\<close> ext_lang_eq)
    ultimately show "TM_decider.rejects tm w"
      using tm_ext_rejects by blast
  next
    fix w
    assume "set w \<subseteq> alphabet L" and "TM_decider.rejects tm w" and "w \<in>\<^sub>L L"
    hence "set (map (\<lambda>x. [x]) w) \<subseteq> alphabet (ext_lang L)" by (induction L) auto
    hence "((map (\<lambda>x. [x]) w) \<notin>\<^sub>L ext_lang L) = TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) (map (\<lambda>x. [x]) w)"
      using a1 by blast
    thus "False"
      using \<open>TM_decider.rejects tm w\<close> \<open>w \<in>\<^sub>L L\<close> ext_lang_eq tm_ext_rejects by auto
  qed
  ultimately show "alphabet L \<subseteq> TM.TM.symbols tm \<and>
    (\<forall>w\<in>(alphabet L)*. (w \<in>\<^sub>L L) = TM_decider.accepts tm w \<and> (w \<notin> words L) = TM_decider.rejects tm w)" by auto
next
  assume a2: "alphabet L \<subseteq> TM.TM.symbols tm \<and>
    (\<forall>w\<in>(alphabet L)*. (w \<in>\<^sub>L L) = TM_decider.accepts tm w \<and> (w \<notin> words L) = TM_decider.rejects tm w)"
  hence "alphabet (ext_lang L) \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))"
  proof
    assume "alphabet L \<subseteq> TM.TM.symbols tm"
    and "\<forall>w\<in>(alphabet L)*. (w \<in>\<^sub>L L) = TM_decider.accepts tm w \<and> (w \<notin> words L) = TM_decider.rejects tm w"
    have "bij_betw (\<lambda>x. [x]) (TM.TM.symbols tm) (TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)))"
    proof -
      have "\<And>s. s\<in>TM.TM.symbols tm \<Longrightarrow> hd [s] = s" by simp
      moreover have "\<And>s. s\<in>TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<Longrightarrow> [hd s] = s"
        by (metis append_self_conv2 card_set_1_iff_replicate ext_symbol_length ext_tm_valid length_1_hd_iff
            list.distinct(1) rotate1.simps(2) rotate1_fixpoint_card trim_left trim_nil trim_nil_eq valid_tm_symbols)
      ultimately show "bij_betw (\<lambda>x. [x]) (TM.TM.symbols tm) (TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)))"
        by (smt (verit, del_insts) bij_betwI' ext_symbols ext_tm_valid valid_tm_symbols)
    qed
    moreover have "bij_betw (\<lambda>x. [x]) (alphabet L) (alphabet (ext_lang L))"
    proof -
      have "inj_on (\<lambda>x. [x]) (alphabet L)"
        by (meson inj_onI list.inject)
      moreover have "image (\<lambda>x. [x]) (alphabet L) = (alphabet (ext_lang L))"
        by (induction L; auto; metis image_iff length_1_hd_iff)
      ultimately show "bij_betw (\<lambda>x. [x]) (alphabet L) (alphabet (ext_lang L))" by (rule bij_betw_imageI)
    qed
    ultimately show "alphabet (ext_lang L) \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))"
      by (metis \<open>alphabet L \<subseteq> TM.TM.symbols tm\<close> bij_betw_imp_surj_on image_mono)
  qed
  moreover have "\<forall>w\<in>(alphabet (ext_lang L))*.
        (w \<in>\<^sub>L ext_lang L) = TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) w \<and>
        (w \<notin> words (ext_lang L)) = TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w"
  proof rule+
    fix w
    assume "w \<in> (alphabet (ext_lang L))*" and "w \<in>\<^sub>L ext_lang L"
    let ?wne = "map (\<lambda>x. hd x) w"
    have "set w \<subseteq> alphabet (ext_lang L)"
      using \<open>w \<in> (alphabet (ext_lang L))*\<close> by auto
    hence "\<And>s. s\<in>set w \<Longrightarrow> length s = 1"
      using ext_lang_length by blast
    moreover have "\<And>l. length l = 1 \<Longrightarrow> [hd l] = l"
      by (metis cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv
          length_tl less_one list.exhaust_sel not_gr0)
    ultimately have "\<And>s. s \<in> set w \<Longrightarrow> [hd s] = s" by auto
    hence "map (\<lambda>x. [x]) ?wne = w" by (induction w) simp_all
    hence "(?wne \<in>\<^sub>L L) = TM_decider.accepts tm ?wne"
      by (metis \<open>w \<in>\<^sub>L ext_lang L\<close> a2 ext_lang_eq member_langD(1))
    moreover have "(map (\<lambda>x. [x]) ?wne) \<in>\<^sub>L ext_lang L"
      using \<open>map (\<lambda>x. [x]) (map hd w) = w\<close> \<open>w \<in>\<^sub>L ext_lang L\<close> by auto
    ultimately show "TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) w"
      by (metis \<open>map (\<lambda>x. [x]) (map hd w) = w\<close> ext_lang_eq tm_ext_accepts)
  next
    fix w
    assume "w \<in> (alphabet (ext_lang L))*" and "TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) w"
    let ?wne = "map (\<lambda>x. hd x) w"
    have "set w \<subseteq> alphabet (ext_lang L)"
      using \<open>w \<in> (alphabet (ext_lang L))*\<close> by auto
    hence "\<And>s. s\<in>set w \<Longrightarrow> length s = 1"
      using ext_lang_length by blast
    moreover have "\<And>l. length l = 1 \<Longrightarrow> [hd l] = l"
      by (metis cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv
          length_tl less_one list.exhaust_sel not_gr0)
    ultimately have "\<And>s. s \<in> set w \<Longrightarrow> [hd s] = s" by auto
    hence "map (\<lambda>x. [x]) ?wne = w" by (induction w) simp_all
    hence "?wne \<in> (alphabet L)*"
      by (smt (verit, ccfv_threshold) Ball_set_map
          \<open>\<And>s. s \<in> set w \<Longrightarrow> [hd s] = s\<close> \<open>set w \<subseteq> alphabet (ext_lang L)\<close>
          ext_lang.simps in_mono lang.exhaust_sel lang.sel(1) lists_member set_ext_eq)
    moreover have "?wne \<in>\<^sub>L L"
      by (metis \<open>TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) w\<close> \<open>map (\<lambda>x. [x]) (map hd w) = w\<close>
          a2 calculation tm_ext_accepts)
    ultimately show "w \<in>\<^sub>L ext_lang L"
      by (metis \<open>map (\<lambda>x. [x]) (map hd w) = w\<close> ext_lang_eq)
  next
    fix w
    assume "w \<in> (alphabet (ext_lang L))*"
    hence "w \<notin> words (ext_lang L) \<Longrightarrow> TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w"
    proof
      assume "w \<notin> words (ext_lang L)" and "set w \<subseteq> alphabet (ext_lang L)"
      let ?wne = "map (\<lambda>x. hd x) w"
      have "\<And>s. s\<in>set w \<Longrightarrow> length s = 1"
        using \<open>set w \<subseteq> alphabet (ext_lang L)\<close> ext_lang_length by blast
      moreover have "\<And>l. length l = 1 \<Longrightarrow> [hd l] = l"
        by (metis cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv
          length_tl less_one list.exhaust_sel not_gr0)
      ultimately have "\<And>s. s \<in> set w \<Longrightarrow> [hd s] = s" by auto
      hence "map (\<lambda>x. [x]) ?wne = w" by (induction w) simp_all
      hence "?wne \<notin> words L"
        by (metis \<open>w \<notin> words (ext_lang L)\<close> ext_lang_eq)
      moreover have "set ?wne \<subseteq> alphabet L" using \<open>set w \<subseteq> alphabet (ext_lang L)\<close>
        by (smt (verit, ccfv_SIG) Ball_set_map \<open>map (\<lambda>x. [x]) (map hd w) = w\<close> ext_lang.simps
            lang.collapse lang.sel(1) set_ext_eq subsetI)
      ultimately have "TM_decider.rejects tm ?wne" using a2 by blast
      thus "TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w"
        by (metis \<open>map (\<lambda>x. [x]) (map hd w) = w\<close> tm_ext_rejects)
    qed
    moreover have "TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w \<Longrightarrow> w \<notin> words (ext_lang L)"
    proof
      assume "TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w" and "w \<in>\<^sub>L ext_lang L"
      let ?wne = "map (\<lambda>x. hd x) w"
      have "set w \<subseteq> alphabet (ext_lang L)" using \<open>w \<in>\<^sub>L ext_lang L\<close> by auto
      have "\<And>s. s\<in>set w \<Longrightarrow> length s = 1"
        using \<open>set w \<subseteq> alphabet (ext_lang L)\<close> ext_lang_length by blast
      moreover have "\<And>l. length l = 1 \<Longrightarrow> [hd l] = l"
        by (metis cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv
          length_tl less_one list.exhaust_sel not_gr0)
      ultimately have "\<And>s. s \<in> set w \<Longrightarrow> [hd s] = s" by auto
      hence "map (\<lambda>x. [x]) ?wne = w" by (induction w) simp_all
      hence "TM_decider.rejects tm ?wne"
        by (metis \<open>TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w\<close> tm_ext_rejects)
      hence "?wne \<notin>\<^sub>L L"
        using a2 by blast
      hence "w \<notin>\<^sub>L ext_lang L"
        by (metis \<open>map (\<lambda>x. [x]) (map hd w) = w\<close> ext_lang_eq)
      thus "False" using \<open>w \<in>\<^sub>L ext_lang L\<close> by simp
    qed
    ultimately show "(w \<notin> words (ext_lang L)) = TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w" by auto
  qed
  ultimately show "alphabet (ext_lang L) \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<and>
    (\<forall>w\<in>(alphabet (ext_lang L))*.
        (w \<in>\<^sub>L ext_lang L) = TM_decider.accepts (Abs_TM (tm_to_ext_tm tm)) w \<and>
        (w \<notin> words (ext_lang L)) = TM_decider.rejects (Abs_TM (tm_to_ext_tm tm)) w)" by auto
qed

definition compl_TM :: "('a, 'b) TM_decider \<Rightarrow> ('a, 'b, bool) TM_record" where
  "compl_TM tm \<equiv> TM (TM.tape_count tm) (TM.symbols tm) (TM.states tm)
    (TM.initial_state tm) (TM.final_states tm) (-TM.label tm) (TM.next_state tm)
    (TM.next_write tm) (TM.next_move tm)"

lemma compl_TM_valid: "valid_TM (compl_TM tm)" unfolding compl_TM_def by auto

lemma compl_TM_next_writes: "TM.next_writes (Abs_TM (compl_TM tm)) tmc =
                             TM.next_writes tm tmc"
proof (unfold TM.next_writes_def)
  have 1: "TM.TM.tape_count (Abs_TM (compl_TM tm)) = TM.TM.tape_count tm" unfolding
    compl_TM_def using compl_TM_valid by (simp add: valid_TM_I valid_tm_tape_count)
  have 2: "TM.TM.next_write (Abs_TM (compl_TM tm)) tmc = TM.TM.next_write tm tmc"
    unfolding compl_TM_def using compl_TM_valid
    by (metis compl_TM_def select_convs(8) valid_tm_next_write)
  show "(\<lambda>hds. map (TM.TM.next_write (Abs_TM (compl_TM tm)) tmc hds)
             [0..<TM.TM.tape_count (Abs_TM (compl_TM tm))]) =
    (\<lambda>hds. map (TM.TM.next_write tm tmc hds) [0..<TM.TM.tape_count tm])"
      unfolding 1 2 ..
  qed

lemma compl_TM_next_moves: "TM.next_moves (Abs_TM (compl_TM tm)) tmc =
                             TM.next_moves tm tmc"
proof (unfold TM.next_moves_def)
  have 1: "TM.TM.tape_count (Abs_TM (compl_TM tm)) = TM.TM.tape_count tm" unfolding
    compl_TM_def using compl_TM_valid by (simp add: valid_TM_I valid_tm_tape_count)
  have 2: "TM.next_move (Abs_TM (compl_TM tm)) tmc = TM.TM.next_move tm tmc"
    unfolding compl_TM_def using compl_TM_valid
    by (metis compl_TM_def select_convs(9) valid_tm_next_move)
  show "(\<lambda>hds. map (TM.TM.next_move (Abs_TM (compl_TM tm)) tmc hds)
             [0..<TM.TM.tape_count (Abs_TM (compl_TM tm))]) =
    (\<lambda>hds. map (TM.TM.next_move tm tmc hds) [0..<TM.TM.tape_count tm])"
    unfolding 1 2 ..
qed

lemma compl_TM_step: "TM.step (Abs_TM (compl_TM tm)) tmc = TM.step tm tmc"
proof -
  have 1: "state tmc \<in> TM.final_states tm \<longleftrightarrow>
        state tmc \<in> TM.final_states (Abs_TM (compl_TM tm))" using compl_TM_valid
    unfolding compl_TM_def by (metis select_convs(5) valid_tm_final_states)
  moreover have "state tmc \<in> TM.final_states tm \<Longrightarrow> TM.step tm tmc = tmc"
    unfolding TM.step_def by simp
  moreover have "state tmc \<in> TM.final_states (Abs_TM (compl_TM tm)) \<Longrightarrow>
    TM.step (Abs_TM (compl_TM tm)) tmc = tmc" unfolding compl_TM_def TM.step_def by simp
  ultimately have "state tmc \<in> TM.final_states tm \<Longrightarrow>
    TM.step tm tmc = TM.step (Abs_TM (compl_TM tm)) tmc" by auto
  moreover have "state tmc \<notin> TM.final_states tm \<Longrightarrow>
    TM.step (Abs_TM (compl_TM tm)) tmc = TM.step tm tmc"
  proof (unfold TM.step_def 1 [symmetric], auto, unfold TM.step_not_final_def)
    have 2: "TM.TM.next_state (Abs_TM (compl_TM tm)) = TM.TM.next_state tm"
      unfolding compl_TM_def using compl_TM_valid
      by (metis compl_TM_def select_convs(7) valid_tm_next_state)
    have 3: "TM.next_actions (Abs_TM (compl_TM tm)) = TM.next_actions tm"
      unfolding TM.next_actions_def compl_TM_next_writes compl_TM_next_moves ..
    show "(let q = state tmc; hds = heads tmc
     in TM_config (TM.TM.next_state (Abs_TM (compl_TM tm)) q hds)
         (map2 TM_abbrevs.tape_action (TM.next_actions (Abs_TM (compl_TM tm)) q hds)
           (tapes tmc))) =
    (let q = state tmc; hds = heads tmc
     in TM_config (TM.TM.next_state tm q hds)
         (map2 TM_abbrevs.tape_action (TM.next_actions tm q hds) (tapes tmc)))"
      unfolding 2 3 ..
  qed
  ultimately show ?thesis by metis
qed

lemma compl_TM_initial_config: "TM.initial_config (Abs_TM (compl_TM tm)) w =
                                TM.initial_config tm w"
proof (unfold TM.initial_config_def)
  have 1: "TM.TM.initial_state (Abs_TM (compl_TM tm)) =
           TM.TM.initial_state tm"
    by (metis compl_TM_def compl_TM_valid select_convs(4) valid_tm_initial_state)
  have 2: "TM.TM.tape_count (Abs_TM (compl_TM tm)) = TM.TM.tape_count tm"
    unfolding compl_TM_def using compl_TM_valid
    by (metis compl_TM_def select_convs(1) valid_tm_tape_count)
  show "TM_config (TM.TM.initial_state (Abs_TM (compl_TM tm)))
     (TM_abbrevs.input_tape w #
      Tape [] None [] \<up> (TM.TM.tape_count (Abs_TM (compl_TM tm)) - 1)) =
    TM_config (TM.TM.initial_state tm)
     (TM_abbrevs.input_tape w # Tape [] None [] \<up> (TM.TM.tape_count tm - 1))"
    unfolding 1 2 ..
qed

lemma compl_TM_run: "TM.run (Abs_TM (compl_TM tm)) k = TM.run tm k"
  unfolding TM.run_def unfolding compl_TM_step unfolding compl_TM_initial_config ..

lemma compl_TM_accepts: "TM_decider.accepts (Abs_TM (compl_TM tm)) w \<longleftrightarrow>
                        TM_decider.rejects tm w"
  unfolding TM_decider.accepts_def TM_decider.rejects_def TM.compute_def
    TM.compute_config_def TM_decider.acc_def TM_decider.rej_def compl_TM_step
proof -
  have 1: "\<And>n. TM.is_final (Abs_TM (compl_TM tm))
             ((TM.step tm ^^ n) (TM.initial_config (Abs_TM (compl_TM tm)) w)) \<longleftrightarrow>
            TM.is_final tm ((TM.step tm ^^ n) (TM.initial_config tm w))"
    by (metis compl_TM_def compl_TM_initial_config compl_TM_valid is_finalD
        is_finalI select_convs(5) valid_tm_final_states)
  have "TM.TM.final_states (Abs_TM (compl_TM tm)) = TM.TM.final_states tm"
    by (metis compl_TM_def compl_TM_valid select_convs(5) valid_tm_final_states)
  moreover have "\<And>q. TM.TM.label (Abs_TM (compl_TM tm)) q \<longleftrightarrow> \<not>TM.TM.label tm q"
  proof
    fix q
    assume "TM.TM.label (Abs_TM (compl_TM tm)) q"
    thus "\<not> TM.TM.label tm q" unfolding compl_TM_def
      by (metis (no_types, lifting) bot.extremum_uniqueI compl_TM_def
          compl_TM_valid compl_le_compl_iff le_boolI' select_convs(6)
          uminus_apply valid_tm_label)
  next
    fix q
    assume "\<not> TM.TM.label tm q"
    thus "TM.TM.label (Abs_TM (compl_TM tm)) q" unfolding compl_TM_def
      by (metis (no_types, lifting) bot.extremum_uniqueI compl_TM_def
          compl_TM_valid compl_le_compl_iff le_boolI' select_convs(6)
          uminus_apply valid_tm_label)
  qed
  ultimately have 2: "{q \<in> TM.TM.final_states (Abs_TM (compl_TM tm)).
         TM.TM.label (Abs_TM (compl_TM tm)) q = True} =
           {q \<in> TM.TM.final_states tm. TM.TM.label tm q = False}" by simp
  show "(state
      ((TM.step tm ^^
        (LEAST n.
            TM.is_final (Abs_TM (compl_TM tm))
             ((TM.step tm ^^ n) (TM.initial_config (Abs_TM (compl_TM tm)) w))))
        (TM.initial_config (Abs_TM (compl_TM tm)) w))
     \<in> {q \<in> TM.TM.final_states (Abs_TM (compl_TM tm)).
         TM.TM.label (Abs_TM (compl_TM tm)) q = True}) =
    (state
      ((TM.step tm ^^
        (LEAST n. TM.is_final tm ((TM.step tm ^^ n) (TM.initial_config tm w))))
        (TM.initial_config tm w))
     \<in> {q \<in> TM.TM.final_states tm. TM.TM.label tm q = False})" unfolding 1 2
      compl_TM_initial_config
    by (simp add: \<open>TM.TM.final_states (Abs_TM (compl_TM tm)) = TM.TM.final_states tm\<close>)
qed

lemma compl_TM_rejects: "TM_decider.rejects (Abs_TM (compl_TM tm)) w \<longleftrightarrow>
                        TM_decider.accepts tm w"
  by (metis TM.halts_altdef TM.is_final_def TM_decider.accepts_halts
      TM_decider.rejects_accepts compl_TM_accepts compl_TM_def compl_TM_run
      compl_TM_valid select_convs(5) valid_tm_final_states)

lemma compl_TM_halts: "TM.halts (Abs_TM (compl_TM tm)) w \<longleftrightarrow> TM.halts tm w"
  unfolding TM.halts_def TM.halts_config_def
  by (metis TM.halts_altdef TM.run_def TM_decider.accepts_halts
      TM_decider.rejects_accepts compl_TM_accepts compl_TM_rejects)

subsection\<open>TM Languages\<close>

definition TM_lang :: "('q, 's) TM_decider \<Rightarrow> 's lang" ("L'(_')")
  where "L(M) \<equiv> Lang (TM.symbols M) (TM_decider.accepts M)"

lemma TM_lang_simps[simp]:
  shows TM_lang_alphabet: "alphabet L(M) = TM.symbols M"
    and TM_lang_gen_pred: "gen_pred L(M) = TM_decider.accepts M"
    and TM_lang_words: "words L(M) = {w\<in>(TM.symbols M)*. TM_decider.accepts M w}"
  unfolding TM_lang_def words_def by auto

context TM_decider
begin

lemma decides_TM_lang: "(\<And>w. w \<in> \<Sigma>* \<Longrightarrow> halts w) \<Longrightarrow> decides L(M)"
  by (simp add: TM_lang_def rejects_accepts)

lemma TM_lang_uniq:
  assumes "alphabet L = \<Sigma>"
    and "decides L"
  shows "words L(M) = words L"
    and "alphabet L(M) = alphabet L"
proof -
  from \<open>alphabet L = \<Sigma>\<close> show "alphabet L(M) = alphabet L" by simp

  from \<open>decides L\<close> have dec: "\<forall>w\<in>\<Sigma>*. decides_word L w" unfolding \<open>alphabet L = \<Sigma>\<close> ..
  show "words L(M) = words L"
  proof (intro Set.equalityI subsetI)
    fix w assume \<open>w \<in>\<^sub>L L\<close>
    then have "w \<in> \<Sigma>*" by (simp add: \<open>alphabet L = \<Sigma>\<close> member_lang_iff)
    moreover with \<open>w \<in>\<^sub>L L\<close> and dec have "accepts w" by simp
    ultimately show "w \<in>\<^sub>L L(M)" unfolding TM_lang_def by simp
  next
    fix w assume \<open>w \<in>\<^sub>L L(M)\<close>
    then have "accepts w" and "w \<in> \<Sigma>*" by auto
    with dec show "w \<in>\<^sub>L L" by simp
  qed
qed

end

lemma set_tape_in_symbols: "set w \<subseteq> TM.symbols M \<Longrightarrow> i < TM.tape_count M \<Longrightarrow>
       set_tape (tapes (TM.steps M n (TM.initial_config M w)) ! i) \<subseteq> TM.symbols M"
proof (induction n)
  case 0
  then show ?case apply simp
    unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
    apply (metis "0.prems"(1) One_nat_def TM.init_conf_len TM.initial_config_def
        TM_abbrevs.input_tape_def TM_abbrevs.input_tape_set TM_config.sel(2)
        length_replicate nth_replicate replicate_Suc subsetD)
    by (metis One_nat_def Suc_le_eq TM_abbrevs.input_tape.simps(1,2)
        TM_abbrevs.input_tape_set bot_nat_0.not_eq_extremum diff_less_mono in_set_replicate
        list.exhaust_sel nth_Cons' nth_replicate replicate_0 subset_eq)
next
  case (Suc n)
  hence [simp]: "[0..<TM.TM.tape_count M] ! i = i" by simp
  note 1 = Suc(1) [OF Suc(2, 3)]
  have 2: "set (right (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i)) \<subseteq>
           options (set_tape (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i))"
    apply (auto simp add: options_def)
    apply (cases "tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i")
    apply auto
    by (metis image_iff not_Some_eq option.set_intros tape.set tape.set_intros(3))
  have 3: "set (left (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i)) \<subseteq>
           options (set_tape (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i))"
    apply (auto simp add: options_def)
    apply (cases "tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i")
    apply auto
    by (metis UN_I Un_iff image_iff not_Some_eq option.set_intros)
  have 4: "head (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i) \<in>
           options (set_tape (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i))"
    apply (auto simp add: options_def)
    apply (cases "tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i")
    apply auto
    by (metis insert_iff le_sup_iff options_def set_options_eq sup_ge1)
  show ?case apply simp
    apply (subst TM.step_def)
    apply auto
    using Suc.IH Suc.prems(1,2) apply blast
    apply (subst (asm) nth_map2)
      apply (simp_all add: Suc.prems(2) TM.next_actions_simps(2))
     apply (simp add: Suc.prems(2) TM.run_tapes_len)
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
      TM.next_moves_def apply (subst (asm) (1 2) nth_zip)
      apply auto
    using Suc.prems(2) apply force+
    apply (subst (asm) (1 2) nth_map)
     apply auto
    using Suc.prems(2) apply blast
    apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) (TM.initial_config M w)))
                  (heads ((TM.step M ^^ n) (TM.initial_config M w))) i")
      apply auto
    unfolding TM_abbrevs.tape_write_def
      apply (cases "left (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i)")
       apply (auto simp add: TM_abbrevs.tape_shift.simps)
    using Some_options_iff[of _ "TM.TM.symbols M"] Suc.prems(1,2)
      TM.next_write_valid[of "state ((TM.step M ^^ n) (TM.initial_config M w))" M
        "heads ((TM.step M ^^ n) (TM.initial_config M w))" i]
      TM.wf_config_iff[of M "(TM.step M ^^ n) (TM.initial_config M w)"]
      TM.wf_initial_config[of w M] TM.wf_steps[of M "TM.initial_config M w" n]
      lists_member[of w "TM.TM.symbols M"] apply presburger
    using 1 2 apply blast
    using 1 2 3 apply auto
    using Some_options_iff[of _ "TM.TM.symbols M"] Suc.prems(1,2)
      TM.next_write_valid[of "state ((TM.step M ^^ n) (TM.initial_config M w))" M
        "heads ((TM.step M ^^ n) (TM.initial_config M w))" i]
      TM.wf_config_iff[of M "(TM.step M ^^ n) (TM.initial_config M w)"]
      TM.wf_initial_config[of w M] TM.wf_steps[of M "TM.initial_config M w" n]
      lists_member[of w "TM.TM.symbols M"] apply presburger
     apply (cases "right (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i)")
      apply (auto simp add: TM_abbrevs.tape_shift.simps)
    using Some_options_iff[of _ "TM.TM.symbols M"] Suc.prems(1,2)
      TM.next_write_valid[of "state ((TM.step M ^^ n) (TM.initial_config M w))" M
        "heads ((TM.step M ^^ n) (TM.initial_config M w))" i]
      TM.wf_config_iff[of M "(TM.step M ^^ n) (TM.initial_config M w)"]
      TM.wf_initial_config[of w M] TM.wf_steps[of M "TM.initial_config M w" n]
      lists_member[of w "TM.TM.symbols M"] by presburger+
qed

function cell_index :: "('q, 's, 'l) TM \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "cell_index M w i 0 = 0" |
  "TM.next_move M (state (TM.steps M k (TM.initial_config M w)))
   (heads (TM.steps M k (TM.initial_config M w))) i = Shift_Left \<Longrightarrow>
   cell_index M w i (Suc k) = cell_index M w i k - 1" |
  "TM.next_move M (state (TM.steps M k (TM.initial_config M w)))
   (heads (TM.steps M k (TM.initial_config M w))) i = Shift_Right \<Longrightarrow>
   cell_index M w i (Suc k) = cell_index M w i k + 1" |
  "TM.next_move M (state (TM.steps M k (TM.initial_config M w)))
   (heads (TM.steps M k (TM.initial_config M w))) i = No_Shift \<Longrightarrow>
   cell_index M w i (Suc k) = cell_index M w i k"
  by auto (meson head_move.exhaust list_decode.cases)
termination by lexicographic_order

lemma cell_index_abs_bound: "abs (cell_index M w i k) \<le> k"
proof (induction k rule: cell_index.induct)
  case (1 M w i)
  then show ?case by simp
next
  case (2 M k w i)
  then show ?case by simp
next
  case (3 M k w i)
  then show ?case by simp
next
  case (4 M k w i)
  then show ?case by simp
qed

lemma cell_index_eq_steps_all_lower_eq: "cell_index M w i k = k \<Longrightarrow> n \<le> k \<Longrightarrow> cell_index M w i n = n"
proof (induction k arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (rule ccontr, cases "cell_index M w i n < int n")
    case True
    have 1: "cell_index M w i (Suc n) \<le> int n"
      apply (cases rule: cell_index.cases [where x="(M, w, i, Suc n)"])
      using True by simp_all
    show False apply (cases "n = Suc k")
      using Suc(1) [of n] Suc(2,3) 1
       apply (metis Suc.prems(2) Suc.prems(1) True less_Suc_eq_le of_nat_less_iff not_less_eq_eq)
      using Suc(1) [of n] Suc(2,3) 1 apply auto
      by (smt (verit, del_insts) True cell_index.simps(2,3,4) cell_index_abs_bound head_move.exhaust)
  next
    case False
    moreover assume "cell_index M w i n \<noteq> int n"
    ultimately show False using cell_index_abs_bound [of M w i n] by simp
  qed
qed

lemma cell_index_eq_minus_steps_all_lower_eq: "cell_index M w i k = -k \<Longrightarrow> n \<le> k \<Longrightarrow> cell_index M w i n = -n"
proof (induction k arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (rule ccontr, cases "cell_index M w i n > -int n")
    case True
    have 1: "cell_index M w i (Suc n) \<ge> -int n"
      apply (cases rule: cell_index.cases [where x="(M, w, i, Suc n)"])
      using True by simp_all
    show False apply (cases "n = Suc k")
      using Suc(1) [of n] Suc(3) apply (metis Suc.prems(1) True dual_order.refl linorder_not_less)
      using Suc(1) [of n] Suc(2,3) 1 apply auto
      by (smt (verit, del_insts) True cell_index.simps(2,3,4) cell_index_abs_bound head_move.exhaust)
  next
    case False
    moreover assume "cell_index M w i n \<noteq> -int n"
    ultimately show False using cell_index_abs_bound [of M w i n] by simp
  qed
qed

definition max_cell_index :: "('q, 's, 'l) TM \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "max_cell_index M w i k \<equiv> Max {ci. \<exists>n\<le>k. cell_index M w i n = ci}"

definition min_cell_index :: "('q, 's, 'l) TM \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "min_cell_index M w i k \<equiv> Min {ci. \<exists>n\<le>k. cell_index M w i n = ci}"

lemma max_cell_index_ge_cell_index: "cell_index M w i k \<le> max_cell_index M w i k"
  unfolding max_cell_index_def
proof -
  have "cell_index M w i k \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}"
    by blast
  thus "cell_index M w i k \<le> Max {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by simp
qed

lemma min_cell_index_le_cell_index: "cell_index M w i k \<ge> min_cell_index M w i k"
  unfolding min_cell_index_def
proof -
  have "cell_index M w i k \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}"
    by blast
  thus "cell_index M w i k \<ge> Min {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by simp
qed

lemma max_cell_index_ge_0: "max_cell_index M w i k \<ge> 0"
  unfolding max_cell_index_def
proof -
  have "0 \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by fastforce
  thus "0 \<le> Max {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by simp
qed

lemma min_cell_index_le_0: "min_cell_index M w i k \<le> 0"
  unfolding min_cell_index_def
proof -
  have "0 \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by fastforce
  thus "0 \<ge> Min {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by simp
qed

lemma max_cell_index_max: "n \<le> k \<Longrightarrow> max_cell_index M w i k \<ge> cell_index M w i n"
  unfolding max_cell_index_def
proof -
  assume a1: "n \<le> k"
  have 1: "cell_index M w i n \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}" using a1 by blast
  show "cell_index M w i n \<le> Max {ci. \<exists>n\<le>k. cell_index M w i n = ci}" using 1 by simp
qed

lemma min_cell_index_min: "n \<le> k \<Longrightarrow> min_cell_index M w i k \<le> cell_index M w i n"
  unfolding min_cell_index_def
proof -
  assume a1: "n \<le> k"
  have 1: "cell_index M w i n \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}" using a1 by blast
  show "cell_index M w i n \<ge> Min {ci. \<exists>n\<le>k. cell_index M w i n = ci}" using 1 by simp
qed

lemma max_cell_index_obtain: obtains n :: nat where "n \<le> k" and "max_cell_index M w i k = cell_index M w i n"
proof -
  assume a1: "\<And>n. n \<le> k \<Longrightarrow> max_cell_index M w i k = cell_index M w i n \<Longrightarrow> thesis"
  have "0 \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by fastforce
  moreover have "finite {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by simp
  ultimately have "max_cell_index M w i k \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}"
    unfolding max_cell_index_def using Max_in by blast
  then obtain n :: nat where n_le: "n \<le> k" and n_ci: "cell_index M w i n = max_cell_index M w i k" by auto
  show thesis apply (rule a1)
     apply (fact n_le)
    by (fact n_ci [symmetric])
qed

lemma min_cell_index_obtain: obtains n :: nat where "n \<le> k" and "min_cell_index M w i k = cell_index M w i n"
proof -
  assume a1: "\<And>n. n \<le> k \<Longrightarrow> min_cell_index M w i k = cell_index M w i n \<Longrightarrow> thesis"
  have "0 \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by fastforce
  moreover have "finite {ci. \<exists>n\<le>k. cell_index M w i n = ci}" by simp
  ultimately have "min_cell_index M w i k \<in> {ci. \<exists>n\<le>k. cell_index M w i n = ci}"
    unfolding min_cell_index_def using Min_in by blast
  then obtain n :: nat where n_le: "n \<le> k" and n_ci: "cell_index M w i n = min_cell_index M w i k" by auto
  show thesis apply (rule a1)
     apply (fact n_le)
    by (fact n_ci [symmetric])
qed

lemma max_cell_index_bound: "max_cell_index M w i k \<le> k"
  apply (rule max_cell_index_obtain [of k M w i])
  apply simp
proof -
  fix n :: nat
  assume a1: "n \<le> k"
  show "cell_index M w i n \<le> int k" using cell_index_abs_bound [of M w i n] a1 by linarith
qed

lemma min_cell_index_bound: "min_cell_index M w i k \<ge> -k"
  apply (rule min_cell_index_obtain [of k M w i])
  apply simp
proof -
  fix n :: nat
  assume a1: "n \<le> k"
  show "- int k \<le> cell_index M w i n" using cell_index_abs_bound [of M w i n] a1 by linarith
qed

lemma cell_index_eq_k_is_max: "cell_index M w i k = k \<longleftrightarrow> max_cell_index M w i k = k"
  apply auto
   apply (metis max_cell_index_bound max_cell_index_ge_cell_index verit_la_disequality)
proof (rule max_cell_index_obtain [of k M w i])
  fix n :: nat
  assume a1: "max_cell_index M w i k = int k" and a2: "n \<le> k" and
         a3: "max_cell_index M w i k = cell_index M w i n"
  have "cell_index M w i n = int k" unfolding a1 [symmetric] a3 [symmetric] ..
  hence "k \<le> n" using cell_index_abs_bound [of M w i n] by simp
  hence 1: "k = n" using a2 by simp
  show "cell_index M w i k = int k" unfolding a1 [symmetric] a3 unfolding 1 ..
qed

lemma cell_index_eq_mk_is_min: "cell_index M w i k = -k \<longleftrightarrow> min_cell_index M w i k = -k"
  apply auto
  apply (metis min_cell_index_bound min_cell_index_le_cell_index verit_la_disequality)
proof (rule min_cell_index_obtain [of k M w i])
  fix n :: nat
  assume a1: "min_cell_index M w i k = - int k" and a2: "n \<le> k" and
         a3: "min_cell_index M w i k = cell_index M w i n"
  have "cell_index M w i n = - int k" unfolding a1 [symmetric] a3 [symmetric] ..
  hence "k \<le> n" using cell_index_abs_bound [of M w i n] by simp
  hence 1: "k = n" using a2 by simp
  show "cell_index M w i k = - int k" unfolding a1 [symmetric] a3 unfolding 1 ..
qed

lemma max_cell_index_mono: "n \<le> k \<Longrightarrow> max_cell_index M w i n \<le> max_cell_index M w i k"
  apply (rule max_cell_index_obtain [of k M w i])
  apply (rule max_cell_index_obtain [of n M w i])
proof -
  fix l m :: nat
  assume a1: "n \<le> k" and a2: "l \<le> k" and a3: "m \<le> n" and a4: "max_cell_index M w i k = cell_index M w i l" and
         a5: "max_cell_index M w i n = cell_index M w i m"
  show "max_cell_index M w i n \<le> max_cell_index M w i k"
    by (metis a1 a3 a5 max_cell_index_max order_trans)
qed

lemma min_cell_index_revmono: "n \<le> k \<Longrightarrow> min_cell_index M w i n \<ge> min_cell_index M w i k"
  apply (rule min_cell_index_obtain [of k M w i])
  apply (rule min_cell_index_obtain [of n M w i])
proof -
  fix l m :: nat
  assume a1: "n \<le> k" and a2: "l \<le> k" and a3: "m \<le> n" and a4: "min_cell_index M w i k = cell_index M w i l" and
         a5: "min_cell_index M w i n = cell_index M w i m"
  show "min_cell_index M w i n \<ge> min_cell_index M w i k"
    by (metis a1 a3 a5 min_cell_index_min order_trans)
qed

lemma max_ci_eq_ci: "n \<le> k \<Longrightarrow> max_cell_index M w i k = cell_index M w i n \<Longrightarrow>
                     max_cell_index M w i n = cell_index M w i n"
  by (smt (verit, best) max_cell_index_ge_cell_index max_cell_index_mono)

lemma min_ci_eq_ci: "n \<le> k \<Longrightarrow> min_cell_index M w i k = cell_index M w i n \<Longrightarrow>
                     min_cell_index M w i n = cell_index M w i n"
  by (smt (verit, best) min_cell_index_le_cell_index min_cell_index_revmono)

lemma max_cell_index_0 [simp]: "max_cell_index M w i 0 = 0"
  unfolding max_cell_index_def by simp

lemma min_cell_index_0 [simp]: "min_cell_index M w i 0 = 0"
  unfolding min_cell_index_def by simp

lemma max_cell_index_add_ge: "max_cell_index M w i k + n \<ge> max_cell_index M w i (k + n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (rule max_cell_index_obtain [of "k + Suc n" M w i])
    fix m :: nat
    assume a1: "m \<le> k + Suc n" and a2: "max_cell_index M w i (k + Suc n) = cell_index M w i m"
    have 1: "m \<le> k + n \<Longrightarrow> max_cell_index M w i (k + n) = cell_index M w i m"
      apply (frule max_cell_index_max [where M=M and w=w and i=i])
      apply (frule max_cell_index_mono [where M=M and w=w and i=i])
      unfolding a2 [symmetric] by (metis add_Suc_right max_cell_index_mono suc_is_ge verit_la_disequality)
    have 2: "\<not> m \<le> k + n \<Longrightarrow> m = k + Suc n" using a1 by auto
    have 3: "m = k + Suc n \<Longrightarrow> max_cell_index M w i (k + Suc n) \<le> cell_index M w i (k + n) + 1"
      unfolding a2 apply simp
      by (smt (verit, best) cell_index.simps(2,3,4) head_move.exhaust)
    show "max_cell_index M w i (k + Suc n) \<le> max_cell_index M w i k + int (Suc n)"
      apply (cases "m \<le> k + n")
       apply (subst a2)
       apply (subst 1 [symmetric])
        apply assumption
      using Suc apply simp
      apply (drule 2)
      apply (frule 3)
      by (smt (verit, best) Suc max_cell_index_ge_cell_index of_nat_Suc)
  qed
qed

lemma min_cell_index_sub_le: "min_cell_index M w i k - n \<le> min_cell_index M w i (k + n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (rule min_cell_index_obtain [of "k + Suc n" M w i])
    fix m :: nat
    assume a1: "m \<le> k + Suc n" and a2: "min_cell_index M w i (k + Suc n) = cell_index M w i m"
    have 1: "m \<le> k + n \<Longrightarrow> min_cell_index M w i (k + n) = cell_index M w i m"
      apply (frule min_cell_index_min [where M=M and w=w and i=i])
      apply (frule min_cell_index_revmono [where M=M and w=w and i=i])
      unfolding a2 [symmetric] by (metis add_Suc_right min_cell_index_revmono suc_is_ge verit_la_disequality)
    have 2: "\<not> m \<le> k + n \<Longrightarrow> m = k + Suc n" using a1 by auto
    have 3: "m = k + Suc n \<Longrightarrow> min_cell_index M w i (k + Suc n) \<ge> cell_index M w i (k + n) - 1"
      unfolding a2 apply simp
      by (smt (verit, best) cell_index.simps(2,3,4) head_move.exhaust)
    show "min_cell_index M w i (k + Suc n) \<ge> min_cell_index M w i k - int (Suc n)"
      apply (cases "m \<le> k + n")
       apply (subst a2)
       apply (subst 1 [symmetric])
        apply assumption
      using Suc apply simp
      apply (drule 2)
      apply (frule 3)
      by (smt (verit, best) Suc min_cell_index_le_cell_index of_nat_Suc)
  qed
qed

lemma max_cell_index_Suc1: "cell_index M w i (Suc k) \<le> max_cell_index M w i k \<Longrightarrow>
                            max_cell_index M w i (Suc k) = max_cell_index M w i k"
proof (rule max_cell_index_obtain)
  fix n :: nat
  assume a1: "cell_index M w i (Suc k) \<le> max_cell_index M w i k" and
         a2: "n \<le> Suc k" and
         a3: "max_cell_index M w i (Suc k) = cell_index M w i n"
  have "n = Suc k \<Longrightarrow> max_cell_index M w i (Suc k) = max_cell_index M w i k"
    unfolding a3 apply simp
    by (metis a3 a1 max_cell_index_mono verit_la_disequality order_trans suc_is_ge)
  moreover have "n < Suc k \<Longrightarrow> max_cell_index M w i (Suc k) = max_cell_index M w i k"
    using a3 [symmetric] max_cell_index_max [of n k M w i] apply simp
    by (metis max_cell_index_mono verit_la_disequality suc_is_ge)
  ultimately show "max_cell_index M w i (Suc k) = max_cell_index M w i k" using a2 by fastforce
qed

lemma max_cell_index_Suc2: "cell_index M w i (Suc k) > max_cell_index M w i k \<Longrightarrow>
                            max_cell_index M w i (Suc k) = max_cell_index M w i k + 1"
proof (rule max_cell_index_obtain)
  fix n :: nat
  assume a1: "cell_index M w i (Suc k) > max_cell_index M w i k" and
         a2: "n \<le> Suc k" and
         a3: "max_cell_index M w i (Suc k) = cell_index M w i n"
  have "n < Suc k \<Longrightarrow> False"
    using max_cell_index_max [of n k M w i, folded a3] apply simp
    by (smt (verit, best) a1 max_cell_index_ge_cell_index)
  hence 1: "n = Suc k" using a2 by fastforce
  show "max_cell_index M w i (Suc k) = max_cell_index M w i k + 1"
    using a1 [folded 1]
    by (smt (verit, best) 1 a3 cell_index.simps(2,3,4) head_move.exhaust max_cell_index_ge_cell_index)
qed

lemma max_cell_index_Suc: "max_cell_index M w i (Suc k) =
                           (if cell_index M w i (Suc k) \<le> max_cell_index M w i k then
                           max_cell_index M w i k else max_cell_index M w i k + 1)"
  apply auto
   apply (erule max_cell_index_Suc1)
  apply (rule max_cell_index_Suc2)
  by simp

lemma min_cell_index_Suc1: "cell_index M w i (Suc k) \<ge> min_cell_index M w i k \<Longrightarrow>
                            min_cell_index M w i (Suc k) = min_cell_index M w i k"
proof (rule min_cell_index_obtain)
  fix n :: nat
  assume a1: "cell_index M w i (Suc k) \<ge> min_cell_index M w i k" and
         a2: "n \<le> Suc k" and
         a3: "min_cell_index M w i (Suc k) = cell_index M w i n"
  have "n = Suc k \<Longrightarrow> min_cell_index M w i (Suc k) = min_cell_index M w i k"
    unfolding a3 apply simp
    by (metis a3 a1 min_cell_index_revmono verit_la_disequality suc_is_ge)
  moreover have "n < Suc k \<Longrightarrow> min_cell_index M w i (Suc k) = min_cell_index M w i k"
    using a3 [symmetric] min_cell_index_min [of n k M w i] apply simp
    by (metis min_cell_index_revmono verit_la_disequality suc_is_ge)
  ultimately show "min_cell_index M w i (Suc k) = min_cell_index M w i k" using a2 by fastforce
qed

lemma min_cell_index_Suc2: "cell_index M w i (Suc k) < min_cell_index M w i k \<Longrightarrow>
                            min_cell_index M w i (Suc k) = min_cell_index M w i k - 1"
proof (rule min_cell_index_obtain)
  fix n :: nat
  assume a1: "cell_index M w i (Suc k) < min_cell_index M w i k" and
         a2: "n \<le> Suc k" and
         a3: "min_cell_index M w i (Suc k) = cell_index M w i n"
  have "n < Suc k \<Longrightarrow> False"
    using min_cell_index_min [of n k M w i, folded a3] apply simp
    by (smt (verit, best) a1 min_cell_index_le_cell_index)
  hence 1: "n = Suc k" using a2 by fastforce
  show "min_cell_index M w i (Suc k) = min_cell_index M w i k - 1"
    using a1 [folded 1]
    by (smt (verit, best) 1 a3 cell_index.simps(2,3,4) head_move.exhaust min_cell_index_le_cell_index)
qed

lemma min_cell_index_Suc: "min_cell_index M w i (Suc k) =
                           (if cell_index M w i (Suc k) \<ge> min_cell_index M w i k then
                           min_cell_index M w i k else min_cell_index M w i k - 1)"
  apply auto
   apply (erule min_cell_index_Suc1)
  apply (rule min_cell_index_Suc2)
  by simp

lemma max_cell_index_Suc_gt_impl_eq_cell_index_Suc: "max_cell_index M w i (Suc k) > max_cell_index M w i k \<Longrightarrow>
                                                     max_cell_index M w i (Suc k) = cell_index M w i (Suc k)"
  by (smt (verit, ccfv_threshold) max_cell_index_Suc1 max_cell_index_Suc2 max_cell_index_ge_cell_index)

lemma max_cell_index_Suc_gt_impl_eq_cell_index: "max_cell_index M w i (Suc k) > max_cell_index M w i k \<Longrightarrow>
                                                 max_cell_index M w i k = cell_index M w i k"
  by (smt (verit, best) cell_index.simps(2,3,4) head_move.exhaust max_cell_index_Suc_gt_impl_eq_cell_index_Suc
      max_cell_index_ge_cell_index)

lemma min_cell_index_Suc_lt_impl_eq_cell_index_Suc: "min_cell_index M w i (Suc k) < min_cell_index M w i k \<Longrightarrow>
                                                     min_cell_index M w i (Suc k) = cell_index M w i (Suc k)"
  by (smt (verit, ccfv_threshold) min_cell_index_Suc1 min_cell_index_Suc2 min_cell_index_le_cell_index)

lemma min_cell_index_Suc_lt_impl_eq_cell_index: "min_cell_index M w i (Suc k) < min_cell_index M w i k \<Longrightarrow>
                                                 min_cell_index M w i k = cell_index M w i k"
  by (smt (verit, best) cell_index.simps(2,3,4) head_move.exhaust min_cell_index_Suc_lt_impl_eq_cell_index_Suc
      min_cell_index_le_cell_index)

lemma cell_index_eq_next_moves_eq: "cell_index M1 w1 i1 k = cell_index M2 w2 i2 k \<Longrightarrow>
                                    TM.next_move M1 (state (TM.steps M1 k (TM.initial_config M1 w1)))
                                    (heads (TM.steps M1 k (TM.initial_config M1 w1))) i1 =
                                    TM.next_move M2 (state (TM.steps M2 k (TM.initial_config M2 w2)))
                                    (heads (TM.steps M2 k (TM.initial_config M2 w2))) i2 \<Longrightarrow>
                                    cell_index M1 w1 i1 (Suc k) = cell_index M2 w2 i2 (Suc k)"
  by (cases "TM.next_move M1 (state (TM.steps M1 k (TM.initial_config M1 w1)))
             (heads (TM.steps M1 k (TM.initial_config M1 w1))) i1") simp_all

lemma max_cell_Suc_uneq_p1: "max_cell_index M w i (Suc k) \<noteq> max_cell_index M w i k \<Longrightarrow>
                             max_cell_index M w i (Suc k) = max_cell_index M w i k + 1"
  by (smt (verit, best) max_cell_index_Suc1 max_cell_index_Suc2)

lemma min_cell_Suc_uneq_m1: "min_cell_index M w i (Suc k) \<noteq> min_cell_index M w i k \<Longrightarrow>
                             min_cell_index M w i (Suc k) = min_cell_index M w i k - 1"
  by (smt (verit, best) min_cell_index_Suc1 min_cell_index_Suc2)

lemma between_min_cell_index_max_cell_index_obtain:
  assumes "i \<ge> min_cell_index M w j k" and "i \<le> max_cell_index M w j k"
  obtains k' :: nat where "k' \<le> k" and "i = cell_index M w j k'"
  using assms apply (induction k)
   apply simp
proof -
  fix k :: nat
  assume a1: "(\<And>k'. k' \<le> k \<Longrightarrow> i = cell_index M w j k' \<Longrightarrow> thesis) \<Longrightarrow>
              min_cell_index M w j k \<le> i \<Longrightarrow> i \<le> max_cell_index M w j k \<Longrightarrow> thesis" and
         a2: "\<And>k'. k' \<le> Suc k \<Longrightarrow> i = cell_index M w j k' \<Longrightarrow> thesis" and
         a3: "min_cell_index M w j (Suc k) \<le> i" and a4: "i \<le> max_cell_index M w j (Suc k)"
  show thesis
    apply (cases "min_cell_index M w j (Suc k) = min_cell_index M w j k")
     apply (cases "max_cell_index M w j (Suc k) = max_cell_index M w j k")
    apply (rule a1)
      apply (rule a2)
       apply (erule le_SucI)
        apply assumption
    using a3 apply simp
    using a4 apply simp
     apply (cases "i = max_cell_index M w j (Suc k)")
      apply (metis a1 a2 a3 le_Suc_eq linorder_not_less max_cell_index_Suc_gt_impl_eq_cell_index_Suc)
     apply (smt (verit, best) a1 a2 a3 a4 le_Suc_eq max_cell_index_Suc1 max_cell_index_Suc2)
    apply (cases "max_cell_index M w j (Suc k) = max_cell_index M w j k")
     apply (cases "i = min_cell_index M w j (Suc k)")
      apply (metis a1 a2 a4 le_Suc_eq linorder_not_less min_cell_index_Suc_lt_impl_eq_cell_index_Suc)
    apply (smt (verit, best) a1 a2 a3 a4 le_Suc_eq min_cell_Suc_uneq_m1)
    apply (cases "i = min_cell_index M w j (Suc k)")
     apply (cases "i = max_cell_index M w j (Suc k)")
      apply (metis a2 dual_order.refl verit_la_disequality max_cell_index_Suc_gt_impl_eq_cell_index_Suc suc_is_ge
        linorder_not_less max_cell_index_mono)
     apply (metis a2 min_cell_index_Suc_lt_impl_eq_cell_index_Suc min_cell_index_revmono order_le_less suc_is_ge)
    apply (cases "i = max_cell_index M w j (Suc k)")
     apply (drule max_cell_Suc_uneq_p1)
     apply (drule min_cell_Suc_uneq_m1)
     apply simp
     apply (metis a2 max_cell_index_obtain)
    apply (drule max_cell_Suc_uneq_p1)
    apply (drule min_cell_Suc_uneq_m1)
    apply simp
    apply (rule a1)
    using a2 le_Suc_eq apply blast
    using a3 apply linarith
    using a4 by linarith
qed

lemma next_moves_eq_cell_index_eq: "(\<And>n. n \<le> k \<Longrightarrow> TM.next_move M1 (state (TM.steps M1 n (TM.initial_config M1 w1)))
                                    (heads (TM.steps M1 n (TM.initial_config M1 w1))) i1 =
                                    TM.next_move M2 (state (TM.steps M2 n (TM.initial_config M2 w2)))
                                    (heads (TM.steps M2 n (TM.initial_config M2 w2))) i2) \<Longrightarrow>
                                    cell_index M1 w1 i1 k = cell_index M2 w2 i2 k"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note 1 = Suc(2) [of k, simplified]
  show ?case apply (cases rule: cell_index.cases [of "(M1, w1, i1, Suc k)"])
       apply auto
    unfolding 1 cell_index.simps(2) apply (subst Suc(1))
    using Suc(2) apply fastforce
      apply standard
    unfolding cell_index.simps(3) apply (subst Suc(1))
    using Suc(2) apply fastforce
     apply standard
    unfolding cell_index.simps(4) apply (subst Suc(1))
    using Suc(2) apply fastforce
    ..
qed

lemma cell_index_eq_next_moves_eq': "(\<And>n. n \<le> k \<Longrightarrow> cell_index M1 w1 i1 n = cell_index M2 w2 i2 n) \<Longrightarrow> n < k \<Longrightarrow>
                                     TM.next_move M1 (state (TM.steps M1 n (TM.initial_config M1 w1)))
                                     (heads (TM.steps M1 n (TM.initial_config M1 w1))) i1 =
                                     TM.next_move M2 (state (TM.steps M2 n (TM.initial_config M2 w2)))
                                     (heads (TM.steps M2 n (TM.initial_config M2 w2))) i2"
proof (induction k arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  have 1: "cell_index M1 w1 i1 n' = cell_index M2 w2 i2 n'" using Suc.prems(1) by auto
  have 2: "cell_index M1 w1 i1 n = cell_index M2 w2 i2 n" using Suc.prems(1,2) by auto
  have 3: "cell_index M1 w1 i1 (Suc n') = cell_index M2 w2 i2 (Suc n')" using Suc.prems(1) by blast
  have 4: "cell_index M1 w1 i1 (Suc n) = cell_index M2 w2 i2 (Suc n)"
    using Suc.prems(1,2) less_eq_Suc_le by blast
  show ?case apply (cases "TM.TM.next_move M1 (state ((TM.step M1 ^^ n) (TM.initial_config M1 w1)))
                           (heads ((TM.step M1 ^^ n) (TM.initial_config M1 w1))) i1")
    using 4 apply (subst (asm) cell_index.simps(2))
       apply assumption
      apply (cases "TM.TM.next_move M2 (state ((TM.step M2 ^^ n) (TM.initial_config M2 w2)))
                    (heads ((TM.step M2 ^^ n) (TM.initial_config M2 w2))) i2")
    using 2 apply simp_all
    using 4 apply (subst (asm) cell_index.simps(3))
      apply assumption
     apply (cases "TM.TM.next_move M2 (state ((TM.step M2 ^^ n) (TM.initial_config M2 w2)))
                   (heads ((TM.step M2 ^^ n) (TM.initial_config M2 w2))) i2")
    using 2 apply simp_all
    using 4 apply (subst (asm) cell_index.simps(4))
     apply assumption
    apply (cases "TM.TM.next_move M2 (state ((TM.step M2 ^^ n) (TM.initial_config M2 w2)))
                  (heads ((TM.step M2 ^^ n) (TM.initial_config M2 w2))) i2")
    using 2 by simp_all
qed

lemma max_cell_index_eq_from_cell_index_eqs: "(\<And>k'. k' \<le> k \<Longrightarrow> cell_index M1 w1 i1 k' = cell_index M2 w2 i2 k') \<Longrightarrow>
                                              k' \<le> k \<Longrightarrow> max_cell_index M1 w1 i1 k' = max_cell_index M2 w2 i2 k'"
proof -
  assume a1: "\<And>k'. k' \<le> k \<Longrightarrow> cell_index M1 w1 i1 k' = cell_index M2 w2 i2 k'" and
         a2: "k' \<le> k"
  have 1: "{ci. \<exists>n\<le>k'. cell_index M1 w1 i1 n = ci} = {ci. \<exists>n\<le>k'. cell_index M2 w2 i2 n = ci}"
    using a1 a2 by auto
  show "max_cell_index M1 w1 i1 k' = max_cell_index M2 w2 i2 k'" unfolding max_cell_index_def 1 ..
qed

lemma min_cell_index_eq_from_cell_index_eqs: "(\<And>k'. k' \<le> k \<Longrightarrow> cell_index M1 w1 i1 k' = cell_index M2 w2 i2 k') \<Longrightarrow>
                                              k' \<le> k \<Longrightarrow> min_cell_index M1 w1 i1 k' = min_cell_index M2 w2 i2 k'"
proof -
  assume a1: "\<And>k'. k' \<le> k \<Longrightarrow> cell_index M1 w1 i1 k' = cell_index M2 w2 i2 k'" and
         a2: "k' \<le> k"
  have 1: "{ci. \<exists>n\<le>k'. cell_index M1 w1 i1 n = ci} = {ci. \<exists>n\<le>k'. cell_index M2 w2 i2 n = ci}"
    using a1 a2 by auto
  show "min_cell_index M1 w1 i1 k' = min_cell_index M2 w2 i2 k'" unfolding min_cell_index_def 1 ..
qed

lemma cell_index_is_max_Shift_Right: "cell_index M w i k = k \<Longrightarrow> k' < k \<Longrightarrow>
                                      TM.next_move M (state ((TM.step M ^^ k') (TM.initial_config M w)))
                                      (heads ((TM.step M ^^ k') (TM.initial_config M w))) i = Shift_Right"
proof (induction k arbitrary: k')
  case 0
  then show ?case by simp
next
  case (Suc k)
  hence 1: "cell_index M w i k = int k" using cell_index_eq_steps_all_lower_eq suc_is_ge by blast
  show ?case apply (cases "k' < k")
     apply (erule Suc(1) [OF 1, of k'])
    using Suc(2) apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                                (heads ((TM.step M ^^ k) (TM.initial_config M w))) i")
    using Suc(3) apply simp_all
    using cell_index_abs_bound [of M w i k] apply simp
    using less_Suc_eq apply blast
    using cell_index_abs_bound [of M w i k] by simp
qed

lemma cell_index_is_min_Shift_Left: "cell_index M w i k = -k \<Longrightarrow> k' < k \<Longrightarrow>
                                     TM.next_move M (state ((TM.step M ^^ k') (TM.initial_config M w)))
                                     (heads ((TM.step M ^^ k') (TM.initial_config M w))) i = Shift_Left"
proof (induction k arbitrary: k')
  case 0
  then show ?case by simp
next
  case (Suc k)
  hence 1: "cell_index M w i k = -int k" using cell_index_eq_minus_steps_all_lower_eq suc_is_ge by blast
  show ?case apply (cases "k' < k")
     apply (erule Suc(1) [OF 1, of k'])
    using Suc(2) apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                                (heads ((TM.step M ^^ k) (TM.initial_config M w))) i")
    using Suc(3) apply simp_all
    using less_Suc_eq apply blast
    using cell_index_abs_bound [of M w i k] by simp_all
qed

definition trim_tapes :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config" where
  "trim_tapes c \<equiv> TM_config (state c) (map (\<lambda>t. Tape (trimRight None (left t))
                  (head t) (trimRight None (right t))) (tapes c))"

lemma trim_tapes_state [simp]: "state (trim_tapes c) = state c"
  unfolding trim_tapes_def by simp

lemma trim_tapes_init_conf [simp]: "trim_tapes (TM.initial_config M w) =
                                    TM.initial_config M w"
  unfolding TM.initial_config_def trim_tapes_def apply auto
  unfolding TM_abbrevs.input_tape_def apply auto
  by (smt (verit) dropWhile_eq_self_iff hd_rev last_map map_is_Nil_conv
      option.discI rev_is_Nil_conv rev_swap)

lemma trim_tapes_heads [simp]: "heads (trim_tapes c) = heads c"
  unfolding trim_tapes_def by simp

lemma trim_tapes_tape_count [simp]: "length (tapes (trim_tapes c)) = length (tapes c)"
  unfolding trim_tapes_def by simp

lemma trim_tapes_left [simp]: "i < length (tapes c) \<Longrightarrow>
                               left (tapes (trim_tapes c) ! i) =
                               trimRight None (left (tapes c ! i))"
  unfolding trim_tapes_def by simp

lemma trim_tapes_right [simp]: "i < length (tapes c) \<Longrightarrow>
                               right (tapes (trim_tapes c) ! i) =
                               trimRight None (right (tapes c ! i))"
  unfolding trim_tapes_def by simp

lemma trim_tapes_normal [simp]: "trim_tapes (trim_tapes c) = trim_tapes c"
  unfolding trim_tapes_def by simp

lemma trim_tapes_step: "trim_tapes (TM.step M (trim_tapes c)) =
                        trim_tapes (TM.step M c)"
  unfolding TM.step_def apply auto
  unfolding TM.step_not_final_def Let_def apply auto
  unfolding trim_tapes_def apply (simp add: comp_def)
  apply (rule nth_equalityI)
   apply auto unfolding TM.next_actions_def TM_abbrevs.tape_action_def apply auto
proof -
  fix i :: nat
  assume a1: "i < length (tapes c)" and
         a2: "i < length (TM.next_writes M (state c) (heads c))" and
         a3: "i < length (TM.next_moves M (state c) (heads c))"
  show "trimLeft None (rev (left
        (TM_abbrevs.tape_shift (TM.next_moves M (state c) (heads c) ! i)
        (TM_abbrevs.tape_write (TM.next_writes M (state c) (heads c) ! i)
        (Tape (trimRight None (left (tapes c ! i))) (head (tapes c ! i))
        (trimRight None (right (tapes c ! i)))))))) = trimLeft None (rev (left
        (TM_abbrevs.tape_shift (TM.next_moves M (state c) (heads c) ! i)
        (TM_abbrevs.tape_write (TM.next_writes M (state c) (heads c) ! i)
        (tapes c ! i)))))" using a1 a2 a3
    unfolding TM.next_writes_def TM.next_moves_def apply auto
    apply (cases "TM.TM.next_move M (state c) (heads c) i") apply auto
      apply (rule rev_is_rev_conv [THEN iffD1]) unfolding trimRight_tl
      apply (auto simp add: TM_abbrevs.tape_write_hd)
    unfolding trimLeft_idem_app apply simp
    apply (rule rev_is_rev_conv [THEN iffD1])
    unfolding TM_abbrevs.tape_shift.simps(5) by simp
  have 1: "trimRight None (left (tapes c ! i)) = rev (rev as @ [a]) \<Longrightarrow>
           a = hd (left (tapes c ! i))" for as :: "'b option list" and
                                            a :: "'b option"
    apply (induction as)
  proof auto
    assume "trimLeft None (rev (left (tapes c ! i))) = [a]"
    then have "remdups_adj (None # rev (left (tapes c ! i))) = [None, a]"
      by (simp add: remdups_adj_Cons')
    then show ?thesis
      by (smt (z3) hd_append2 hd_remdups_adj list.sel(1) not_Cons_self2
          remdups_adj.simps(2) remdups_adj_rev rev.simps(2) rev_rev_ident
          rev_singleton_conv)
  next
    fix a' :: "'b option" and as :: "'b option list"
    assume "trimLeft None (rev (left (tapes c ! i))) = rev as @ [a', a]"
    hence "a = last (rev (left (tapes c ! i)))"
      by (metis append.left_neutral append_Cons dropWhile.simps(1)
          dropWhile_idem last_ConsL last_appendR last_remdups_adj list.distinct(1)
          remdups_adj_Cons')
    thus "a = hd (left (tapes c ! i))" using last_rev by blast
  qed
  have 2: "trimRight None (right (tapes c ! i)) = rev (rev as @ [a]) \<Longrightarrow>
           a = hd (right (tapes c ! i))" for as :: "'b option list" and a
    apply (induction as)
  proof auto
    show "trimLeft None (rev (right (tapes c ! i))) = [a] \<Longrightarrow>
          a = hd (right (tapes c ! i))"
    proof -
      assume a1: "trimLeft None (rev (right (tapes c ! i))) = [a]"
      have f2: "\<forall>zs. hd (remdups_adj zs) = (hd zs::'b option)"
        by simp
      have f3: "\<forall>zs. remdups_adj (rev (zs::'b option list)) = rev (remdups_adj zs)"
        using remdups_adj_rev by blast
      have f4: "\<forall>p. dropWhile p ([]::'b option list) = []"
        using dropWhile.simps(1) by blast
      have f5: "\<forall>z zs. hd ((z::'b option) # zs) = z"
        using list.sel(1) by blast
      have f6: "\<forall>z zs. [] \<noteq> (z::'b option) # zs"
        by blast
      have f7: "\<forall>zs zsa. (zsa::'b option list) = rev zs \<or> rev zsa \<noteq> zs"
        using rev_swap by blast
      have f8: "\<forall>zs zsa. zs = [] \<or> hd (zs @ zsa) = (hd zs::'b option)"
        using hd_append2 by blast
      have f9: "\<forall>z. remdups_adj [z::'b option] = z # remdups_adj []"
        by simp
      have f10: "\<forall>z zs. zs = rev [z::'b option] \<or> zs \<noteq> [z]"
        using f7 by blast
      have f11: "\<forall>zs z. hd (rev ((z::'b option) # zs)) = hd (rev zs) \<or> rev zs = []"
        by auto
      have f12: "\<forall>zs z. rev ((z::'b option) # rev zs) = zs @ [z]"
        by simp
      have f13: "remdups_adj (None # rev (right (tapes c ! i))) =
                 None # remdups_adj [a]"
        using a1 by (simp add: remdups_adj_Cons')
      obtain bb :: "'b option \<Rightarrow> 'b option \<Rightarrow> bool" where
        "dropWhile (bb None) (rev (right (tapes c ! i))) = [a]"
        using a1 by simp
      then show ?thesis
        using f13 f12 f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 by (smt (z3))
    qed
  next
    fix a' :: "'b option" and as :: "'b option list"
    assume "trimLeft None (rev (right (tapes c ! i))) = rev as @ [a', a]"
    hence "a = last (rev (right (tapes c ! i)))"
      by (metis append_is_Nil_conv last.simps last_append list.distinct(1)
          takeWhile_dropWhile_id)
    thus "a = hd (right (tapes c ! i))" using last_rev by blast
  qed
  show "head (TM_abbrevs.tape_shift (TM.next_moves M (state c) (heads c) ! i)
        (TM_abbrevs.tape_write (TM.next_writes M (state c) (heads c) ! i)
        (Tape (trimRight None (left (tapes c ! i))) (head (tapes c ! i))
        (trimRight None (right (tapes c ! i)))))) =
        head (TM_abbrevs.tape_shift (TM.next_moves M (state c) (heads c) ! i)
        (TM_abbrevs.tape_write (TM.next_writes M (state c) (heads c) ! i)
        (tapes c ! i)))" using a1 a2 a3
    unfolding TM.next_writes_def TM.next_moves_def apply auto
    apply (cases "TM.TM.next_move M (state c) (heads c) i") apply auto
      apply (cases "left (Tape (trimRight None (left (tapes c ! i)))
                    (head (tapes c ! i)) (trimRight None (right (tapes c ! i))))")
       apply auto
       apply (metis head_in_left_tape head_left_empty left_after_write)
      apply (rule Shift_Left_is_left_not_empty [THEN ssubst]) apply auto
      apply (rule TM.Shift_Left_is_left_not_empty [THEN ssubst]) apply auto
      apply (subst (asm) rev_is_rev_conv [symmetric]) apply (erule 1)
      apply (cases "right (Tape (trimRight None (left (tapes c ! i)))
                    (head (tapes c ! i)) (trimRight None (right (tapes c ! i))))")
      apply auto
      apply (metis head_in_right_tape head_right_empty right_after_write)
      apply (rule Shift_Right_is_right_not_empty [THEN ssubst]) apply auto
      apply (rule TM.Shift_Right_is_right_not_empty [THEN ssubst]) apply auto
     apply (subst (asm) rev_is_rev_conv [symmetric]) apply (erule 2)
    by (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_hd)
  show "trimLeft None (rev (right
        (TM_abbrevs.tape_shift (TM.next_moves M (state c) (heads c) ! i)
        (TM_abbrevs.tape_write (TM.next_writes M (state c) (heads c) ! i)
        (Tape (trimRight None (left (tapes c ! i))) (head (tapes c ! i))
        (trimRight None (right (tapes c ! i)))))))) = trimLeft None (rev (right
        (TM_abbrevs.tape_shift (TM.next_moves M (state c) (heads c) ! i)
        (TM_abbrevs.tape_write (TM.next_writes M (state c) (heads c) ! i)
        (tapes c ! i)))))" using a1 a2 a3
    unfolding TM.next_writes_def TM.next_moves_def apply auto
  proof -
    assume a1: "i < TM.TM.tape_count M"
    obtain bb :: "'b option \<Rightarrow> 'b option \<Rightarrow> bool" where
      f2: "\<forall>X0 x2. bb X0 x2 = (x2 = X0)"
      by moura
    have f3: "\<forall>t. TM_abbrevs.tape_shift No_Shift (t::'b tape) = t"
      using TM_abbrevs.tape_shift.simps(5) by blast
    have f4: "\<forall>z t. head (TM_abbrevs.tape_write (z::'b option) t) = z"
      by (simp add: TM_abbrevs.tape_write_hd)
    have f5: "\<forall>t z. right (TM_abbrevs.tape_write (z::'b option) t) = right t"
      using right_after_write by blast
    have f6: "\<forall>zs z zsa za. TM_abbrevs.tape_write (z::'b option) (Tape zs za zsa) =
              Tape zs z zsa"
      by (simp add: TM_abbrevs.tape_write_simps)
    have f7: "\<forall>zs zsa z. right (Tape zsa (z::'b option) zs) = zs"
      by simp
    have f8: "\<forall>z zs zsa. head (Tape zs (z::'b option) zsa) = z"
      by simp
    have f9: "\<forall>zs. rev (rev (zs::'b option list)) = zs"
      by simp
    have f10: "\<forall>p zs. dropWhile p (dropWhile p (zs::'b option list)) = dropWhile p zs"
      by simp
    have f11: "\<forall>n t a zs. \<not> n < TM.TM.tape_count (t::('a, 'b, 'c) TM) \<or>
               TM.next_writes t a zs ! n = TM.TM.next_write t a zs n"
      by (smt (z3) TM.next_writes_simps(1))
    have f12: "\<forall>h. h = Shift_Right \<or> h = No_Shift \<or> h = Shift_Left"
      by (smt (z3) head_move.exhaust)
    have f13: "\<forall>zs z. rev ((z::'b option) # zs) = rev zs @ [z]"
      by simp
    have f14: "\<forall>t. right (TM_abbrevs.tape_shift Shift_Right (t::'b tape)) =
               tl (right t)"
      using right_Shift_Right by blast
    have f15: "\<forall>t. right (TM_abbrevs.tape_shift Shift_Left (t::'b tape)) =
               head t # right t"
      using right_Shift_Left by blast
    have f16: "\<forall>z zs. trimRight (z::'b option) (tl zs) = tl (trimRight z zs)"
      using trimRight_tl by blast
    have f17: "\<forall>z zs zsa. trimLeft (z::'b option) (trimLeft z zs @ zsa) =
               trimLeft z (zs @ zsa)"
      using trimLeft_idem_app by blast
    have f18: "\<forall>z zs. rev (dropWhile (bb z) (rev (tl zs))) =
               tl (rev (dropWhile (bb z) (rev zs)))"
      using f16 f2 by presburger
    have "\<forall>z zs zsa. dropWhile (bb z) (dropWhile (bb z) zs @ zsa) =
          dropWhile (bb z) (zs @ zsa)"
      using f17 f2 by presburger
    then have "dropWhile (bb None) (rev (right (TM_abbrevs.tape_shift
               (TM.TM.next_move M (state c) (heads c) i) (TM_abbrevs.tape_write
               (TM.TM.next_write M (state c) (heads c) i)
               (Tape (rev (dropWhile (bb None) (rev (left (tapes c ! i)))))
               (head (tapes c ! i)) (rev (dropWhile (bb None)
               (rev (right (tapes c ! i)))))))))) =
               dropWhile (bb None) (rev (right (TM_abbrevs.tape_shift
               (TM.TM.next_move M (state c) (heads c) i) (TM_abbrevs.tape_write
               (TM.TM.next_write M (state c) (heads c) i) (tapes c ! i)))))"
      using f18 f15 f14 f13 f12 f11 f10 f9 f8 f7 f6 f5 f4 f3 a1 by (smt (z3))
    then show "trimLeft None (rev (right (TM_abbrevs.tape_shift
               (TM.TM.next_move M (state c) (heads c) i) (TM_abbrevs.tape_write
               (TM.TM.next_write M (state c) (heads c) i)
               (Tape (trimRight None (left (tapes c ! i))) (head (tapes c ! i))
               (trimRight None (right (tapes c ! i)))))))) =
               trimLeft None (rev (right (TM_abbrevs.tape_shift (TM.TM.next_move M
               (state c) (heads c) i) (TM_abbrevs.tape_write (TM.TM.next_write M
               (state c) (heads c) i) (tapes c ! i)))))"
      using f2
    proof -
      { assume "TM.TM.next_move M (state c) (heads c) i \<noteq> No_Shift"
        moreover
        { assume "TM.TM.next_move M (state c) (heads c) i \<noteq> No_Shift \<and>
                  TM.TM.next_move M (state c) (heads c) i \<noteq> Shift_Left"
          then have "trimLeft None (rev (tl (trimRight None (right (tapes c ! i))))) =
                     trimLeft None (rev (tl (right (tapes c ! i)))) \<and>
                     TM.TM.next_move M (state c) (heads c) i \<noteq> No_Shift \<and>
                     TM.TM.next_move M (state c) (heads c) i \<noteq> Shift_Left"
            by (metis f10 f9 trimRight_tl)
          then have "trimLeft None (rev (right (TM_abbrevs.tape_shift
                     (TM.TM.next_move M (state c) (heads c) i) (Tape (left (Tape
                     (trimRight None (left (tapes c ! i))) (head (tapes c ! i))
                     (trimRight None (right (tapes c ! i))))) (TM.TM.next_write M
                     (state c) (heads c) i) (trimRight None
                     (right (tapes c ! i))))))) =
                     trimLeft None (rev (right (TM_abbrevs.tape_shift
                     (TM.TM.next_move M (state c) (heads c) i) (Tape (left
                     (tapes c ! i)) (TM.TM.next_write M (state c) (heads c) i)
                     (right (tapes c ! i))))))"
            by (smt (z3) head_move.exhaust right_Shift_Right tape.sel(3)) }
        ultimately have "trimLeft None (rev (right (TM_abbrevs.tape_shift
                         (TM.TM.next_move M (state c) (heads c) i) (Tape (left (Tape
                         (trimRight None (left (tapes c ! i))) (head (tapes c ! i))
                         (trimRight None (right (tapes c ! i)))))
                         (TM.TM.next_write M (state c) (heads c) i) (trimRight None
                         (right (tapes c ! i))))))) =
                         trimLeft None (rev (right (TM_abbrevs.tape_shift
                         (TM.TM.next_move M (state c) (heads c) i)
                         (Tape (left (tapes c ! i)) (TM.TM.next_write M (state c)
                         (heads c) i) (right (tapes c ! i))))))"
          using trimLeft_idem_app by fastforce }
      then show ?thesis
        by (smt (z3) TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_def f10
            f9 tape.sel(3))
    qed
  qed
qed

lemma trim_tapes_steps: "trim_tapes (TM.steps M n (trim_tapes c)) =
                         trim_tapes (TM.steps M n c)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (metis comp_apply funpow.simps(2) trim_tapes_step)
qed

lemma trim_tapes_run: "trim_tapes c = TM.initial_config M w \<Longrightarrow>
                       trim_tapes (TM.run M n w) = trim_tapes (TM.steps M n c)"
  unfolding TM.run_def using trim_tapes_steps by metis

lemma trim_tapes_prefix_left: "i < length (tapes c) \<Longrightarrow>
                               prefix (left (tapes (trim_tapes c) ! i)) (left (tapes c ! i))"
  unfolding trim_tapes_def apply simp
  by (metis prefixI rev_append rev_rev_ident takeWhile_dropWhile_id)

lemma trim_tapes_prefix_right: "i < length (tapes c) \<Longrightarrow>
                          prefix (right (tapes (trim_tapes c) ! i)) (right (tapes c ! i))"
  unfolding trim_tapes_def apply simp
  by (metis prefixI rev_append rev_rev_ident takeWhile_dropWhile_id)

lemma trim_tapes_left_nth_Some: "i < length (tapes c) \<Longrightarrow>
                                 j < length (left (tapes c ! i)) \<Longrightarrow>
                                 left (tapes c ! i) ! j = Some s \<Longrightarrow>
                                 left (tapes (trim_tapes c) ! i) ! j = Some s"
proof (induction "left (tapes c ! i)" arbitrary: s j c rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case IH: (snoc x xs)
  obtain c' :: "('b, 'a) TM_config" where c'_state: "state c' = state c" and
    c'_i_left: "left (tapes c' ! i) = xs" and
    c'_tapes_length: "length (tapes c') = length (tapes c)" and
    c'_lefts: "\<And>i'. i' \<noteq> i \<Longrightarrow> i' < length (tapes c') \<Longrightarrow>
               left (tapes c' ! i') = left (tapes c ! i')" and
    c'_heads: "\<And>j. j < length (tapes c') \<Longrightarrow> head (tapes c' ! j) = head (tapes c ! j)" and
    c'_rights: "\<And>j. j < length (tapes c') \<Longrightarrow> right (tapes c' ! j) = right (tapes c ! j)"
  proof
    define c' :: "('b, 'a) TM_config" where "c' \<equiv> TM_config (state c) ((take i (tapes c)) @
      [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @ (drop (Suc i) (tapes c)))"
    show "state c' = state c" unfolding c'_def by simp
    show "left (tapes (TM_config (state c) (take i (tapes c) @
          [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
          drop (Suc i) (tapes c))) ! i) = xs" apply simp
      by (metis IH.prems(1) length_take linorder_not_less min_def nth_append_length
          tape.sel(1))
    show 1: "length (tapes (TM_config (state c) (take i (tapes c) @
             [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
             drop (Suc i) (tapes c)))) = length (tapes c)" apply simp
      using IH.prems(1) by force
    fix i' :: nat
    show "i' \<noteq> i \<Longrightarrow> i' < length (tapes (TM_config (state c) (take i (tapes c) @
          [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
          drop (Suc i) (tapes c)))) \<Longrightarrow>
          left (tapes (TM_config (state c) (take i (tapes c) @
          [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
          drop (Suc i) (tapes c))) ! i') = left (tapes c ! i')" apply simp
      unfolding 1 [simplified]
      by (metis IH.prems(1) nth_list_update_neq upd_conv_take_nth_drop)
    fix j :: nat
    show "j < length (tapes (TM_config (state c) (take i (tapes c) @
          [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
          drop (Suc i) (tapes c)))) \<Longrightarrow>
          head (tapes (TM_config (state c) (take i (tapes c) @
          [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
          drop (Suc i) (tapes c))) ! j) = head (tapes c ! j)" apply simp
      by (metis IH.prems(1) length_take[of i "tapes c"] min.absorb4[of i "length (tapes c)"]
          nth_append_length[of "take i (tapes c)"
            "Tape xs (head (tapes c ! i)) (right (tapes c ! i))" "drop (Suc i) (tapes c)"]
          nth_list_update_neq[of i j "tapes c"
            "Tape xs (head (tapes c ! i)) (right (tapes c ! i))"]
          tape.sel(2)[of xs "head (tapes c ! i)" "right (tapes c ! i)"]
          upd_conv_take_nth_drop[of i "tapes c"
            "Tape xs (head (tapes c ! i)) (right (tapes c ! i))"])
    show "j < length (tapes (TM_config (state c) (take i (tapes c) @
          [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
          drop (Suc i) (tapes c)))) \<Longrightarrow>
          right (tapes (TM_config (state c) (take i (tapes c) @
          [Tape xs (head (tapes c ! i)) (right (tapes c ! i))] @
          drop (Suc i) (tapes c))) ! j) = right (tapes c ! j)" apply simp
      by (metis IH.prems(1) length_take min.absorb4 nth_append_length nth_list_update_neq
          tape.collapse tape.inject upd_conv_take_nth_drop)
  qed
  note 1 = IH(1) [OF c'_i_left [symmetric] IH(3) [folded c'_tapes_length]]
  have 2: "length (left (tapes c ! i)) = Suc (length (left (tapes c' ! i)))"
    unfolding IH(2) [symmetric] c'_i_left by simp
  show ?case
  proof (cases x)
    case None
    have 3: "left (tapes (trim_tapes c) ! i) = left (tapes (trim_tapes c') ! i)"
      unfolding trim_tapes_def apply simp
      by (metis (mono_tags, lifting) IH.hyps(2) IH.prems(1) None TM_config.sel(2) c'_i_left
          c'_tapes_length dropWhile.simps(2) rev.simps(2) rev_rev_ident trim_tapes_def
          trim_tapes_left)
    show ?thesis unfolding 3 apply (rule 1)
      apply (metis 2 IH.hyps(2) IH.prems(2,3) None c'_i_left less_antisym nth_append_length
          option.discI)
      by (metis 2 IH.hyps(2) IH.prems(2,3) None c'_i_left not_less_less_Suc_eq
          nth_append_left nth_append_length option.distinct(1))
  next
    case (Some a)
    have 3: "left (tapes (trim_tapes c) ! i) = left (tapes c ! i)"
      unfolding trim_tapes_def IH(2) [symmetric] Some apply simp
      by (smt (z3) IH.hyps(2) IH.prems(1) Some TM_config.sel(2) append_Cons
          dropWhile.simps(2) option.distinct(1) rev_append rev_eq_append_conv
          rev_singleton_conv trim_tapes_def trim_tapes_left)
    show ?thesis unfolding 3 by fact
  qed
qed

lemma trim_tapes_right_nth_Some: "i < length (tapes c) \<Longrightarrow>
                                  j < length (right (tapes c ! i)) \<Longrightarrow>
                                  right (tapes c ! i) ! j = Some s \<Longrightarrow>
                                  right (tapes (trim_tapes c) ! i) ! j = Some s"
proof (induction "right (tapes c ! i)" arbitrary: s j c rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case IH: (snoc x xs)
  obtain c' :: "('b, 'a) TM_config" where c'_state: "state c' = state c" and
    c'_i_right: "right (tapes c' ! i) = xs" and
    c'_tapes_length: "length (tapes c') = length (tapes c)" and
    c'_rights: "\<And>i'. i' \<noteq> i \<Longrightarrow> i' < length (tapes c') \<Longrightarrow>
               right (tapes c' ! i') = right (tapes c ! i')" and
    c'_heads: "\<And>j. j < length (tapes c') \<Longrightarrow> head (tapes c' ! j) = head (tapes c ! j)" and
    c'_lefts: "\<And>j. j < length (tapes c') \<Longrightarrow> left (tapes c' ! j) = left (tapes c ! j)"
  proof
    define c' :: "('b, 'a) TM_config" where "c' \<equiv> TM_config (state c) ((take i (tapes c)) @
      [Tape (left (tapes c ! i)) (head (tapes c ! i)) xs] @ (drop (Suc i) (tapes c)))"
    show "state c' = state c" unfolding c'_def by simp
    show "right (tapes (TM_config (state c) (take i (tapes c) @
          [Tape (left (tapes c ! i)) (head (tapes c ! i)) xs] @
          drop (Suc i) (tapes c))) ! i) = xs" apply simp
      by (metis IH.prems(1) length_take min.absorb4 nth_append_length tape.sel(3))
    show 1: "length (tapes c') = length (tapes c)" unfolding c'_def apply simp
      using IH.prems(1) by force
    fix i' :: nat
    show "i' \<noteq> i \<Longrightarrow> i' < length (tapes c') \<Longrightarrow>
          right (tapes c' ! i') = right (tapes c ! i')" unfolding c'_def apply simp
      unfolding 1 [simplified]
      by (metis IH.prems(1) nth_list_update_neq upd_conv_take_nth_drop)
    fix j :: nat
    show "j < length (tapes c') \<Longrightarrow>
          head (tapes c' ! j) = head (tapes c ! j)" unfolding c'_def apply simp
      by (metis IH.prems(1)
          cancel_comm_monoid_add_class.diff_cancel[of "length (take i (tapes c))"]
          le_refl[of "length (take i (tapes c))"]
          nth_Cons_0[of "(tapes c)[i := Tape (left (tapes c ! i)) (head (tapes c ! i)) xs]
            ! i" "drop (Suc i) (tapes c)"]
          nth_Cons_0[of "Tape (left (tapes c ! i)) (head (tapes c ! i)) xs"
            "drop (Suc i) (tapes c)"]
          nth_append_right[of "take i (tapes c)" "length (take i (tapes c))"
            "(tapes c)[i := Tape (left (tapes c ! i)) (head (tapes c ! i)) xs] ! i #
       drop (Suc i) (tapes c)"]
            nth_append_right[of "take i (tapes c)" "length (take i (tapes c))"
              "Tape (left (tapes c ! i)) (head (tapes c ! i)) xs # drop (Suc i) (tapes c)"]
            nth_list_update_neq[of i j "tapes c" "Tape (left (tapes c ! i))
              (head (tapes c ! i)) xs"]
            nth_list_update_neq[of i "length (take i (tapes c))" "tapes c"
              "(tapes c)[i := Tape (left (tapes c ! i)) (head (tapes c ! i)) xs] ! i"]
            nth_list_update_neq[of i "length (take i (tapes c))" "tapes c"
              "Tape (left (tapes c ! i)) (head (tapes c ! i)) xs"]
            tape.sel(2)[of "left (tapes c ! i)" "head (tapes c ! i)" xs]
            upd_conv_take_nth_drop[of i "tapes c"
              "(tapes c)[i := Tape (left (tapes c ! i)) (head (tapes c ! i)) xs] ! i"]
            upd_conv_take_nth_drop[of i "tapes c"
              "Tape (left (tapes c ! i)) (head (tapes c ! i)) xs"])
    show "j < length (tapes c') \<Longrightarrow>
          left (tapes c' ! j) = left (tapes c ! j)" unfolding c'_def apply simp
      by (metis IH.prems(1) length_take min.absorb4 nth_append_length nth_list_update_neq
          tape.collapse tape.inject upd_conv_take_nth_drop)
  qed
  note 1 = IH(1) [OF c'_i_right [symmetric] IH(3) [folded c'_tapes_length]]
  have 2: "length (right (tapes c ! i)) = Suc (length (right (tapes c' ! i)))"
    unfolding IH(2) [symmetric] c'_i_right by simp
  show ?case
  proof (cases x)
    case None
    have 3: "right (tapes (trim_tapes c) ! i) = right (tapes (trim_tapes c') ! i)"
      unfolding trim_tapes_def apply simp
      by (metis (mono_tags, lifting) IH.hyps(2) IH.prems(1) None TM_config.sel(2) c'_i_right
          c'_tapes_length dropWhile.simps(2) rev.simps(2) rev_swap trim_tapes_def
          trim_tapes_right)
    show ?thesis unfolding 3 apply (rule 1)
      apply (metis 2 IH.hyps(2) IH.prems(2,3) None c'_i_right less_antisym nth_append_length
          option.discI)
      by (metis 2 IH.hyps(2) IH.prems(2,3) None c'_i_right not_less_less_Suc_eq
          nth_append_left nth_append_length option.distinct(1))
  next
    case (Some a)
    have 3: "right (tapes (trim_tapes c) ! i) = right (tapes c ! i)"
      unfolding trim_tapes_def IH(2) [symmetric] Some apply simp
      by (metis (mono_tags, lifting) IH.hyps(2) IH.prems(1) Some TM_config.sel(2)
          append.left_neutral dropWhile.simps(1) dropWhile_append3 option.distinct(1)
          rev.simps(2) rev_rev_ident trim_tapes_def trim_tapes_right)
    show ?thesis unfolding 3 by fact
  qed
qed

lemma trim_tapes_left_nth_Some': "i < length (tapes c) \<Longrightarrow>
                                  j < length (left (tapes (trim_tapes c) ! i)) \<Longrightarrow>
                                  left (tapes (trim_tapes c) ! i) ! j = Some s \<Longrightarrow>
                                  left (tapes c ! i) ! j = Some s"
  by simp (metis length_rev nth_append_left rev_append rev_rev_ident
      takeWhile_dropWhile_id)

lemma trim_tapes_right_nth_Some': "i < length (tapes c) \<Longrightarrow>
                                   j < length (right (tapes (trim_tapes c) ! i)) \<Longrightarrow>
                                   right (tapes (trim_tapes c) ! i) ! j = Some s \<Longrightarrow>
                                   right (tapes c ! i) ! j = Some s"
  by simp (metis length_rev nth_append_left rev_append rev_rev_ident
      takeWhile_dropWhile_id)

lemma TM_steps_valid_stateI: "set w \<subseteq> TM.symbols M \<Longrightarrow>
                              state (TM.steps M n (TM.initial_config M w)) \<in> TM.states M"
  by (meson TM.wf_config_def TM.wf_initial_config TM.wf_steps
      lists_member)

lemma TM_computes_word_left_is_empty: "TM.computes_word M wi wo \<Longrightarrow>
       TM.is_final M (TM.steps M n (TM.initial_config M wi)) \<Longrightarrow>
       left (last (tapes (TM.steps M n (TM.initial_config M wi)))) = []"
  by (simp add: TM.compute_run_eqI TM.computes_word_def TM.has_output_altdef TM.run_def
      TM_abbrevs.input_tape_left)

lemma heads_with_input_eq_states_eq:"(\<And>n. n \<le> k \<Longrightarrow> heads (TM.steps M n (TM.initial_config M w)) =
                                     heads (TM.steps M n (TM.initial_config M w'))) \<Longrightarrow>
                                     state (TM.steps M k (TM.initial_config M w)) =
                                     state (TM.steps M k (TM.initial_config M w'))"
proof (induction k)
  case 0
  show ?case unfolding TM.initial_config_def by simp
next
  case (Suc k)
  have *: "\<And>n. n \<le> k \<Longrightarrow> heads ((TM.step M ^^ n) (TM.initial_config M w)) =
           heads ((TM.step M ^^ n) (TM.initial_config M w'))" using Suc(2) by simp
  show ?case using Suc(1) [OF *, simplified] apply auto
    apply (subst (1 2) TM.step_def)
    apply auto
    unfolding Suc(2) [of k, simplified] by simp
qed

lemma heads_of_first_tape_eq_heads_eq:
  assumes "\<And>n. n \<le> k \<Longrightarrow> heads (TM.steps M n (TM.initial_config M w)) ! 0 =
           heads (TM.steps M n (TM.initial_config M w')) ! 0"
  shows "heads (TM.steps M k (TM.initial_config M w)) = heads (TM.steps M k (TM.initial_config M w'))"
proof -
  have 1: "tapes (TM.steps M k (TM.initial_config M w)) ! i = tapes (TM.steps M k (TM.initial_config M w')) ! i"
    if "i < TM.tape_count M" and "i > 0" for i :: nat using assms(1) that
  proof (induction k arbitrary: i rule: full_nat_induct2)
    case 0
    show ?case apply simp
      unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
      using 0(2, 3) by simp_all
  next
    case (lt_Suc k)
    hence *: "\<And>n. n \<le> k \<Longrightarrow> heads ((TM.step M ^^ n) (TM.initial_config M w)) ! 0 =
              heads ((TM.step M ^^ n) (TM.initial_config M w')) ! 0" by simp
    note lt_Suc(1) [OF _ *]
    hence 1: "\<And>m. m \<le> k \<Longrightarrow> tapes ((TM.step M ^^ m) (TM.initial_config M w)) ! i =
              tapes ((TM.step M ^^ m) (TM.initial_config M w')) ! i"
      if "i > 0" and "i < TM.tape_count M" for i :: nat using that(1,2) by fastforce
    have 2: "\<And>m. m \<le> k \<Longrightarrow> heads ((TM.step M ^^ m) (TM.initial_config M w)) =
              heads ((TM.step M ^^ m) (TM.initial_config M w'))"
      apply (rule nth_equalityI')
       apply auto
       apply (simp add: TM.run_tapes_len)
      using * 1 by (metis TM.run_tapes_len bot_nat_0.not_eq_extremum nth_map)
    note 3 = heads_with_input_eq_states_eq [OF 2, of k, simplified]
    have 4: "[0..<TM.TM.tape_count M] ! i = i" using lt_Suc(3) by simp
    show ?case apply simp
      apply (subst (1 2) TM.step_def)
      apply auto
      unfolding 3 apply auto
       apply (subst 1)
          apply auto
        apply (rule lt_Suc(4))
       apply (rule lt_Suc(3))
      apply (subst (1 2) nth_map2)
          apply (metis TM.next_actions_simps(2) lt_Suc.prems(2))
         apply (simp add: TM.run_tapes_len lt_Suc.prems(2))
        apply (simp add: TM.next_actions_simps(2) lt_Suc.prems(2))
       apply (simp add: TM.run_tapes_len lt_Suc.prems(2))
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
      apply (subst (1 2 3 4) nth_zip)
          apply auto
          apply (rule lt_Suc(3))+
      apply (subst (1 2 3 4) nth_map)
       apply auto
       apply (rule lt_Suc(3))
      unfolding 4 2 [OF Nat.le_refl]
       apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w')))
                     (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i")
        apply auto
      by (simp_all add: 1 lt_Suc.prems(2,3))
  qed
  show ?thesis
    apply (rule nth_equalityI')
     apply auto
     apply (simp add: TM.run_tapes_len)
    using 1 assms(1) [OF Nat.le_refl] by (metis TM.run_tapes_len bot_nat_0.not_eq_extremum nth_map)
qed

lemma heads_of_first_tape_eq_tapes_eq:
  assumes "\<And>n. n \<le> k \<Longrightarrow> heads (TM.steps M n (TM.initial_config M w)) ! 0 =
           heads (TM.steps M n (TM.initial_config M w')) ! 0" and "i > 0" and "i < TM.tape_count M"
  shows "tapes (TM.steps M k (TM.initial_config M w)) ! i = tapes (TM.steps M k (TM.initial_config M w')) ! i"
  using assms(1, 3, 2)
proof (induction k arbitrary: i rule: full_nat_induct2)
  case 0
  show ?case apply simp
    unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
    using 0(2, 3) by simp_all
next
  case (lt_Suc k)
  hence *: "\<And>n. n \<le> k \<Longrightarrow> heads ((TM.step M ^^ n) (TM.initial_config M w)) ! 0 =
            heads ((TM.step M ^^ n) (TM.initial_config M w')) ! 0" by simp
  note lt_Suc(1) [OF _ *]
  hence 1: "\<And>m. m \<le> k \<Longrightarrow> tapes ((TM.step M ^^ m) (TM.initial_config M w)) ! i =
            tapes ((TM.step M ^^ m) (TM.initial_config M w')) ! i"
    if "i > 0" and "i < TM.tape_count M" for i :: nat using that(1,2) by fastforce
  have 2: "\<And>m. m \<le> k \<Longrightarrow> heads ((TM.step M ^^ m) (TM.initial_config M w)) =
           heads ((TM.step M ^^ m) (TM.initial_config M w'))"
    apply (rule nth_equalityI')
     apply auto
     apply (simp add: TM.run_tapes_len)
    using * 1 by (metis TM.run_tapes_len bot_nat_0.not_eq_extremum nth_map)
  note 3 = heads_with_input_eq_states_eq [OF 2, of k, simplified]
  have 4: "[0..<TM.TM.tape_count M] ! i = i" using lt_Suc(3) by simp
  show ?case apply simp
    apply (subst (1 2) TM.step_def)
    apply auto
    unfolding 3 apply auto
     apply (subst 1)
        apply auto
      apply (rule lt_Suc(4))
     apply (rule lt_Suc(3))
    apply (subst (1 2) nth_map2)
        apply (metis TM.next_actions_simps(2) lt_Suc.prems(2))
       apply (simp add: TM.run_tapes_len lt_Suc.prems(2))
      apply (simp add: TM.next_actions_simps(2) lt_Suc.prems(2))
     apply (simp add: TM.run_tapes_len lt_Suc.prems(2))
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
    apply (subst (1 2 3 4) nth_zip)
        apply auto
        apply (rule lt_Suc(3))+
    apply (subst (1 2 3 4) nth_map)
     apply auto
     apply (rule lt_Suc(3))
    unfolding 4 2 [OF Nat.le_refl]
     apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w')))
                   (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i")
      apply auto
    by (simp_all add: 1 lt_Suc.prems(2,3))
qed

lemma TM_steps_valid_headsI: "set w \<subseteq> TM.symbols M \<Longrightarrow>
                              set (heads (TM.steps M k (TM.initial_config M w))) \<subseteq> options (TM.symbols M)"
  by (meson TM.wf_config_hds(2) TM.wf_initial_config TM.wf_steps lists_member)

(* Note: having this much code commented out leads to errors when importing this theory sometimes.
         (Isabelle reports this theory as broken)
         My guess is that Isabelle tries to verify the theory, but does not look ahead far enough
         to find the end-comment, and therefore concludes that the theory is broken. *)

(*
definition "input_assert (P::'s list \<Rightarrow> bool) \<equiv> \<lambda>c::('q, 's::finite, 'l) TM_config.
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
*)
end
