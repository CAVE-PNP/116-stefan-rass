section\<open>The Time Hierarchy Theorem and the Language \<open>L\<^sub>0\<close>\<close>

theory L0
  imports SQ Complexity TM_Encoding Transformations
begin

subsection\<open>Preliminaries\<close>

(* tcomp is used to avoid the situation that SQ of some input i can be decided
   in length i steps. This would mean that the deciding TM couldn't distinguish inputs j with
   length j = length i with longer ones (see lemmas typed_DTIME_tb_le_n and typed_DTIME_tb_le_n_const).
   But then the TM couldn't decide the language.
   For the time being we have a Java program that demonstrates this lemma instead of a formal proof *)
lemma SQ_DTIME: "SQ \<in> DTIME (tcomp (\<lambda>n. n^3))" sorry

lemma SQ'_DTIME: "SQ' \<in> DTIME (tcomp (\<lambda>n. n^3))" using SQ_DTIME ext_DTIME sorry

locale UTM_Encoding =
  fixes enc\<^sub>U :: "('q, 's, 'l) TM \<times> 's list \<Rightarrow> bool list list"
    and is_valid_enc\<^sub>U :: "bool list list \<Rightarrow> bool"
    and dec\<^sub>U :: "bool list list \<Rightarrow> ('q, 's, 'l) TM \<times> 's list"
    and L_invalid :: 'l
  assumes inj_enc\<^sub>U: "inj_on enc\<^sub>U (range canonical_TM \<times> UNIV)"
    and valid_encu: "\<And>M w. TM.wf_input M w \<Longrightarrow> is_valid_enc\<^sub>U (enc\<^sub>U (M, w))"
    and enc_decu:   "\<And>M w. TM.wf_input M w \<Longrightarrow> dec\<^sub>U (enc\<^sub>U (M, w)) = (canonical_TM M, w)" (* TODO again, this is not possible with the current definitions, as label is an unrestricted function *)

      (* TODO is this necessary? could the UTM not just directly output the invalid label when it detects that an encoding is invalid? *)
    and invalid_rejects: "\<And>x. \<not> is_valid_enc\<^sub>U x \<Longrightarrow> let (M, w) = dec\<^sub>U x; c = TM.compute M w in TM.is_final M c \<and> TM.label M (state c) = L_invalid" (* a nicer version of: "\<exists>q\<^sub>0 s w. dec\<^sub>U x = (rejecting_TM q\<^sub>0 s, w)" *)
    and dec_enc: "\<And>x. is_valid_enc\<^sub>U x \<Longrightarrow> enc\<^sub>U (dec\<^sub>U x) = x" (* this should be easy to achieve *)

locale UTM = UTM: TM M\<^sub>U + UTM_Encoding enc\<^sub>U is_valid_enc\<^sub>U dec\<^sub>U False
  for M\<^sub>U :: "('q, bool list) TM_decider" (* TODO make 'q = nat ? *)
    and enc\<^sub>U :: "('q, bool list) TM_decider \<times> bool list list \<Rightarrow> bool list list"
    and is_valid_enc\<^sub>U dec\<^sub>U +
  assumes halts_iff: "\<And>M w. TM.halts M w \<longleftrightarrow> TM.halts M\<^sub>U (enc\<^sub>U (M, w))"
    and accepts_iff: "\<And>M w. TM_decider.accepts M w \<longleftrightarrow> TM_decider.accepts M\<^sub>U (enc\<^sub>U (M, w))"
    and M\<^sub>U_syms_subset: "{s. length s = 2} \<subseteq> TM.symbols M\<^sub>U"
begin
lemma rejects_iff: "TM_decider.rejects M w \<longleftrightarrow> TM_decider.rejects M\<^sub>U (enc\<^sub>U (M, w))"
  by (metis accepts_iff halts_iff TM_decider.rejects_accepts)
end

locale timed_UTM = UTM M\<^sub>U  for M\<^sub>U :: "(nat, bool list) TM_decider" +
  fixes T\<^sub>U :: "nat \<Rightarrow> nat" \<comment> \<open>Simulation time overhead of \<^term>\<open>M\<^sub>U\<close>.\<close>
  assumes sim_overhead: "\<And>M::(nat, bool list) TM_decider. \<And>w. TM.halts M w \<Longrightarrow>
    TM.time M\<^sub>U (enc\<^sub>U (M, w)) \<le> T\<^sub>U (TM.time M w)"
    and overhead_min: "T\<^sub>U n \<ge> n" \<comment> \<open>This should be trivially true, but is required for the THT.\<close>

subsection\<open>The Time Hierarchy Theorem\<close>

locale tht_assms = TM_Encoding' + timed_UTM +
  fixes T t :: "nat \<Rightarrow> nat" and c\<^sub>t :: real
  (* It is a bit weird to use natural numbers as symbols here, but who cares... we have the
     the rule typed_fully_time_constr_natI to make up for it. *)
  assumes fully_tconstr_T: "fully_time_constr T"

  \<comment> \<open>This assumption represents the statements containing \<open>lim\<close> @{cite rassOwf2017} and \<open>lim inf\<close> @{cite hopcroftAutomata1979}.
      \<^const>\<open>LIMSEQ\<close> (\<^term>\<open>X \<longlonglongrightarrow> x\<close>) was chosen, as it seems to match the intended meaning
      (@{thm LIMSEQ_def lim_sequentially}).
      The sources additionally specify \<^term>\<open>T\<^sub>U n = n * log 2 n\<close>.\<close>
    and T_dominates_t: "(\<lambda>n. T\<^sub>U (t n) / T n) \<longlonglongrightarrow> 0"
  \<comment> \<open>Additionally, \<open>T n\<close> is assumed not to be zero since in Isabelle,
      \<open>x / 0 = 0\<close> holds over the reals (@{thm division_ring_divide_zero}).
      Thus, the above assumption would trivially hold for \<open>T(n) = 0\<close>.\<close>
    and T_gt_n: "\<And>n. T n > n"
    and t_gt_n: "\<And>n. t n > n"
    and t_linear_factor: "\<And>n. t (2 * n) \<le> c\<^sub>t * t n"
    and t_superlinear: "superlinear t" (* Seems to be necessary *)

  \<comment> \<open>The following assumption is not found in @{cite rassOwf2017} or the primary source @{cite hopcroftAutomata1979},
    but is taken from the AAU lecture slides of \<^emph>\<open>Algorithms and Complexity Theory\<close>.
    \<^footnote>\<open>TODO properly cite this\<close>
    It patches a hole that allows one to prove \<^const>\<open>False\<close> from the Time Hierarchy Theorem below
    (\<open>time_hierarchy\<close>).
    This is demonstrated in \<^file>\<open>examples/THT_inconsistencies_MWE.thy\<close>.\<close>
begin

lemma c_gt_0: "c\<^sub>t > 0"
  using t_gt_n [of 0] t_linear_factor [of 0] by auto

lemma t_min: "\<forall>\<^sub>\<infinity> n. n \<le> t n"
  apply standard
  apply (rule exI [where x=0])
  using t_gt_n by (auto dest: less_imp_le_nat)

lemma tcomp_t [simp]: "tcomp t = t"
  using t_gt_n by (metis Suc_eq_plus1 less_eq_Suc_le tcomp_nat_id)

lemma tcomp_T [simp]: "tcomp T = T"
  using T_gt_n by (metis Suc_eq_plus1 less_eq_Suc_le tcomp_nat_id)

lemma t_not_0: "t n \<noteq> 0"
  using t_gt_n [of n] by simp

lemma T_not_0: "T n \<noteq> 0"
  using T_gt_n [of n] by simp

lemma T_ge_t_log_t_ae:
  fixes c :: real
  assumes "c \<ge> 0"
  shows "\<forall>\<^sub>\<infinity>n. c * T\<^sub>U (t n) < T n"
proof -
  from T_not_0 and T_dominates_t have "\<forall>\<^sub>\<infinity>n. c * \<bar>real (T\<^sub>U (t n))\<bar> < \<bar>real (T n)\<bar>"
    by (elim dominates_ae) simp
  then show "?thesis" by simp
qed

lemma T_gt_t_ae: "\<forall>\<^sub>\<infinity>n. T n > t n"
proof -
  from T_ge_t_log_t_ae[of 1] have "\<forall>\<^sub>\<infinity>n. T\<^sub>U (t n) < T n" by simp
  then show "\<forall>\<^sub>\<infinity>n. t n < T n"
  proof ae_nat_elim
    fix n
    have "t n \<le> T\<^sub>U (t n)" by (fact overhead_min)
    also assume "T\<^sub>U (t n) < T n"
    finally show "t n < T n" .
  qed
qed

lemma T_superlinear: "superlinear T"
  using T_gt_t_ae t_superlinear unfolding superlinear_def
proof auto
  fix C :: nat
  assume a1: "\<forall>\<^sub>\<infinity>n. t n < T n" and a2: "\<forall>C. \<forall>\<^sub>\<infinity>n. C * n \<le> t n"
  obtain n\<^sub>0 :: nat where n\<^sub>0_def: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> t n < T n" using a1 by auto
  obtain n\<^sub>0' :: nat where n\<^sub>0'_def: "\<And>n. n \<ge> n\<^sub>0' \<Longrightarrow> C * n \<le> t n" using a2 by blast
  have "\<And>n. n \<ge> max n\<^sub>0 n\<^sub>0' \<Longrightarrow> C * n \<le> T n" using n\<^sub>0_def n\<^sub>0'_def
    by (metis max.boundedE order_le_less_trans order_less_imp_le)
  thus "\<forall>\<^sub>\<infinity>n. C * n \<le> T n" by blast
qed

lemma DTIME_t_subset_DTIME_T: "DTIME t \<subseteq> DTIME T"
proof
  fix L :: "'a lang"
  assume a1: "L \<in> DTIME t"
  obtain n\<^sub>0 :: nat where n\<^sub>0_least: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> T n \<ge> t n"
    using T_dominates_t by (metis (no_types, lifting) Alm_all_natD T_gt_t_ae order_less_imp_le)
  note in_dtimeE' [OF a1]
  then obtain M :: "(nat, 'a) TM_decider" where M_syms: "alphabet L \<subseteq> TM.TM.symbols M" and
      M_dec: "TM_decider.decides M L" and TM_tb: "TM.time_bounded M t" by blast
  have 1: "length w \<ge> n\<^sub>0 \<Longrightarrow> TM.time_bounded_word M T w" for w :: "'a list"
    apply (rule TM.time_bounded_word_mono)
     apply (rule TM_tb [THEN spec])
    using n\<^sub>0_least by blast
  have 2: "\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. TM_decider.decides_word M L w \<and> TM.time_bounded_word M T w"
    apply (rule ae_word_lengthI)
    using M_syms apply (metis M_syms finite_subset TM.symbol_axioms(1))
    apply (frule 1)
    apply auto
    using M_dec by simp
  note 3 = conjI [OF M_syms 2]
  note DTIME_ae_tcomp [OF exI, OF 3, simplified]
  thus "L \<in> DTIME T" .
qed

lemma DTIME_TUt_subset_DTIME_T: "DTIME (\<lambda>n. T\<^sub>U (t n)) \<subseteq> DTIME T"
proof
  fix L :: "'a lang"
  assume a1: "L \<in> DTIME (\<lambda>n. T\<^sub>U (t n))"
  obtain n\<^sub>0 :: nat where n\<^sub>0_least: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> T n \<ge> T\<^sub>U (t n)"
    using T_ge_t_log_t_ae [of 1, simplified] by fastforce
  note in_dtimeE' [OF a1]
  then obtain M :: "(nat, 'a) TM_decider" where M_syms: "alphabet L \<subseteq> TM.TM.symbols M" and
      M_dec: "TM_decider.decides M L" and TM_tb: "TM.time_bounded M (\<lambda>n. T\<^sub>U (t n))" by blast
  have 1: "length w \<ge> n\<^sub>0 \<Longrightarrow> TM.time_bounded_word M T w" for w :: "'a list"
    apply (rule TM.time_bounded_word_mono)
     apply (rule TM_tb [THEN spec])
    using n\<^sub>0_least by blast
  have 2: "\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. TM_decider.decides_word M L w \<and> TM.time_bounded_word M T w"
    apply (rule ae_word_lengthI)
    using M_syms apply (metis M_syms finite_subset TM.symbol_axioms(1))
    apply (frule 1)
    apply auto
    using M_dec by simp
  note 3 = conjI [OF M_syms 2]
  note DTIME_ae_tcomp [OF exI, OF 3, simplified]
  thus "L \<in> DTIME T" .
qed

text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  ``The `diagonal-language' \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>L\<^sub>D := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.''
  @{cite rassOwf2017}\<close>

(*definition L\<^sub>D :: "bool lang"
  where "L\<^sub>D \<equiv> Lang UNIV (\<lambda>w. let M\<^sub>w = dec_TM_pad w in
                  TM_decider.rejects M\<^sub>w w \<and> TM.time_bounded_word M\<^sub>w T w)"*)

definition L\<^sub>D :: "bool list lang"
  where "L\<^sub>D \<equiv> Lang {w. length w = 2} (\<lambda>w. let M\<^sub>w = dec_TM_pad' w in
                  TM_decider.rejects M\<^sub>w w \<and> TM.time_bounded_word M\<^sub>w t w)"

lemma LD_T: "L\<^sub>D \<in> DTIME(T)"
proof -
  \<comment> \<open>\<open>M\<close> is a modified universal TM that executes two TMs in parallel upon an input word \<open>w\<close>.
    \<open>M\<^sub>w\<close> is the input word \<open>w\<close> treated as a TM (\<open>M\<^sub>w \<equiv> TM_decode_pad w\<close>).
    \<open>M\<^sub>T\<close> is a "stopwatch", that halts after exactly \<open>tcomp\<^sub>w T w\<close> steps.
    Its existence is assured by the assumption @{thm fully_tconstr_T}.
    Both machines are simulated with input word \<open>w\<close>.

    Once either of these simulated TM halts, \<open>M\<close> halts as well.
    If \<open>M\<^sub>T\<close> halts before \<open>M\<^sub>w\<close>, \<open>M\<close> rejects \<open>w\<close>.
    If \<open>M\<^sub>w\<close> halts first, \<open>M\<close> inverts the output of \<open>M\<^sub>w\<close>:
    If \<open>M\<^sub>w\<close> accepts, then \<open>M\<close> rejects \<open>w\<close>. If \<open>M\<^sub>w\<close> rejects, then \<open>M\<close> accepts \<open>w\<close>.
    Thus \<open>M\<close> accepts \<open>w\<close>, iff \<open>M\<^sub>w\<close> rejects \<open>w\<close> in time \<open>tcomp\<^sub>w t w\<close>.\<close>

  define L\<^sub>D'_P where "L\<^sub>D'_P \<equiv> \<lambda>w. let M\<^sub>w = dec_TM_pad' w in
    TM_decider.rejects M\<^sub>w w \<and> TM.time_bounded_word M\<^sub>w t w"
  then have L\<^sub>D[simp]: "L\<^sub>D = Lang {w. length w = 2} L\<^sub>D'_P" unfolding L\<^sub>D_def by simp

  obtain M\<^sub>T :: "(nat, bool list, unit) TM" where M\<^sub>T_time: "\<And>w. TM.time M\<^sub>T w = T (length w)"
    using fully_tconstr_T [THEN typed_fully_time_constr_natI] unfolding typed_fully_time_constr_def by blast

  obtain s :: "bool list" where s_syms: "s \<in> TM.symbols M\<^sub>T" by fastforce

  obtain M_repl :: "(nat, bool list, unit) TM" where
    M_repl_characteristic: "TM.TM.symbols M_repl = ({w. length w = 2} \<union> TM.symbols M\<^sub>T) \<and>
        TM.TM.tape_count M_repl = (Suc (TM.tape_count M\<^sub>T + TM.tape_count M\<^sub>U)) \<and>
        (\<forall>w\<in>({w. length w = 2} \<union> TM.symbols M\<^sub>T)*.
            (\<forall>n\<in>{1, Suc (TM.tape_count M\<^sub>U)}. tapes (TM.compute M_repl w) ! n = TM_abbrevs.input_tape w) \<and>
            (\<forall>n\<in>{1..TM.tape_count M\<^sub>T + TM.tape_count M\<^sub>U} - {1, Suc (TM.tape_count M\<^sub>U)}.
            tapes (TM.compute M_repl w) ! n = Tape [] None []) \<and>
            TM.time_bounded_word M_repl (\<lambda>n. 2 * n + 1) w)"
    apply (rule replicate_input_on_tapes [of "{w. length w = 2} \<union> TM.symbols M\<^sub>T" "{1, Suc (TM.tape_count M\<^sub>U)}"
        "Suc (TM.tape_count M\<^sub>T + TM.tape_count M\<^sub>U)", unfolded diff_Suc_1, THEN exE])
        apply auto
    using finite_bin_len_eq apply presburger
     apply (metis One_nat_def TM.at_least_one_tape le_add1 linorder_not_less not0_implies_Suc
        plus_1_eq_Suc)
    by (metis One_nat_def TM.at_least_one_tape')
  have M_repl_syms: "TM.TM.symbols M_repl = ({w. length w = 2} \<union> TM.symbols M\<^sub>T)"
    using M_repl_characteristic [THEN conjunct1] .
  have M_repl_tc: "TM.TM.tape_count M_repl = (Suc (TM.tape_count M\<^sub>T + TM.tape_count M\<^sub>U))"
    using M_repl_characteristic [THEN conjunct2, THEN conjunct1] .
  have M_repl_its: "\<And>w n. set w \<subseteq> {w. length w = 2} \<union> TM.symbols M\<^sub>T \<Longrightarrow> n = 1 \<or> n = Suc (TM.tape_count M\<^sub>U) \<Longrightarrow>
                    tapes (TM.compute M_repl w) ! n = TM_abbrevs.input_tape w"
    using M_repl_characteristic [THEN conjunct2, THEN conjunct2] by auto
  have M_repl_ots: "\<And>w n. set w \<subseteq> {w. length w = 2} \<union> TM.symbols M\<^sub>T \<Longrightarrow> n > 1 \<Longrightarrow>
                    n \<le> TM.tape_count M\<^sub>T + TM.tape_count M\<^sub>U \<Longrightarrow> n \<noteq> Suc (TM.tape_count M\<^sub>U) \<Longrightarrow>
                    tapes (TM.compute M_repl w) ! n = Tape [] None []"
    using M_repl_characteristic [THEN conjunct2, THEN conjunct2] by auto
  have M_repl_tb: "\<And>w. set w \<subseteq> {w. length w = 2} \<union> TM.symbols M\<^sub>T \<Longrightarrow>
                   TM.time_bounded_word M_repl (\<lambda>n. 2 * n + 1) w"
    using M_repl_characteristic [THEN conjunct2, THEN conjunct2] by auto
  obtain M_map :: "(nat, bool list, unit) TM" where
    "\<forall>w\<in>(TM.symbols M_map)*. TM.computes_word M_map w (map (\<lambda>_. s) w)" and
    "TM.time_bounded M_map (\<lambda>n. 2 * n + 2)" sorry (* Easy to do: Case distinction on whether or not
      s \<in> {w. length w = 2} and then use typed_comp_in_time_words_tb and map_computable in both cases. *)
  obtain M :: "(nat + nat + ('q \<times> nat), bool list) TM_decider" where
    "{w. length w = 2} \<subseteq> TM.symbols M" and "TM.time_bounded M (\<lambda>n. T n + 4 * n + 3)"
    and *: "\<And>w. if L\<^sub>D'_P w then TM_decider.accepts M w else TM_decider.rejects M w"
  proof (* Probably "easily" doable; just do M_repl first, then M_map, then execute M\<^sub>T and M\<^sub>U in parallel *)
    define M :: "(nat + nat + ('q \<times> nat), bool list, bool) TM_record" where
      "M \<equiv> undefined"
    show "{w. length w = 2} \<subseteq> TM.TM.symbols (Abs_TM M)" sorry
    show "TM.time_bounded (Abs_TM M) (\<lambda>n. T n + 4 * n + 3)" sorry
    fix w :: "bool list list"
    show "if L\<^sub>D'_P w then TM_decider.accepts (Abs_TM M) w else TM_decider.rejects (Abs_TM M) w"
      unfolding L\<^sub>D'_P_def Let_def apply auto sorry
  qed
  then have "TM_decider.decides M L\<^sub>D" unfolding TM_decider.decides_altdef4 by simp
  have DTIME_T_plus: "L\<^sub>D \<in> DTIME (\<lambda>n. T n + 4 * n + 3)"
    apply (rule typed_DTIME_impl_DTIME [where 'q="nat + nat + ('q \<times> nat)"])
    using \<open>TM.time_bounded M (\<lambda>n. T n + 4 * n + 3)\<close> \<open>TM_decider.decides M L\<^sub>D\<close> by blast
  have T_plus_superlinear: "superlinear (\<lambda>n. T n + 4 * n + 3)"
    apply (rule superlinear_ae_mono [of T])
     apply (rule T_superlinear)
    by simp
  have tcomp_remove: "tcomp (\<lambda>n. (real (T n) + 4 * real n + 3) / 2) n \<le>
                      (T n + 4 * n + 4) div 2" for n :: nat
    unfolding tcomp_def by auto
  note L\<^sub>D_speed_up = DTIME_speed_up [OF DTIME_T_plus T_plus_superlinear, of "0.5", simplified, THEN in_dtime_mono,
      OF tcomp_remove, folded L\<^sub>D]
  note T_superlinear [unfolded superlinear_altdef_nat, THEN spec, of 8, unfolded Alm_all_nat_altdef]
  then obtain n\<^sub>0 :: nat where n\<^sub>0_min: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> 8 * n \<le> T n" by blast
  have almall_le: "\<forall>\<^sub>\<infinity>n. (T n + 4 * n + 4) div 2 \<le> T n"
  proof (rule Alm_all_natI')
    fix n :: nat
    assume a1: "Suc n\<^sub>0 \<le> n"
    have 1: "8 * n \<le> T n"
      apply (rule n\<^sub>0_min)
      using a1 by simp
    have 2: "4 * n + 4 \<le> 8 * n" using a1 by auto
    show "(T n + 4 * n + 4) div 2 \<le> T n" using 1 2 by linarith
  qed
  show "L\<^sub>D \<in> DTIME T"
    apply (rule DTIME_mono_ae [where T=T, simplified])
     apply (rule L\<^sub>D_speed_up)
    by fact
qed

lemma LD_t: "L\<^sub>D \<notin> DTIME(t)"
proof -
  have "L \<noteq> L\<^sub>D" if "L \<in> DTIME(t)" for L
  proof (cases "alphabet L = alphabet L\<^sub>D")
    case True
    from \<open>L \<in> DTIME t\<close> obtain M\<^sub>w :: "(nat, bool list) TM_decider"
      where "TM_decider.decides M\<^sub>w L" and "TM.time_bounded M\<^sub>w t" and
            "alphabet L \<subseteq> TM.symbols M\<^sub>w" ..
    interpret TM_decider M\<^sub>w .

    define w' :: "bool list list" where "w' = enc_TM M\<^sub>w"

    let ?n = "length (enc_TM M\<^sub>w) + 2"
    obtain l where "T l \<ge> t l" and "nat_log_ceil 2 l \<ge> ?n"
    proof -
      obtain l\<^sub>1 :: nat where l1: "l \<ge> l\<^sub>1 \<Longrightarrow> T l > t l" for l using T_gt_t_ae by blast
      obtain l\<^sub>2 :: nat where l2: "l \<ge> l\<^sub>2 \<Longrightarrow> nat_log_ceil 2 l \<ge> ?n" for l
      proof
        fix l :: nat
        assume "l \<ge> 2^?n"
        have "?n > 0" by simp
        then have "?n = nat_log_ceil 2 (2^?n)" by (rule log2.ceil_exp[symmetric])
        also have "... \<le> nat_log_ceil 2 l" using log2.ceil_mono \<open>l \<ge> 2^?n\<close> ..
        finally show "nat_log_ceil 2 l \<ge> ?n" .
      qed

      let ?l = "max l\<^sub>1 l\<^sub>2"
      have "T ?l \<ge> t ?l" by (rule less_imp_le, rule l1) force
      moreover have "nat_log_ceil 2 ?l \<ge> ?n" by (rule l2) force
      ultimately show ?thesis by (intro that) fast+
    qed

    from \<open>nat_log_ceil 2 l \<ge> ?n\<close> obtain w
      where [simp]: "length w = l" and dec_w[simp]: "dec_TM_pad' w = canonical_TM M\<^sub>w" and
        w_wf: "bin'_wf w"
      by (rule embed_TM_in_len')

    have "w \<in>\<^sub>L L \<longleftrightarrow> w \<notin>\<^sub>L L\<^sub>D"
      apply standard
       apply (metis (no_types, lifting) L\<^sub>D_def TM_decider.decides_def
          \<open>alphabet L \<subseteq> \<Sigma> \<and> (\<forall>w\<in>(alphabet L)*. decides_word L w)\<close>
          canonical_TM_rejects dec_w lists_member member_langE member_lang_iff'
          order_trans)
    proof
      assume a1: "w \<notin> words L\<^sub>D"
      show "w \<in> (alphabet L)*" using True w_wf by (simp add: L\<^sub>D_def set_all_length_2_wf)
      with \<open>decides L\<close> show "gen_pred L w"
        using a1 unfolding L\<^sub>D_def apply auto
         apply (metis bin'_wf_def w_wf)
        apply (drule bspec [where x=w])
        apply auto
        apply (erule notE)
        using \<open>TM.time_bounded M\<^sub>w t\<close> \<open>length w = l\<close> by blast
      qed
      thus "L \<noteq> L\<^sub>D" by auto
    next
      case False
      thus "L \<noteq> L\<^sub>D" by auto
    qed
  then show "L\<^sub>D \<notin> DTIME t" by blast
qed

theorem time_hierarchy: "L\<^sub>D \<in> DTIME(T) - DTIME(t)" using LD_T and LD_t ..

theorem time_hierarchy': "(DTIME(t)::bool list lang set) \<subset> DTIME(T)"
proof
  show "(DTIME(t)::bool list lang set) \<subseteq> DTIME T" by (rule DTIME_t_subset_DTIME_T)
  show "(DTIME(t)::bool list lang set) \<noteq> DTIME T"
  proof
    assume a1: "(DTIME(t)::bool list lang set) = DTIME T"
    show False using time_hierarchy [unfolded a1] by simp
  qed
qed

end \<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


subsection\<open>The Intermediate Language \<open>L\<^sub>D'\<close>\<close>

subsubsection\<open>Encoding\<close>

text\<open>Decode a pair of \<open>(l, x) \<in> \<nat> \<times> {0,1}*\<close> from its encoded form \<open>w \<in> {0,1}*\<close>.

  The encoding defined by this should have \<open>l\<close> encoded in the upper (more significant) bits of \<open>l\<parallel>x\<close>.

  \<open>w\<close> is related to \<open>(l, x)\<close> through the regular expression \<open>1\<^sup>l0x{0,1}\<^sup>k\<close>,
  where \<^term>\<open>k = suffix_len w\<close>.
  If \<open>w\<close> does not match the expression, default values \<open>l = 0, x = []\<close> are assigned.

  Construction:
  To ensure the required property for Lemma 4.6@{cite rassOwf2017}, the lower half of \<open>w\<close>
  (the \<open>k\<close> least-significant-bits) is dropped.
  Then, \<open>l\<close> is the number of leading \<open>1\<close>s.
  Remove all leading \<open>1\<close>s and one \<open>0\<close> to retain \<open>x\<close>.\<close>

definition strip_sq_pad :: "bool list list \<Rightarrow> bool list list"
  where "strip_sq_pad w \<equiv> take (length w - suffix'_len w) w"
definition decode_pair_l :: "bool list list \<Rightarrow> nat"
  where "decode_pair_l w = length (takeWhile (\<lambda>x. x = [True, False]) (strip_sq_pad w))"
definition decode_pair_x :: "bool list list \<Rightarrow> bool list list"
  where "decode_pair_x w = tl (dropWhile (\<lambda>x. x = [True, False]) (strip_sq_pad w))"
abbreviation decode_pair :: "bool list list \<Rightarrow> nat \<times> bool list list"
  where "decode_pair w \<equiv> (decode_pair_l w, decode_pair_x w)"

definition rev_suffix_len :: "bool list list \<Rightarrow> nat"
  where "rev_suffix_len w = length w + 6"
definition encode_pair :: "nat \<Rightarrow> bool list list \<Rightarrow> bool list list"
  where "encode_pair l x = (let w' = [True, False] \<up> l @ [[False, False]] @ x in
            w' @ [False, False] \<up> (rev_suffix_len w') )"

lemma length_enc_pair: "length (encode_pair l x) = (l + length x) * 2 + 8"
  unfolding encode_pair_def rev_suffix_len_def by simp

lemma strip_sq_pad_Cons_ge: "length (strip_sq_pad (x#xs)) \<ge> length (strip_sq_pad xs)"
  unfolding strip_sq_pad_def suffix'_len_def by simp

lemma strip_sq_pad_Cons_le:
  "length (strip_sq_pad (x#xs)) \<le> Suc (length (strip_sq_pad xs))"
  unfolding strip_sq_pad_def suffix'_len_def by simp

lemma strip_sq_pad_is_prefix: "prefix (strip_sq_pad xs) xs"
  unfolding strip_sq_pad_def by (rule take_is_prefix)

lemma strip_sq_pad_subset: "set (strip_sq_pad xs) \<subseteq> set xs"
  using strip_sq_pad_is_prefix by (simp add: set_mono_prefix)

lemma strip_sq_pad_Nil [simp]: "strip_sq_pad [] = []"
  unfolding strip_sq_pad_def by simp

lemma encode_pair_altdef:
  "encode_pair l x = [True, False] \<up> l @ [[False, False]] @ x @ [False, False] \<up> (length x + l + 7)"
  unfolding encode_pair_def rev_suffix_len_def Let_def by simp

lemma strip_sq_pad_pair:
  fixes l x
  defines w: "w \<equiv> encode_pair l x"
    and w': "w' \<equiv> [True, False] \<up> l @ [[False, False]] @ x"
  shows "strip_sq_pad w = w'"
proof -
  let ?lw = "length w" and ?lw' = "length w'"
  have lw: "?lw = 2 * ?lw' + 6" unfolding w w' encode_pair_altdef by simp
  have lwh: "3 + ?lw div 2 = rev_suffix_len w'" unfolding lw rev_suffix_len_def by simp
  show "strip_sq_pad w = w'" unfolding strip_sq_pad_def suffix'_len_def lwh
    unfolding w encode_pair_def Let_def w'[symmetric] by simp
qed

lemma decode_encode_pair:
  fixes l x
  defines w: "w \<equiv> encode_pair l x"
  shows "decode_pair w = (l, x)"
proof (unfold prod.inject, intro conjI)
  have rw: "(strip_sq_pad w) = [True, False] \<up> l @ [False, False] # x"
    unfolding w strip_sq_pad_pair by force
  show "decode_pair_l w = l" unfolding decode_pair_l_def rw
    by (simp add: takeWhile_tail)
  show "decode_pair_x w = x" unfolding decode_pair_x_def rw
    by (simp add: dropWhile_append3)
qed


lemma pair_adj_sq_eq:
  fixes w
  defines w': "w' \<equiv> adj_sq\<^sub>w' w"
  assumes len: "length w \<ge> 7" and "set w \<subseteq> {w. length w = 2}" and
               "starts_with [True, False] w"
  shows "decode_pair w' = decode_pair w"
proof -
  let ?sl = "suffix'_len w" and ?lw = "length w" and ?lw' = "length w'"
  from len have sh: "shared_MSBs' (?lw - ?sl) w w'" unfolding w'
    using assms(3, 4) by (rule adj_sq'_sh_pfx_half)
  from sh have l_eq: "?lw' = ?lw" ..

  from len have "?sl \<le> length w" by (rule suffix'_min_len)
  then have "?lw - (?lw - ?sl) = ?sl" by (rule diff_diff_cancel)
  from sh have "take (?lw' - ?sl) w' = take (?lw - ?sl) w" unfolding l_eq by auto
  then have sq_pad_eq: "strip_sq_pad w' = strip_sq_pad w"
    unfolding strip_sq_pad_def suffix'_len_def l_eq
    using sh suffix'_len_def by auto
  show "decode_pair w' = decode_pair w"
    unfolding decode_pair_x_def decode_pair_l_def sq_pad_eq ..
qed

subsubsection\<open>Definition\<close>

text\<open>From the proof of Lemma 4.6@{cite rassOwf2017}:

   ``To retain \<open>L\<^sub>D \<inter> SQ \<in> DTIME(T)\<close>, we must choose \<open>T\<close> so large that the decision
    \<open>w \<in> SQ\<close> is possible within the time limit incurred by \<open>T\<close>, so we add \<open>t(n) \<ge> n\<^sup>3\<close>
    to our hypothesis besides Assumption 4.4 (note that we do not need an optimal
    complexity bound here).''\<close>

locale lemma4_6 = TM_Encoding' + timed_UTM +
  fixes T t l\<^sub>R :: "nat \<Rightarrow> nat" and c\<^sub>t :: real
  defines "l\<^sub>R \<equiv> \<lambda>n. 4 * n + 11"
  assumes T_dominates_t': "(\<lambda>n. T\<^sub>U ((t \<circ> l\<^sub>R) n) / T n) \<longlonglongrightarrow> 0"
    and t_mono: "mono t"
    and t_cubic: "\<forall>\<^sub>\<infinity>n. t(n) \<ge> n^3"
    and tht_assms': "tht_assms enc_TM is_valid_enc_TM dec_TM enc\<^sub>U is_valid_enc\<^sub>U dec\<^sub>U M\<^sub>U T\<^sub>U T t c\<^sub>t"
    and t_time_for_reduce_LD_LD': "\<And>n. t n \<ge> 4 * n + 8"
begin

lemma t'_ge_t: "t n \<le> (t \<circ> l\<^sub>R) n" unfolding l\<^sub>R_def comp_def
  using t_mono by (elim monoD) linarith

lemma t_n_ge_n_cube: obtains n :: nat where "\<And>n'. n' \<ge> n \<Longrightarrow> t n' \<ge> n'^3"
  using t_cubic by auto


(* TODO document this approach *)
sublocale tht: tht_assms enc_TM is_valid_enc_TM dec_TM enc\<^sub>U is_valid_enc\<^sub>U dec\<^sub>U M\<^sub>U T\<^sub>U T "t \<circ> l\<^sub>R" c\<^sub>t
  using tht_assms' unfolding tht_assms_def tht_assms_axioms_def
proof (elim conj_forward)
  show "(\<lambda>n. T\<^sub>U ((t \<circ> l\<^sub>R) n) / T n) \<longlonglongrightarrow> 0" by (fact T_dominates_t')
next
  show "\<forall>n. n < t n \<Longrightarrow> \<forall>n. n < (t \<circ> l\<^sub>R) n"
    using order_less_le_trans t'_ge_t by blast
next
  show "\<forall>n. real (t (2 * n)) \<le> c\<^sub>t * real (t n) \<Longrightarrow>
        \<forall>n. real ((t \<circ> l\<^sub>R) (2 * n)) \<le> c\<^sub>t * real ((t \<circ> l\<^sub>R) n)"
    unfolding l\<^sub>R_def
  proof auto
    fix n :: nat
    assume a1: "\<forall>n. real (t (2 * n)) \<le> c\<^sub>t * real (t n)"
    hence 1: "real (t (8 * n + 12)) \<le> c\<^sub>t * real (t (4 * n + 6))"
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) distrib_left_numeral
          numeral_Bit0_eq_double)
    have 2: "real (t (8 * n + 11)) \<le> real (t (8 * n + 12))"
      using t_mono by (simp add: monoD)
    have "c\<^sub>t > 0" using tht_assms' by (rule tht_assms.c_gt_0)
    hence 3: "c\<^sub>t * real (t (4 * n + 6)) \<le> c\<^sub>t * real (t (4 * n + 11))" using t_mono
      by (metis monoE mult_le_cancel_left_pos nat_add_left_cancel_le numeral_le_iff
          of_nat_mono semiring_norm(68) semiring_norm(72) semiring_norm(73))
    show "real (t (8 * n + 11)) \<le> c\<^sub>t * real (t (4 * n + 11))"
      using 1 2 3 by simp
  qed
next
  show "superlinear t \<Longrightarrow> superlinear (t \<circ> l\<^sub>R)"
    apply (rule funcomp_superlinearI)
    unfolding l\<^sub>R_def apply simp
     apply assumption
    by (rule t_mono)
qed

lemma tcomp_t [simp]: "tcomp t = t"
  using tht_assms' tht_assms.tcomp_t by force

text\<open>Note: this is not intended to replace \<^const>\<open>tht.L\<^sub>D\<close>.
  Instead, the further proof uses the similarity of \<open>L\<^sub>D\<close> and \<open>L\<^sub>D'\<close>
  to prove properties of \<open>L\<^sub>D'\<close> via reduction to \<open>L\<^sub>D\<close>.

  Construction: Given a word \<open>w\<close>.
  Split the word \<open>w\<close> into \<^term>\<open>(l::nat, x::bool list)\<close> using \<^const>\<open>decode_pair\<close>.
  Define \<open>v\<close> as the \<open>l\<close> most-significant-bits of \<open>x\<close>.
  Remove the arbitrary-length \<open>1\<^sup>+0\<close>-prefix from \<open>v\<close> to retain the pure encoding of \<open>M\<^sub>v\<close>.
  If \<open>M\<^sub>v\<close> rejects \<open>v\<close> within \<open>t(len(x))\<close> steps, \<open>w \<in> L\<^sub>D'\<close> holds.

  Note that in this version, using \<^const>\<open>TM.time_bounded_word\<close> is not possible,
  as the word that determines the time bound (\<open>x\<close>) differs from the input word (\<open>v\<close>).
  (see \<open>TM.time_bounded_word_def\<close>)\<close>

definition L\<^sub>D' :: "bool list lang"
  where "L\<^sub>D' \<equiv> Lang {s. length s = 2} (\<lambda>w.
      let (l, x) = decode_pair w;
          v = take l x;
          M\<^sub>v = dec_TM_pad' v in
      TM_decider.rejects M\<^sub>v v \<and> TM.is_final M\<^sub>v (TM.run M\<^sub>v (t (l\<^sub>R (length x))) v)
    )"

lemma LD'_starts_with_TF: "w \<in>\<^sub>L L\<^sub>D' \<Longrightarrow> starts_with [True, False] w"
proof (unfold L\<^sub>D'_def Let_def, auto, rule ccontr, auto)
  assume a1: "set w \<subseteq> {w. length w = 2}" and
         a2: "TM_decider.rejects (dec_TM_pad' (take (decode_pair_l w) (decode_pair_x w)))
              (take (decode_pair_l w) (decode_pair_x w))" and
         a3: "\<forall>ys. w \<noteq> [True, False] # ys"
  have 1: "\<forall>ys. strip_sq_pad w \<noteq> [True, False] # ys"
    using a3 unfolding strip_sq_pad_def apply auto
    by (meson starts_with_takeD)
  have 2: "decode_pair_l w = 0" using a3 1 unfolding decode_pair_l_def
    by (metis (full_types) hd_Cons_tl length_0_conv takeWhile_eq_Nil_iff)
  note a2 [unfolded 2, simplified]
  thus False
    by (metis TM_decider.rejects_halts alp_Nil' dec_TM_pad'_def enc_TM_not_empty
        exp_pad_Nil' invalid_enc_TM_not_halts)
qed

subsubsection\<open>Preliminaries\<close>

lemmas T_gt_t_ae = tht_assms.T_gt_t_ae[OF tht_assms']

lemma T_cubic: "\<forall>\<^sub>\<infinity>n. T(n) \<ge> n^3" by (ae_nat_elim add: t_cubic T_gt_t_ae) simp

lemma t_superlinear: "superlinear t"
proof -
  have "superlinear (\<lambda>n::nat. n^3)" by (rule superlinear_poly_nat) auto
  then show ?thesis by (elim superlinear_ae_mono, ae_nat_elim add: t_cubic) simp
qed

lemma T_superlinear: "superlinear T" using t_superlinear
  by (elim superlinear_ae_mono, ae_nat_elim add: T_gt_t_ae) simp

lemma T_ge_tcomp_T_ae: "\<forall>\<^sub>\<infinity> n. T n \<ge> tcomp T n"
proof (ae_nat_elim add: T_cubic)
  fix n :: nat
  assume "n \<ge> 2"
  from \<open>n \<ge> 2\<close> have "n^1 < n^3" using power_strict_increasing_iff[of n 1 3] by simp
  then have "n + 1 \<le> n^3" by simp
  also assume "n^3 \<le> T n"
  finally show "tcomp T n \<le> T n" by simp
qed

lemma t_gt_n: "n < t n"
  using tht_assms' tht_assms.t_gt_n by auto

lemma t_linear_factor: "t (2 * n) \<le> c\<^sub>t * t n"
  using tht_assms' tht_assms.t_linear_factor by auto


subsubsection\<open>\<open>L\<^sub>D' \<notin> DTIME(t)\<close> via Reduction from \<open>L\<^sub>D\<close> to \<open>L\<^sub>D'\<close>\<close>

text\<open>Reduce \<open>L\<^sub>D\<close> to \<open>L\<^sub>D'\<close>:
    Given a word \<open>w\<close>, construct its counterpart \<open>w' := 1\<^sup>l0x0\<^sup>l\<^sup>+\<^sup>9\<close>, where \<open>l = length w\<close>.
    Decoding \<open>w'\<close> then yields \<open>(l, w)\<close> which results in the intermediate value \<open>v\<close>
    being equal to \<open>w\<close> in the definition of \<^const>\<open>L\<^sub>D'\<close>.\<close>

definition reduce_LD_LD' :: "bool list list \<Rightarrow> bool list list"
  where "reduce_LD_LD' w \<equiv> encode_pair (length w) w"

(* I'm certain, that this is only feasible with stronger lower-bound assumptions about t.
   t n > n is not enough, it would have to be at least something like t n > 4 * n + 8 (see reduce_LD_LD'_len),
   but actually even a bit more than that. *)
lemma reduce_LD_LD'_computable: "computable_in_time t reduce_LD_LD'"
  unfolding reduce_LD_LD'_def encode_pair_def Let_def rev_suffix_len_def apply simp oops

lemma reduce_LD_LD'_len: "length (reduce_LD_LD' w) = 4 * length w + 8"
  unfolding reduce_LD_LD'_def encode_pair_def rev_suffix_len_def Let_def by auto

lemma bin'_wf_red_LD_LD'_iff [iff]: "bin'_wf (reduce_LD_LD' w) \<longleftrightarrow> bin'_wf w"
  unfolding reduce_LD_LD'_def encode_pair_def Let_def by fastforce

lemma reduce_LD_LD'_correct:
  fixes w
  defines "w' \<equiv> reduce_LD_LD' w"
  shows "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L tht.L\<^sub>D"
proof (cases "set w \<subseteq> {w. length w = 2}")
  assume a1: "set w \<subseteq> {w. length w = 2}"
  let ?M\<^sub>w = "dec_TM_pad' w"
  interpret TM_decider ?M\<^sub>w .

  have *: "(let (l, x) = decode_pair w';
                  v = drop (length x - l) x;
                 M\<^sub>v = dec_TM_pad' v in P M\<^sub>v x v) \<longleftrightarrow> P ?M\<^sub>w w w" for P
    unfolding w'_def reduce_LD_LD'_def decode_encode_pair Let_def prod.case by simp

  have "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> rejects w \<and> time_bounded_word (t \<circ> l\<^sub>R) w"
    unfolding L\<^sub>D'_def member_lang_iff' mem_Collect_eq * TM.time_bounded_word_def
      Let_def apply auto
    using decode_encode_pair reduce_LD_LD'_def w'_def apply fastforce
    using decode_encode_pair reduce_LD_LD'_def w'_def apply fastforce
    using a1 apply (subst (asm) w'_def)
      apply (metis bin'_wf_def bin'_wf_red_LD_LD'_iff set_all_length_2_wf)
    using decode_encode_pair reduce_LD_LD'_def w'_def by auto
  also have "... \<longleftrightarrow> w \<in>\<^sub>L tht.L\<^sub>D" unfolding tht.L\<^sub>D_def Let_def using a1 by simp
  finally show ?thesis .
next
  assume a1: "\<not> set w \<subseteq> {w. length w = 2}"
  show "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L tht.L\<^sub>D" using a1 unfolding L\<^sub>D'_def tht.L\<^sub>D_def Let_def
      w'_def apply auto
    using set_all_length_2_wf by blast
qed

lemma LD'_t: "L\<^sub>D' \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  let ?f\<^sub>R = reduce_LD_LD'

  assume "L\<^sub>D' \<in> DTIME(t)"
  then have "tht.L\<^sub>D \<in> DTIME (tcomp (t \<circ> l\<^sub>R))" apply (subst (2) comp_def)
  proof (rule reduce_DTIME' [where l\<^sub>R=l\<^sub>R])
    have 1: "{s. length s = 2} =
             {[True, True], [True, False], [False, True], [False, False]}"
      by auto (metis (full_types) length_2_ex_iff)
    show "finite {s::bool list. length s = 2}" unfolding 1 by simp
    show "alphabet L\<^sub>D' \<subseteq> {s. length s = 2}" unfolding L\<^sub>D'_def by simp
    show "alphabet tht.L\<^sub>D \<subseteq> {s. length s = 2}" by (simp add: tht.L\<^sub>D_def)
    show "\<forall>\<^sub>\<infinity>w. (\<forall>s\<in>set w. length s = 2) \<longrightarrow>
          (?f\<^sub>R w \<in>\<^sub>L L\<^sub>D') = (w \<in>\<^sub>L tht.L\<^sub>D) \<and> length (?f\<^sub>R w) \<le> l\<^sub>R (length w)"
      apply (intro eventually_conj eventuallyI)
      apply auto
      using reduce_LD_LD'_correct apply fast
      using reduce_LD_LD'_correct apply presburger
      using l\<^sub>R_def reduce_LD_LD'_len by simp

    from t'_ge_t show "\<forall>\<^sub>\<infinity>x. t x \<le> t (l\<^sub>R x)" by simp

    show "superlinear t" by (fact t_superlinear)

    show "computable_in_time t reduce_LD_LD'" sorry \<comment> \<open>Assume that \<^const>\<open>reduce_LD_LD'\<close> can be computed in time \<open>O(n)\<close>.\<close>
  qed
  then have "tht.L\<^sub>D \<in> DTIME (t \<circ> l\<^sub>R)" using tht.tcomp_t by argo
  moreover from tht.LD_t have "tht.L\<^sub>D \<notin> DTIME(t \<circ> l\<^sub>R)" .
  ultimately show False by contradiction
qed


subsubsection\<open>\<open>L\<^sub>D' \<in> DTIME(T)\<close> analogous to the THT\<close>

lemma reduce_LD_LD'_left_inv: "decode_pair_x (reduce_LD_LD' w) = w"
  unfolding reduce_LD_LD'_def using decode_encode_pair by simp

lemma reduce_LD_LD'_inj: "inj reduce_LD_LD'"
  by (metis reduce_LD_LD'_left_inv injI)

lemma LD'_T: "L\<^sub>D' \<in> DTIME(T)"
proof -
  \<comment> \<open>For now this is a carbon copy of the proof of (@{thm tht.LD_T}).

    Ideally, if the TM constructed in the THT is feasible to construct in Isabelle/HOL,
    and its properties can be proven, the ``difficult parts'' could potentially be reused.
    It may suffice to add a pre-processing step for decoding the input word \<open>w\<close> into \<open>x, v\<close>,
    with \<open>v\<close> being the input for the universal TM part, and \<open>x\<close> the input for the stopwatch.

    Note: it seems feasible to construct this adapter and (if this approach works)
    reduce the \<open>sorry\<close> statements in the THT and this proof into one common assumption;
    the existence of the UTM with only \<open>log\<close> time overhead.\<close>

  define LD'_P where "LD'_P \<equiv> \<lambda>w. let (l, x) = decode_pair w;
          v = take l x;
          M\<^sub>v = dec_TM_pad' v in
      TM_decider.rejects M\<^sub>v v \<and> TM.is_final M\<^sub>v (TM.run M\<^sub>v (t (l\<^sub>R (length x))) v)"
  have [simp]: "L\<^sub>D' = Lang {w. length w = 2} LD'_P" unfolding L\<^sub>D'_def LD'_P_def ..

  obtain M :: "(nat, bool list) TM_decider" where "TM.symbols M = {w. length w = 2}"
    and "TM.time_bounded M T"
    and *: "\<And>w. if LD'_P w then TM_decider.accepts M w else TM_decider.rejects M w" sorry (* probably out of scope *)
  from * have "TM_decider.decides M L\<^sub>D'" unfolding TM_decider.decides_altdef4
      \<open>TM.symbols M = {w. length w = 2}\<close> by simp
  with \<open>TM.time_bounded M T\<close> show "L\<^sub>D' \<in> DTIME(T)" by blast
qed


subsection\<open>The Hard Language \<open>L\<^sub>0\<close>\<close>

text\<open>``\<^bold>\<open>Lemma 4.6.\<close> Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.''\<close>

definition L\<^sub>0 :: "bool list lang" where "L\<^sub>0 \<equiv> L\<^sub>D' \<inter>\<^sub>L SQ'"

lemma alphabet_L\<^sub>0 [simp]: "alphabet L\<^sub>0 = {w. length w = 2}"
  unfolding L\<^sub>0_def L\<^sub>D'_def SQ'_def by simp

lemma L\<^sub>D'_adj_sq_iff:
  fixes w
  defines "w' \<equiv> adj_sq\<^sub>w' w"
  assumes len: "length w \<ge> 7" and "set w \<subseteq> {w. length w = 2}" and
          "starts_with [True, False] w"
  shows "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'"
  unfolding L\<^sub>D'_def member_lang_UNIV w'_def len[THEN pair_adj_sq_eq] using assms(3)
  pair_adj_sq_eq [OF len assms(3, 4)] adj_sq'_word'_correct by simp

lemma L\<^sub>D'_L\<^sub>0_adj_sq_iff:
  fixes w
  defines "w' \<equiv> adj_sq\<^sub>w' w"
  assumes len: "length w \<ge> 7" and "set w \<subseteq> {s. length s = 2}" and
          "starts_with [True, False] w"
  shows "w' \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'"
  unfolding L\<^sub>0_def w'_def using assms(3, 4) len[THEN L\<^sub>D'_adj_sq_iff]
    adj_sq'_word'_correct by auto

lemma L0_t: "L\<^sub>0 \<notin> DTIME(t)"
proof
  assume "L\<^sub>0 \<in> DTIME(t)"
  then have "L\<^sub>D' \<in> DTIME (tcomp (\<lambda>x. t (2 * x)))"
  proof (rule reduce_DTIME')
    show "finite {s::bool list. length s = 2}" by (rule finite_bin_len_eq)
    show "alphabet L\<^sub>0 \<subseteq> {s. length s = 2}" by simp
    show "alphabet L\<^sub>D' \<subseteq> {s. length s = 2}" unfolding L\<^sub>D'_def by simp
    have 1: "finite {s::bool list. length s = 2}" by (rule finite_bin_len_eq)
    have 2: "\<exists>n. \<forall>w\<in>{s. length s = 2}*. n \<le> length w \<longrightarrow>
             (adj_sq\<^sub>w' w \<in>\<^sub>L L\<^sub>0) = (w \<in>\<^sub>L L\<^sub>D') \<and> length (adj_sq\<^sub>w' w) \<le> 2 * length w"
    proof (rule exI [where x=12], fold atomize_ball, rule impI, rule conjI)
      fix w :: "bool list list"
      assume a1: "w \<in> {s. length s = 2}*" and a2: "12 \<le> length w"
      have lw: "7 \<le> length w" using a2 by simp
      have "w \<in>\<^sub>L L\<^sub>D' \<Longrightarrow> adj_sq\<^sub>w' w \<in>\<^sub>L L\<^sub>0"
        apply (frule LD'_starts_with_TF)
        apply (drule L\<^sub>D'_L\<^sub>0_adj_sq_iff [OF lw a1 [simplified]])
        by simp
      moreover have "adj_sq\<^sub>w' w \<in>\<^sub>L L\<^sub>0 \<Longrightarrow> w \<in>\<^sub>L L\<^sub>D'"
        apply (rule L\<^sub>D'_L\<^sub>0_adj_sq_iff [OF lw a1 [simplified], THEN iffD1])
         apply (subst (asm) L\<^sub>0_def)
         apply (auto simp del: adj_sq\<^sub>w'_def)
        apply (drule LD'_starts_with_TF)
        apply (auto simp del: adj_sq\<^sub>w'_def)
        apply (rule adj_sq_sTw)
           apply (rule a2)
        using a1 by simp
      ultimately show "adj_sq\<^sub>w' w \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'" by blast
      show "length (adj_sq\<^sub>w' w) \<le> 2 * length w"
        using a1 length_adj_sq_le set_all_length_2_wf by simp
    qed
    show "\<forall>\<^sub>\<infinity>w. (\<forall>s\<in>set w. length s = 2) \<longrightarrow>
          (adj_sq\<^sub>w' w \<in>\<^sub>L L\<^sub>0) = (w \<in>\<^sub>L L\<^sub>D') \<and> length (adj_sq\<^sub>w' w) \<le> 2 * length w"
      apply (rule eventually_mono)
      apply (rule ae_word_length_iff [THEN iffD2, where \<Sigma>1="{s. length s = 2}" and
          P1="(\<lambda>w. (adj_sq\<^sub>w' w \<in>\<^sub>L L\<^sub>0) = (w \<in>\<^sub>L L\<^sub>D') \<and> length (adj_sq\<^sub>w' w) \<le> 2 * length w)",
          OF 1 2])
      by auto

    show "superlinear t" by (fact t_superlinear)

    show "computable_in_time t adj_sq\<^sub>w'" sorry
    \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be computed by a TM in time \<open>n\<^sup>3\<close>.\<close>
    show "\<forall>\<^sub>\<infinity>x. t x \<le> t (2 * x)" using t_mono [THEN monoD] by simp
  qed
  hence "L\<^sub>D' \<in> DTIME (\<lambda>x. t (2 * x))"
  proof
    fix n :: nat
    show "tcomp (\<lambda>x. real (t (2 * x))) n \<le> (\<lambda>x. t (2 * x)) n"
      using t_gt_n [of "2 * n"] by simp
  qed
  hence LD'ct: "L\<^sub>D' \<in> DTIME (\<lambda>n. nat (ceiling (c\<^sub>t * t n)))"
    using tht_assms.t_linear_factor [OF tht_assms']
    by (smt (verit) in_dtime_mono of_nat_le_iff real_nat_ceiling_ge)
  have superlinear: "superlinear (\<lambda>n. nat \<lceil>c\<^sub>t * real (t n)\<rceil>)"
    using t_superlinear superlinear_factor [OF tht.c_gt_0, THEN iffD2,
        THEN superlinear_ae_mono, where f2="(\<lambda>n. of_nat (t n))" and
        g="(\<lambda>n. nat \<lceil>c\<^sub>t * real (t n)\<rceil>)"] apply auto
    using of_nat_ceiling by blast
  have "L\<^sub>D' \<in> DTIME (tcomp t)"
    apply (cases "c\<^sub>t \<ge> 1")
    using DTIME_speed_up
      [OF LD'ct superlinear, of "1 / (2 * c\<^sub>t + 1)"] tht.c_gt_0 apply auto[1]
    apply (drule in_dtime_mono [where T="(tcomp (\<lambda>x. real (t x)))"])
  proof (auto simp add: tcomp_def max_def)
    fix n :: nat
    assume a1: "1 \<le> c\<^sub>t" and a2: "Suc n \<le> nat \<lceil>real_of_int \<lceil>c\<^sub>t * real (t n)\<rceil> / (2 * c\<^sub>t + 1)\<rceil>"
    have "real_of_int \<lceil>c\<^sub>t * real k\<rceil> / (2 * c\<^sub>t + 1) \<le> real k" for k :: nat
    proof (induction k)
      case 0
      then show ?case by simp
    next
      case IH: (Suc k)
      note ceiling_add_le [of c\<^sub>t "c\<^sub>t * real k"]
      hence "real_of_int \<lceil>c\<^sub>t + c\<^sub>t * real k\<rceil> / (2 * c\<^sub>t + 1) \<le>
             real_of_int \<lceil>c\<^sub>t\<rceil> / (2 * c\<^sub>t + 1) + \<lceil>c\<^sub>t * real k\<rceil> / (2 * c\<^sub>t + 1)"
        by (smt (verit) a1 add_divide_distrib divide_right_mono of_int_add of_int_le_iff)
      also have "... \<le> 1 + real_of_int \<lceil>c\<^sub>t * real k\<rceil> / (2 * c\<^sub>t + 1)"
        by (smt (verit) ceiling_correct divide_le_eq_1 tht.c_gt_0)
      finally have "real_of_int \<lceil>c\<^sub>t * real (Suc k)\<rceil> / (2 * c\<^sub>t + 1) \<le>
            1 + real_of_int \<lceil>c\<^sub>t * real k\<rceil> / (2 * c\<^sub>t + 1)" apply simp
        unfolding distrib_left by simp
      thus ?case using IH by simp
    qed
    thus "real_of_int \<lceil>c\<^sub>t * real (t n)\<rceil> / (2 * c\<^sub>t + 1) \<le> real (t n)" .
  next
    show "\<And>n. 1 \<le> c\<^sub>t \<Longrightarrow>
          \<not> Suc n \<le> nat \<lceil>real_of_int \<lceil>c\<^sub>t * real (t n)\<rceil> / (2 * c\<^sub>t + 1)\<rceil> \<Longrightarrow> Suc n \<le> t n"
      using Suc_le_eq tht_assms' tht_assms.t_gt_n by auto
  next
    show "\<not> 1 \<le> c\<^sub>t \<Longrightarrow> L\<^sub>D' \<in> DTIME t"
      apply (insert LD'ct [unfolded tcomp_def max_def])
      apply (drule in_dtime_mono
          [where T="(\<lambda>n. if Suc n \<le> t n then nat \<lceil>real (t (of_nat n))\<rceil> else n + 1)"])
       apply auto
      using less_eq_Suc_le tht_assms' tht_assms.t_gt_n by force+
  qed
  hence "L\<^sub>D' \<in> DTIME t" by (simp only: tht_assms.tcomp_t [OF tht_assms'])
  moreover have "L\<^sub>D' \<notin> DTIME(t)" by (fact LD'_t)
  ultimately show False by contradiction
qed


(* Apparently, we do not need the linear speed-up theorem directly *)
lemma L0_T: "L\<^sub>0 \<in> DTIME(T)"
proof -
  define T' where "T' \<equiv> \<lambda>n. max (T n) (n^3)"
  have [simp]: "(\<lambda>n. max (T n) (tcomp (\<lambda>n. n ^ 3) n)) = (\<lambda>n. max (T n) (n ^ 3))"
    apply standard
    unfolding max_def
  proof auto
    fix n :: nat
    assume a1: "T n \<le> tcomp (\<lambda>n. n ^ 3) n" and a2: "T n \<le> n ^ 3"
    have "tcomp (\<lambda>n. n ^ 3) n > n" using a1 tht.T_gt_n [of n]
      by (metis dual_order.order_iff_strict dual_order.strict_trans1 le_add1
          nat_add_left_cancel_le not_numeral_le_zero numeral_One tcomp_min)
    thus "tcomp (\<lambda>n. n ^ 3) n = n ^ 3" unfolding tcomp_def apply auto
      by (smt (z3) a2 ceiling_of_nat eq_imp_le int_nat_eq le_add_same_cancel1 max.absorb2
          max.bounded_iff nat_int_comparison(1) not_le not_less_eq_eq of_nat_0 of_nat_power
          of_nat_power_le_of_nat_cancel_iff tht.T_gt_n trans_le_add1)
  next
    fix n :: nat
    assume a1: "T n \<le> tcomp (\<lambda>n. n ^ 3) n" and a2: "\<not> T n \<le> n ^ 3"
    thus "tcomp (\<lambda>n. n ^ 3) n = T n" unfolding tcomp_def apply auto
      by (metis ceiling_of_nat le_Suc_eq le_max_iff_disj linorder_linear linorder_not_le
          max.orderE nat_int of_nat_eq_of_nat_power_cancel_iff tht.T_gt_n)
  next
    fix n :: nat
    assume a1: "\<not> T n \<le> tcomp (\<lambda>n. n ^ 3) n" and a2: "T n \<le> n ^ 3"
    thus "T n = n ^ 3" unfolding tcomp_def apply auto
      by (metis ceiling_of_nat max.coboundedI2 nat_int of_nat_power_eq_of_nat_cancel_iff)
  qed
  have "L\<^sub>0 \<in> DTIME(T')" unfolding L\<^sub>0_def T'_def
    using DTIME_int [OF LD'_T SQ'_DTIME] by simp
  then have "L\<^sub>0 \<in> DTIME(tcomp (\<lambda>n. real (T n)))"
  proof (elim DTIME_mono_ae, ae_nat_elim add: T_cubic)
    fix n
    assume "n \<ge> 2" and "n ^ 3 \<le> T n"
    (* We do not need the factor 2 in (2 * T n) *)
    then have "max (T n) (n^3) \<le> T n" by force
    thus "T' n \<le> T n" unfolding T'_def .
  qed
  then have "L\<^sub>0 \<in> DTIME(tcomp T)" by simp
  with T_ge_tcomp_T_ae have "L\<^sub>0 \<in> DTIME(tcomp T)" by (elim DTIME_mono_ae) ae_nat_elim
  thus "L\<^sub>0 \<in> DTIME T" by simp
qed


theorem L0_time_hierarchy: "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" using L0_T L0_t ..

theorem dens_L0: "dens' L\<^sub>0 n \<le> dsqrt n"
proof -
  have "dens' L\<^sub>0 n = dens' (L\<^sub>D' \<inter>\<^sub>L SQ') n" unfolding L\<^sub>0_def ..
  also have "... \<le> dens' SQ' n" by (rule dens'_intersect_le) (fact alphabet_SQ'_subset)
  also have "... = dsqrt n" by (rule dens'_SQ')
  finally show ?thesis .
qed

lemmas lemma4_6 = L0_time_hierarchy dens_L0

end \<comment> \<open>context \<^locale>\<open>lemma4_6\<close>\<close>
                     
locale lemma4_7 = lemma4_6
begin
lemma length_reduce_LD_LD'_greater: "length (reduce_LD_LD' w) > length w"
  unfolding reduce_LD_LD'_def encode_pair_def by simp

(* The time bound is very large, but via the linear speed-up theorem it goes away anyways. *)
lemma dereduction_computable: "computable_in_time (\<lambda>n. 6 * n + 6)
                               (takeWhile (P1::(('a::finite) \<Rightarrow> bool)) \<circ> tl \<circ> dropWhile P2)"
proof -
  have 1: "max_Tf (\<lambda>n. 2 * n + 2) (dropWhile P2) n + (2 * n + 2) \<le> 4 * n + 4" for n :: nat
    apply (rule max_Tf_w [of n "(\<lambda>n. 2 * n + 2)" "dropWhile P2"])
    apply auto
    apply (erule subst)
    by (simp add: length_dropWhile_le)
  note 2 = computable_in_time_compI [OF dropWhile_computable tl_computable, of P2,
      THEN computable_mono, of "\<lambda>n. 4 * n + 4", OF 1]
  have 3: "max_Tf (\<lambda>n. 2 * n + 2) (tl \<circ> dropWhile P2) n + (4 * n + 4) \<le> 6 * n + 6" for n :: nat
    unfolding max_Tf_def apply simp
  proof -
    have "{t. \<exists>w. length w = n \<and> Suc (Suc (2 * (length (dropWhile P2 w) - Suc 0))) = t} \<noteq> {}"
      by (rule max_Tf_not_empty)
    moreover have "\<And>w. length w = n \<Longrightarrow>
                   Suc (Suc (2 * (length (dropWhile P2 w) - Suc 0))) \<le> Suc (Suc (2 * n))"
      apply simp
      by (metis One_nat_def Suc_eq_plus1 le_SucI le_diff_conv length_dropWhile_le)
    hence "\<And>t. \<exists>w. length w = n \<and> Suc (Suc (2 * (length (dropWhile P2 w) - Suc 0))) = t \<Longrightarrow>
           t \<le> Suc (Suc (2 * n))" by blast
    hence "\<And>t. t \<in> {t. \<exists>w. length w = n \<and> Suc (Suc (2 * (length (dropWhile P2 w) - Suc 0))) = t} \<Longrightarrow>
           t \<le> Suc (Suc (2 * n))" by blast
    ultimately show "Max {t. \<exists>w. length w = n \<and> Suc (Suc (2 * (length (dropWhile P2 w) - Suc 0))) = t} \<le>
                     Suc (Suc (2 * n))" by (rule natset_bounded_Max_bounded)
  qed
  note computable_in_time_compI [OF 2 takeWhile_computable, of P1, THEN computable_mono,
      OF 3]
  thus "computable_in_time (\<lambda>n. 6 * n + 6) (takeWhile P1 \<circ> tl \<circ> dropWhile P2)"
    unfolding comp_assoc .
qed

lemma dereduction_correct: "pre \<in> {TT, TF, FF}* \<Longrightarrow> w \<in> {TT, TF}* \<Longrightarrow>
      (takeWhile (\<lambda>s. s \<in> {TT, TF}) \<circ> tl \<circ> dropWhile (\<lambda>s. s \<noteq> FT)) (pre @ [FT] @ w @ [FT] @ suff) = w"
proof simp
  assume a1: "set pre \<subseteq> {TT, TF, FF}" and a2: "set w \<subseteq> {TT, TF}"
  have 1: "dropWhile (\<lambda>s. s \<noteq> FT) (pre @ FT # w @ FT # suff) = FT # w @ FT # suff"
    using a1 by (induction pre) auto
  have 2: "tl (dropWhile (\<lambda>s. s \<noteq> FT) (pre @ FT # w @ FT # suff)) = w @ FT # suff"
    unfolding 1 by simp
  show "takeWhile (\<lambda>s. s = TT \<or> s = TF) (tl (dropWhile (\<lambda>s. s \<noteq> FT) (pre @ FT # w @ FT # suff))) = w"
    unfolding 2 using a2 by (induction w) auto
qed

fun bits_conversion :: "bit2 \<Rightarrow> bool list" where
  "bits_conversion TT = [True, True]" |
  "bits_conversion TF = [True, False]" |
  "bits_conversion FT = [False, True]" |
  "bits_conversion FF = [False, False]"

lemma bits_conversion_bij: "bij_betw bits_conversion UNIV {w. length w = 2}"
  unfolding bij_betw_def apply auto
    apply (rule injI)
    apply (smt (verit, best) bit2.exhaust bits_conversion.simps(1,2,3,4) list.inject)
   apply (metis bit2.exhaust bits_conversion.simps(1,2,3,4) length_2_ex_iff)
  by (metis (full_types) bits_conversion.simps(1,2,3,4) length_2_ex_iff range_eqI)

lemma bits_conversion_inv [simp]:
  shows "(inv bits_conversion) [True, True] = TT" and
        "(inv bits_conversion) [True, False] = TF" and
        "(inv bits_conversion) [False, True] = FT" and
        "(inv bits_conversion) [False, False] = FF"
proof -
  show "inv bits_conversion [True, True] = TT"
    using bits_conversion.simps(1) by (metis bij_betw_def bits_conversion_bij inv_f_eq)
  show "inv bits_conversion [True, False] = TF"
    using bits_conversion.simps(2) by (metis bij_betw_def bits_conversion_bij inv_f_eq)
  show "inv bits_conversion [False, True] = FT"
    using bits_conversion.simps(3) by (metis bij_betw_def bits_conversion_bij inv_f_eq)
  show "inv bits_conversion [False, False] = FF"
    using bits_conversion.simps(4) by (metis bij_betw_def bits_conversion_bij inv_f_eq)
qed

(* Verwende die Aussage, um die TMs zu konstruieren, die immer in der Zeitschranke anhalten und
   die korrekte Funktion berechnen. *)
lemmas test = typed_comp_in_time_sym_type [OF bits_conversion_bij dereduction_computable, THEN exE]

lemma dereduced_decidable: "alphabet L = {[True, False], [True, True]} \<Longrightarrow> L \<in> DTIME t \<Longrightarrow>
                            (Lang {s. length s = 2} (\<lambda>w. ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
                            dropWhile (\<lambda>s. s \<noteq> [False, True])) w) \<notin>\<^sub>L L)) \<in> DTIME (\<lambda>n. min (t n) (T n))"
proof (drule DTIME_compl_helper, erule in_dtimeE', simp_all; erule conjE, unfold compl_alphabet)
  fix M :: "(nat, bool list) TM_decider"
  assume a1: "alphabet L = {[True, False], [True, True]}" and
         a2: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M (-L) w" and
         a3: "\<forall>w. TM.time_bounded_word M t w" and
         a4: "alphabet L \<subseteq> TM.TM.symbols M"
  have *: "[True, False] \<in> TM.symbols M" and **: "[True, True] \<in> TM.symbols M"
    using a4 unfolding a1 by auto
  have f: "map bits_conversion ((takeWhile (\<lambda>s. s = TF \<or> s = TT) \<circ> tl \<circ> dropWhile (\<lambda>s. s \<noteq> FT))
           (map (inv bits_conversion) x)) = (takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
           dropWhile (\<lambda>s. s \<noteq> [False, True])) x" if "bin'_wf x" for x :: "bool list list"
    apply auto
    using that
  proof (induction x rule: bin'_wf_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons2 xs x y)
    note 1 = Cons2(2) [OF Cons2(1)]
    have 2: "set (takeWhile (\<lambda>x. inv bits_conversion x = TF \<or> inv bits_conversion x = TT) xs) \<subseteq> alphabet L"
      unfolding a1 apply auto
    proof -
      fix x :: "bool list"
      assume a6: "x \<in> set (takeWhile (\<lambda>x. inv bits_conversion x = TF \<or> inv bits_conversion x = TT) xs)" and
             a7: "x \<noteq> [True, False]"
      have 1: "x \<in> set xs" using a6 [THEN set_takeWhile_subset [THEN subsetD]] .
      have 2: "x = [True, False] \<or> x = [True, True] \<or> x = [False, False] \<or> x = [False, True]"
        using Cons2(1) [THEN bin'_wfD, OF 1] by blast
      show "x = [True, True]" using a6 a7 2 apply auto
        using set_takeWhileD by fastforce+
    qed
    have 3: "\<And>x. x \<in> set xs \<Longrightarrow> inv bits_conversion x = TF \<or> inv bits_conversion x = TT \<longleftrightarrow> x \<in> alphabet L"
      by (metis (full_types) Cons2.hyps a1 bin'_wfD bit2.simps(10,4,6,8) bits_conversion_inv(1,2,3,4)
          empty_iff insert_iff)
    show ?case apply (cases x)
       apply (cases y)
        apply auto
      using 1 apply fastforce+
      apply (subst map_takeWhile [symmetric])
      apply auto
      apply (subst takeWhile_cong [OF refl 3, of xs])
       apply assumption
      unfolding a1 apply auto
      apply (rule nth_equalityI)
       apply auto
    proof -
      fix i :: nat
      assume a6: "i < length (takeWhile (\<lambda>x. x = [True, False] \<or> x = [True, True]) xs)"
      have "takeWhile (\<lambda>x. x = [True, False] \<or> x = [True, True]) xs ! i = [True, False] \<or>
            takeWhile (\<lambda>x. x = [True, False] \<or> x = [True, True]) xs ! i = [True, True]"
        using a6 nth_mem set_takeWhileD by fastforce
      thus "bits_conversion (inv bits_conversion (takeWhile (\<lambda>x. x = [True, False] \<or> x = [True, True]) xs ! i)) =
            takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) xs ! i" by fastforce
    qed
  next
    show "bin'_wf x" by fact
  qed
  note typed_comp_in_time_sym_type [OF bits_conversion_bij dereduction_computable, of "\<lambda>s. s = TF \<or> s = TT"
      "\<lambda>s. s \<noteq> FT"]
  hence "\<exists>M::(nat, bool list, unit) TM. TM.TM.symbols M = {w. length w = 2} \<and>
         (\<forall>w\<in>{w. length w = 2}*. TM.computes_word M w ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
         dropWhile (\<lambda>s. s \<noteq> [False, True])) w)) \<and>
         (\<forall>w. TM.time_bounded_word M (\<lambda>n. 6 * n + 6) w)"
    apply auto
    apply (rule exI)
    apply auto
    apply (subst f [simplified, symmetric])
     apply auto
    by (metis set_all_length_2_wf)
  then obtain Mf_pre :: "(nat, bool list, unit) TM" where
    Mf_pre_syms: "TM.TM.symbols Mf_pre = {w. length w = 2}" and
    Mf_pre_computes: "\<And>w. set w \<subseteq> {w. length w = 2} \<Longrightarrow>
                      TM.computes_word Mf_pre w ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
                      dropWhile (\<lambda>s. s \<noteq> [False, True])) w)" and
    Mf_pre_tb: "TM.time_bounded Mf_pre (\<lambda>n. 6 * n + 6)" by blast
  define syms :: "bool list set" where "syms \<equiv> TM.symbols Mf_pre \<union> TM.symbols M"
  define Mdec :: "(nat, bool list, bool) TM_record" where "Mdec \<equiv> tm_extra_symbols M syms"
  define Mf :: "(nat, bool list, unit) TM_record" where "Mf \<equiv> tm_extra_symbols Mf_pre syms"
  have Mdec_valid [simp, intro]: "valid_TM Mdec"
    unfolding Mdec_def syms_def by (rule tm_extra_symbols_valid) simp
  have Mf_valid [simp, intro]: "valid_TM Mf"
    unfolding Mf_def syms_def by (rule tm_extra_symbols_valid) simp
  have Mdec_syms [simp]: "TM.symbols (Abs_TM Mdec) = syms"
    unfolding valid_tm_symbols [OF Mdec_valid] unfolding Mdec_def tm_extra_symbols_def syms_def by auto
  have Mf_syms [simp]: "TM.symbols (Abs_TM Mf) = syms"
    unfolding valid_tm_symbols [OF Mf_valid] unfolding Mf_def tm_extra_symbols_def syms_def by simp
  have syms_finite: "finite syms" unfolding syms_def by simp
  note DTIME_speed_up
  interpret comp: IO_TM_comp "Abs_TM Mf" "Abs_TM Mdec"
    apply unfold_locales
    unfolding Mf_syms Mdec_syms ..
  note tm_extra_symbols_compute [OF syms_finite, of _ Mf_pre, folded Mf_def, unfolded Mf_pre_syms]
  hence comp_word_eq: "\<And>w w'. set w \<subseteq> {w. length w = 2} \<Longrightarrow>
                       comp.M1.computes_word w w' \<longleftrightarrow> TM.computes_word Mf_pre w w'"
    by (simp add: Mf_def TM.computes_word_def TM.halts_compute syms_finite tm_extra_symbols_is_final)
  have Mf_computes: "\<And>w. set w \<subseteq> {w. length w = 2} \<Longrightarrow>
                     TM.computes_word (Abs_TM Mf) w ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
                     dropWhile (\<lambda>s. s \<noteq> [False, True])) w)" using Mf_pre_computes unfolding comp_word_eq .
  have 1: "\<And>w. set w \<subseteq> {w. length w = 2} \<Longrightarrow> comp.M1.wf_input w" by (auto simp add: syms_def Mf_pre_syms)
  have 2: "\<And>w. set w \<subseteq> {w. length w = 2} \<Longrightarrow>
           comp.M2.wf_input ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ> dropWhile (\<lambda>s. s \<noteq> [False, True])) w)"
    apply (auto simp add: syms_def Mf_pre_syms)
    by (metis (no_types, lifting) bin'_wf_def list.sel(2) list.set_sel(2) set_all_length_2_wf
        set_dropWhile_subset set_takeWhileD subsetD)
  have 3: "TM.initial_config (Abs_TM (tm_extra_symbols M syms)) = TM.initial_config M"
    apply (rule ext)
    unfolding TM.initial_config_def apply auto
     apply (metis (no_types, lifting) Mdec_def Mdec_valid select_convs(4) tm_extra_symbols_def
        valid_tm_initial_state)
    by (metis (no_types, lifting) Mdec_def Mdec_valid simps(1) tm_extra_symbols_def valid_tm_tape_count)
  have 4: "\<And>w. comp.M2.halts ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ> dropWhile (\<lambda>s. s \<noteq> [False, True])) w)"
    unfolding comp.M2.halts_def comp.M2.halts_config_def unfolding Mdec_def apply (subst tm_extra_symbols_steps)
        apply auto
    unfolding comp.M2.M'.symbols_in_config_def apply auto
        apply (subst (asm) TM.initial_config_def)
    unfolding TM_abbrevs.input_tape_def apply auto
        apply (erule ifE)
         apply auto
         apply (smt (verit, best) a1 * ** append_Cons insert_iff list.collapse list.inject singletonD
        takeWhile_dropWhile_id takeWhile_eq_Nil_iff)
        apply (metis a1 * ** empty_iff insert_iff list.set_sel(2) set_takeWhileD)
       apply fact
       apply (subst TM.initial_config_def)
      apply simp
    unfolding valid_tm_initial_state [OF Mdec_valid [unfolded Mdec_def]]
      apply (subst tm_extra_symbols_def)
      apply simp
     apply (subst TM.initial_config_def)
    unfolding TM_abbrevs.input_tape_def apply simp
     apply (metis (no_types, lifting) Mdec_def Mdec_valid simps(1) tm_extra_symbols_def valid_tm_tape_count)
    apply (subst tm_extra_symbols_is_final)
     apply fact
    unfolding TM.time_bounded_word_def TM.run_def apply (rule exI)
    using a3 [THEN spec, unfolded TM.time_bounded_word_def TM.run_def] unfolding 3 .
  note comp.io_comp_run' [OF Mf_computes 1 2 4]
  hence 5: "\<And>w. set w \<subseteq> {w. length w = 2} \<Longrightarrow> comp.run (comp.M1.time w + t (length w)) w =
            TM_config (Inr (state (comp.M2.run (t (length w)) ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
            dropWhile (\<lambda>s. s \<noteq> [False, True])) w))))
            (butlast (tapes (comp.M1.compute w)) @ tapes (comp.M2.run (t (length w))
            ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ> dropWhile (\<lambda>s. s \<noteq> [False, True])) w)))" .
  have 6: "set w \<subseteq> {w. length w = 2} \<Longrightarrow>
           state (comp.M2.run (t (length (takeWhile (\<lambda>s. s \<in> alphabet L)
           (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))))) ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
           dropWhile (\<lambda>s. s \<noteq> [False, True])) w)) \<in> comp.M2.final_states" for w :: "bool list list"
    using a3 unfolding TM.time_bounded_word_def TM.is_final_def unfolding Mdec_def
    apply (subst tm_extra_symbols_run)
      apply (rule syms_finite)
     apply (subst a1)
     apply auto[1]
    using * ** set_takeWhileD apply fastforce
    unfolding valid_tm_final_states [OF Mdec_valid [unfolded Mdec_def]] unfolding tm_extra_symbols_def by simp
  have "\<And>w. length (takeWhile (\<lambda>s. s \<in> alphabet L) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))) \<le> length w"
    by (metis (no_types, lifting) Nil_tl impossible_Cons length_dropWhile_le length_takeWhile_le list.collapse
        nle_le order_trans)
  hence 7: "\<And>w. t (length (takeWhile (\<lambda>s. s \<in> alphabet L) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)))) \<le>
            t (length w)" using t_mono incseqD by blast
  have 8: "set w \<subseteq> {w. length w = 2} \<Longrightarrow>
           state (comp.M2.run (t (length w)) ((takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
           dropWhile (\<lambda>s. s \<noteq> [False, True])) w)) \<in> comp.M2.final_states" for w :: "bool list list"
    apply (drule 6)
    using 7 [of w] comp.M2.final_mono_run by blast
  have 9: "set w \<subseteq> {w. length w = 2} \<Longrightarrow> comp.is_final (comp.run (comp.M1.time w + t (length w)) w)"
    for w :: "bool list list" unfolding 5 using 8 [of w] by fastforce
  have 10: "set w \<subseteq> {w. length w = 2} \<Longrightarrow> comp.M1.time w \<le> 6 * (length w) + 6" for w :: "bool list list"
    unfolding comp.M1.time_def comp.M1.config_time_def apply (rule Least_le)
    unfolding TM.run_def [symmetric] unfolding Mf_def apply (subst tm_extra_symbols_run)
      apply (rule syms_finite)
     apply auto
    using Mf_pre_syms apply blast
    apply (subst tm_extra_symbols_is_final)
     apply (rule syms_finite)
    by (metis Mf_pre_tb TM.time_bounded_word_def)
  have 11: "set w \<subseteq> {w. length w = 2} \<Longrightarrow> comp.M1.time w + t (length w) \<le>
            6 * (length w) + 6 + t (length w)" for w :: "bool list list" using 10 [of w] by fastforce
  have 12: "set w \<subseteq> {w. length w = 2} \<Longrightarrow>
            comp.is_final (comp.run (6 * (length w) + 6 + t (length w)) w)" for w :: "bool list list"
    apply (frule 9 [of w])
    apply (drule 11 [of w])
    unfolding TM.is_final_def comp.run_def using comp.final_mono by blast
  have comp_dec: "TM_decider.decides comp.M (Lang {s. length s = 2}
        (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
        \<notin> words L))" apply auto
    unfolding syms_def apply auto
    using Mf_pre_syms apply blast
    unfolding TM_decider.decides_def apply auto
    unfolding TM_decider.accepts_def TM_decider.acc_def apply simp
       apply (rule conjI)
        apply (metis (no_types, lifting) 9 TM.conf_time_finalI comp.M2.M'_fields(5) comp.M_fields(5) comp.halts_def
        comp.is_final_def haltsI)
  proof -
    fix w :: "bool list list"
    assume a6: "set w \<subseteq> {s. length s = 2}"
    have 1: "state (comp.steps (comp.config_time (comp.c\<^sub>0 w)) (comp.c\<^sub>0 w)) \<in> comp.F"
      using 12 [OF a6] comp.halts_def comp.is_final_def by blast
    obtain x :: nat where x_def: "state (comp.steps (comp.config_time (comp.c\<^sub>0 w)) (comp.c\<^sub>0 w)) = Inr x"
      by (metis 1 comp.final_is_Inr)
    have 2: "takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True])
             (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)) \<in> (alphabet L)*" apply (simp add: a1)
      using set_takeWhileD by fastforce
    have 3: "comp.F = Inr ` comp.M2.F" by simp
    have 4: "x \<in> TM.final_states M"
      using 1 [unfolded x_def] unfolding 3 apply auto
      unfolding valid_tm_final_states [OF Mdec_valid] unfolding Mdec_def tm_extra_symbols_def by simp
    have 13: "comp.config_time (comp.c\<^sub>0 w) \<le> comp.M1.config_time (comp.M1.c\<^sub>0 w) + t (length w)"
      unfolding comp.config_time_def apply (rule Least_le)
      using 9 [OF a6] unfolding comp.run_def comp.M1.time_def .
    have 14: "state (comp.steps (comp.M1.config_time (comp.M1.c\<^sub>0 w) + t (length w)) (comp.c\<^sub>0 w)) = Inr x"
      using x_def 1 13 by (smt (verit, best) comp.final_mono comp.is_final_def comp.is_final_states_eq)
    note 15 = 5 [OF a6, THEN arg_cong, of state, simplified, unfolded 14, THEN Inr_inject]
    have 16: "state (TM.steps M (t (length w)) (TM.initial_config M (takeWhile (\<lambda>s. s \<in> alphabet L)
              (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))))) = x" unfolding 15 unfolding TM.run_def [symmetric]
      unfolding Mdec_def apply (subst tm_extra_symbols_run)
        apply fact
      using a4 set_takeWhileD apply fastforce
      ..
    have steps_eq_compute:"\<And>M w n. state (TM.steps M n (TM.initial_config M w)) \<in> TM.final_states M \<Longrightarrow>
                           TM.steps M n (TM.initial_config M w) = TM.compute M w"
      by (metis TM.run_def TM.compute_run_eqI TM.is_final_def)
    have 17: "state (TM.compute M (takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True])
              (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)))) = x" apply (subst steps_eq_compute [symmetric])
      using 4 [folded 16, unfolded a1] apply simp
      using 16 unfolding a1 by simp
    show "takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True])
          (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)) \<notin> words L \<Longrightarrow>
          case state (comp.steps (comp.config_time (comp.c\<^sub>0 w)) (comp.c\<^sub>0 w)) of Inr x \<Rightarrow> comp.M2.label x"
      unfolding x_def apply simp
      using a2 [THEN bspec, OF 2] unfolding valid_tm_label [OF Mdec_valid] unfolding Mdec_def tm_extra_symbols_def
      apply simp
      unfolding TM_decider.decides_def apply auto
       apply (subst (asm) compl_word)
      unfolding a1 apply auto
      using set_takeWhileD apply fastforce
      unfolding TM_decider.accepts_def TM_decider.acc_def apply auto
      unfolding 17 [symmetric] apply simp
      unfolding 17 using 4 apply simp
      using 2 compl_word by auto
    have 18: "state (comp.compute w) = Inr x"
      using 1 comp.compute_run_eqI comp.is_final_def comp.run_def x_def by presburger
    show "state (comp.compute w) \<in> {q \<in> comp.F. comp.label q = True} \<Longrightarrow>
          takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True])
          (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)) \<in>\<^sub>L L \<Longrightarrow> False" unfolding 18 apply auto
      unfolding valid_tm_label [OF Mdec_valid] valid_tm_final_states [OF Mdec_valid] unfolding Mdec_def
        tm_extra_symbols_def apply simp
      using a2 [THEN bspec, OF 2, unfolded TM_decider.decides_def, THEN conjunct2] apply (subst (asm) compl_word)
       apply (rule 2)
      apply simp
      unfolding TM_decider.rejects_def TM_decider.rej_def apply auto
      using 17 by force
    show "takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True])
          (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)) \<in>\<^sub>L L \<Longrightarrow> TM_decider.rejects comp.M w"
      unfolding TM_decider.rejects_def 18 TM_decider.rej_def apply auto
      using 1 3 x_def apply argo
      using a2 [THEN bspec, OF 2, unfolded TM_decider.decides_def, THEN conjunct2] apply (subst (asm) compl_word)
       apply (rule 2)
      apply simp
      unfolding valid_tm_label [OF Mdec_valid] unfolding Mdec_def tm_extra_symbols_def apply simp
      unfolding TM_decider.rejects_def TM_decider.rej_def apply auto
      using 17 by blast
    show "TM_decider.rejects comp.M w \<Longrightarrow>
          takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True])
          (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)) \<in>\<^sub>L L"
      unfolding TM_decider.rejects_def 18 TM_decider.rej_def apply auto
      unfolding valid_tm_label [OF Mdec_valid] valid_tm_final_states [OF Mdec_valid] unfolding Mdec_def
        tm_extra_symbols_def apply simp
      using a2 [THEN bspec, OF 2, unfolded TM_decider.decides_def, THEN conjunct2] apply (subst compl_word)
       apply (rule 2)
      apply simp
      unfolding TM_decider.rejects_def TM_decider.rej_def 17 by simp
  qed
  have 13: "Lang {s. length s = 2}
            (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
            \<notin>\<^sub>L L) \<in> typed_DTIME TYPE(nat + nat) (\<lambda>n. 6 * n + 6 + t n)"
    apply (rule in_dtimeI'' [where M="comp.M"])
    using comp_dec apply meson
    using comp_dec apply meson
    apply simp
    using 12 by fast
  have 14: "superlinear (\<lambda>n. 6 * n + 6 + t n)"
    using t_superlinear by (rule superlinear_nat_addI' [OF disjI2])
  have 15: "(\<lambda>n. (6 * real n + 6 + real (t n)) / 12) = (\<lambda>n. real n / 2 + 1 / 2 + real (t n) / 12)"
    by auto
  note DTIME_speed_up [OF 13 [THEN typed_DTIME_impl_DTIME] 14, of "1 / 12", simplified, unfolded 15,
      THEN in_dtimeD']
  then obtain Msu :: "(nat, bool list) TM_decider" where
    Msu_syms: "alphabet (Lang {s. length s = 2}
     (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
     \<notin>\<^sub>L L)) \<subseteq> TM.TM.symbols Msu" and
    Msu_dec: "\<forall>w\<in>(alphabet (Lang {s. length s = 2}
     (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
     \<notin>\<^sub>L L)))*. TM_decider.decides_word Msu (Lang {s. length s = 2}
     (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
     \<notin>\<^sub>L L)) w" and
    Msu_tb: "\<forall>w. TM.time_bounded_word Msu (tcomp (\<lambda>n. real n / 2 + 1 / 2 + real (t n) / 12)) w" by blast
  have 16: "\<forall>\<^sub>\<infinity>w\<in>{s. length s = 2}*. TM.time_bounded_word Msu t w"
    apply (rule ae_word_lengthI)
     apply simp_all
     apply (metis finite_bin_len_eq)
  proof -
    fix w :: "bool list list"
    have "\<exists>n0. \<forall>n\<ge>n0. 6 * n \<le> t n"
      using t_superlinear unfolding superlinear_altdef_nat by blast
    hence "\<exists>n0. \<forall>n\<ge>n0. real n \<le> real (t n) / 6" by force
    hence "\<exists>n0. \<forall>n\<ge>n0. real n / 2 \<le> real (t n) / 12" by force
    then obtain n0 :: nat where n0_def: "\<And>n. n\<ge>n0 \<Longrightarrow> real n / 2 \<le> real (t n) / 12" by blast
    have "\<exists>n0. \<forall>n\<ge>n0. 6 \<le> t n"
      apply (rule exI [where x=6])
      apply auto
      using t_gt_n [of 6] t_mono by (meson nat_less_le order_trans t_gt_n)
    hence "\<exists>n0. \<forall>n\<ge>n0. 1 / 2 \<le> real (t n) / 12" by force
    then obtain n1 :: nat where n1_def: "\<And>n. n\<ge>n1 \<Longrightarrow> 1 / 2 \<le> real (t n) / 12" by blast
    have 2: "\<And>n. real (t n) / 4 \<le> real (t n)" by simp
    have 3: "\<exists>n0. \<forall>n\<ge>n0. real n / 2 + 1 / 2 + real (t n) / 12 \<le> t n"
    proof
      show "\<forall>(n::nat)\<ge>max n0 n1. real n / 2 + 1 / 2 + real (t n) / 12 \<le> real (t n)"
        apply auto
        apply (drule n0_def)
        apply (drule n1_def)
        using 2 by linarith
    qed
    define n :: nat where "n \<equiv> (SOME n0. \<forall>n\<ge>n0. real n / 2 + 1 / 2 + real (t n) / 12 \<le> t n)"
    note 4 = someI_ex [OF 3, folded n_def]
    assume a1: "set w \<subseteq> {s. length s = 2}" and a2: "n \<le> length w"
    have 5: "t = tcomp t" using t_gt_n by simp
    have "\<forall>n'\<ge>n. (tcomp (\<lambda>n. real n / 2 + 1 / 2 + real (t n) / 12)) n' \<le> (tcomp t) n'"
      using 4 by blast
    hence 6: "(tcomp (\<lambda>n. real n / 2 + 1 / 2 + real (t n) / 12)) (length w) \<le> (tcomp t) (length w)"
      using a2 by blast
    show "TM.time_bounded_word Msu t w" apply (subst 5)
      using Msu_tb 6 TM.time_bounded_word_mono by blast
  qed
  have 17: "\<forall>\<^sub>\<infinity>x\<in>(alphabet (Lang {s. length s = 2}
            (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
            \<notin> words L)))*. TM_decider.decides_word Msu
            (Lang {s. length s = 2}
            (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
            \<notin> words L)) x \<and> TM.time_bounded_word Msu t x" using Msu_dec 16 by auto
  note 18 = DTIME_ae_tcomp [OF exI, OF conjI, OF Msu_syms 17]
  note T_gt_t_ae
  hence 19: "\<forall>\<^sub>\<infinity>n. tcomp (\<lambda>x. real (t x)) n \<le> min (t n) (T n)" by auto
  have 20: "tcomp (\<lambda>x. real (min (t x) (T x))) = (\<lambda>x. min (t x) (T x))"
    apply (rule ext)
    apply auto
    using t_gt_n tht.T_gt_n by (simp add: less_eq_Suc_le)
  note DTIME_mono_ae [OF 18 19, unfolded 20]
  thus "Lang {s. length s = 2}
        (\<lambda>w. takeWhile (\<lambda>s. s = [True, False] \<or> s = [True, True]) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w))
        \<notin> words L) \<in> DTIME (\<lambda>n. min (t n) (T n))" .
qed

theorem L_poly_reduction: "alphabet L = {[True, False], [True, True]} \<Longrightarrow>
                           L \<in> DTIME t \<Longrightarrow> L \<le>\<^sub>p L\<^sub>0"
proof (frule (1) dereduced_decidable)
  assume a1: "alphabet L = {[True, False], [True, True]}" and a2: "L \<in> DTIME t" and
         a3: "Lang {s. length s = 2} (\<lambda>w. (takeWhile (\<lambda>s. s \<in> alphabet L) \<circ> tl \<circ>
              dropWhile (\<lambda>s. s \<noteq> [False, True])) w \<notin>\<^sub>L L) \<in> DTIME (\<lambda>n. min (t n) (T n))"
  note in_dtimeD' [OF a3, simplified]
  then obtain M :: "(nat, bool list) TM_decider" where M_syms: "{s. length s = 2} \<subseteq> TM.TM.symbols M" and
      M_dec: "\<And>w. set w \<subseteq> {s. length s = 2} \<Longrightarrow> (TM_decider.decides_word M (Lang {s. length s = 2}
              (\<lambda>w. takeWhile (\<lambda>s. s \<in> alphabet L) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True]) w)) \<notin>\<^sub>L L)) w)" and
      M_tb: "TM.time_bounded M (\<lambda>n. min (t n) (T n))" by auto
  have M_tb_t: "TM.time_bounded M t"
    using M_tb by (rule TM.time_bounded_mono) simp
  have M_tb_T: "TM.time_bounded M T"
    using M_tb by (rule TM.time_bounded_mono) simp
  have M_tb_tlR: "TM.time_bounded M (t \<circ> l\<^sub>R)"
    using M_tb apply (rule TM.time_bounded_mono)
    using min_le_iff_disj t'_ge_t by blast
  define pre_reduction :: "bool list list \<Rightarrow> bool list list" ("\<phi>\<^sub>p\<^sub>r\<^sub>e") where
    "\<And>w. \<phi>\<^sub>p\<^sub>r\<^sub>e w \<equiv> add_exp_pad' (add_al_prefix' (enc_TM M)) @ [$] @ w @ [$]"
  define reduction :: "bool list list \<Rightarrow> bool list list" ("\<phi>") where
    "\<And>w. \<phi> w \<equiv> adj_sq\<^sub>w' (reduce_LD_LD' (\<phi>\<^sub>p\<^sub>r\<^sub>e w))"
  show "L \<le>\<^sub>p L\<^sub>0"
  proof (rule poly_reducibleI')
    (* Definitely prove the following statement *)
    (* This asserts that \<phi> is in fact a reduction function *)
    show "w \<in>\<^sub>L L \<longleftrightarrow> \<phi> w \<in>\<^sub>L L\<^sub>0" if "set w \<subseteq> alphabet L" for w :: "bool list list"
    proof -
      have "\<phi> w \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> reduce_LD_LD' (\<phi>\<^sub>p\<^sub>r\<^sub>e w) \<in>\<^sub>L L\<^sub>D'" unfolding reduction_def
      proof (rule L\<^sub>D'_L\<^sub>0_adj_sq_iff)
        show "7 \<le> length (reduce_LD_LD' (\<phi>\<^sub>p\<^sub>r\<^sub>e w))" unfolding reduce_LD_LD'_def
            encode_pair_def Let_def apply auto
          apply (subst pre_reduction_def)
          apply auto
          using rev_suffix_len_def by fastforce
        show "set (reduce_LD_LD' (\<phi>\<^sub>p\<^sub>r\<^sub>e w)) \<subseteq> {s. length s = 2}" unfolding reduce_LD_LD'_def
            encode_pair_def Let_def apply auto
          unfolding pre_reduction_def Let_def apply (auto simp add: separator_def)
          using enc_TM_wf apply fastforce
          using that a1 by fastforce
        show "\<exists>ys. reduce_LD_LD' (\<phi>\<^sub>p\<^sub>r\<^sub>e w) = [True, False] # ys"
          unfolding reduce_LD_LD'_def encode_pair_def Let_def apply auto
          apply (subst pre_reduction_def)
          by simp
      qed
      also have "... \<longleftrightarrow> \<phi>\<^sub>p\<^sub>r\<^sub>e w \<in>\<^sub>L tht.L\<^sub>D" by (rule reduce_LD_LD'_correct)
      finally have 1: "\<phi> w \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> \<phi>\<^sub>p\<^sub>r\<^sub>e w \<in>\<^sub>L tht.L\<^sub>D" .
      have *: "[False, False] \<noteq> [True, False]" and **: "[False, False] \<noteq> [True, True]" by simp_all
      have 2: "4 * 2 ^ length (enc_TM M) > Suc (Suc (length (enc_TM M)))"
        by (metis One_nat_def add_Suc less_exp numeral_2_eq_2 numeral_Bit0_eq_double plus_1_eq_Suc
            power2_eq_square power_add)
      have ***: "\<And>x y xs ys. (x # y # xs) @ ys = x # y # xs @ ys" by simp
      have ****: "\<And>n l1 l2. length l1 \<le> n \<Longrightarrow> take n (l1 @ l2) = l1 @ (take (n - length l1) l2)" by simp
      have "length (add_al_prefix' (enc_TM M)) \<le> x \<Longrightarrow> dec_TM (strip_al_prefix' (take x
            (add_exp_pad' (add_al_prefix' (enc_TM M)) @ [$] @ w @ [$]))) =
            dec_TM (enc_TM M)" for x :: nat
        apply auto
        apply (cases "Suc (Suc (length (enc_TM M))) < x")
        apply (subst dec_TM_append [OF valid_enc * **, of M, symmetric,
              where t="take (x - Suc (Suc (Suc (length (enc_TM M)))))
                       ([False, False] \<up> (4 * 2 ^ length (enc_TM M) - Suc (Suc (Suc (length (enc_TM M))))) @
                       $ # w @ [$])"])
         apply (rule arg_cong [where f=dec_TM])
         apply auto
        apply (subst *** [symmetric])
        apply (subst ****)
         apply simp
        apply simp
        by (smt (verit, best) 2 Suc_diff_Suc add_Suc_right append_Cons min_Suc_Suc replicate_Suc)
      also have "... = canonical_TM M" by (rule enc_dec_TM)
      finally have 3: "\<And>x. length (add_al_prefix' (enc_TM M)) \<le> x \<Longrightarrow>
                       dec_TM (strip_al_prefix' (take x (add_exp_pad' (add_al_prefix' (enc_TM M)) @
                       [$] @ w @ [$]))) = canonical_TM M" .
      have 4: "dec_TM_pad' (\<phi>\<^sub>p\<^sub>r\<^sub>e w) = canonical_TM M"
        unfolding pre_reduction_def Let_def dec_TM_pad'_def enc_dec_TM [symmetric]
        apply (rule strip_exp_pad'_add_append_ex [THEN exE])
        apply (erule conjE)
        apply (erule ssubst)
        unfolding 3 by (simp add: enc_dec_TM)
      have 5: "set (\<phi>\<^sub>p\<^sub>r\<^sub>e w) \<subseteq> TM.symbols M"
        using M_syms unfolding pre_reduction_def apply auto
        unfolding separator_def apply auto
        using enc_TM_wf set_all_length_2_wf apply blast
        apply (drule that [THEN subsetD, unfolded a1])
        by auto
      show "w \<in>\<^sub>L L \<longleftrightarrow> \<phi> w \<in>\<^sub>L L\<^sub>0" unfolding 1
      proof
        assume a3: "w \<in>\<^sub>L L"
        have w_in_syms: "set (\<phi>\<^sub>p\<^sub>r\<^sub>e w) \<subseteq> {w. length w = 2}"
          using that unfolding a1 pre_reduction_def Let_def separator_def apply auto
          by (metis enc_TM_wf bin'_wf_def)
        show "\<phi>\<^sub>p\<^sub>r\<^sub>e w \<in>\<^sub>L tht.L\<^sub>D" unfolding tht.L\<^sub>D_def apply auto
          unfolding Let_def apply (subst (asm) pre_reduction_def)
           apply auto
          unfolding separator_def apply simp
          using bin'_wf_def enc_TM_wf apply blast
          using that unfolding a1 apply fastforce
          unfolding 4 canonical_TM_rejects [simplified, OF 5] canonical_TM_time_bounded [simplified, OF 5]
        proof -
          note 6 = M_dec [OF w_in_syms, unfolded TM_decider.decides_def, THEN conjunct2, THEN iffD1]
          have 7: "dropWhile (\<lambda>s. s \<noteq> [False, True]) (enc_TM M @
                   [False, False] \<up> (4 * 2 ^ length (enc_TM M) - Suc (Suc (length (enc_TM M)))) @
                   [False, True] # w @ [[False, True]]) = [False, True] # w @ [[False, True]]"
            using enc_TM_doubletons [of M] unfolding dropWhile_append by auto
          show "TM_decider.rejects M (\<phi>\<^sub>p\<^sub>r\<^sub>e w)"
            apply (rule 6)
            unfolding pre_reduction_def Let_def separator_def apply auto
            unfolding 7 apply simp
            unfolding a1 using a3 [unfolded words_def, simplified, THEN conjunct1, unfolded a1]
            unfolding takeWhile_append apply simp
            apply (rule conjI)
             apply (rule impI)
             apply (rule a3)
            by blast
        next
          show "TM.time_bounded_word M (t \<circ> l\<^sub>R) (\<phi>\<^sub>p\<^sub>r\<^sub>e w)" using M_tb_tlR ..
        qed
      next
        assume a3: "\<phi>\<^sub>p\<^sub>r\<^sub>e w \<in>\<^sub>L tht.L\<^sub>D"
        have *: "\<phi>\<^sub>p\<^sub>r\<^sub>e w \<in> (TM.symbols M)*" using M_syms a3 unfolding tht.L\<^sub>D_def by auto
        note a3 [unfolded tht.L\<^sub>D_def Let_def, simplified, unfolded 4 canonical_TM_rejects [OF *]
            canonical_TM_time_bounded [OF *]]
        hence 1: "set (\<phi>\<^sub>p\<^sub>r\<^sub>e w) \<subseteq> {w. length w = 2}" and
              2: "TM_decider.rejects M (\<phi>\<^sub>p\<^sub>r\<^sub>e w)" by blast+
        have 3: "set ([False, False] \<up> 0) \<subseteq> {s. length s = 2}" by auto
        (* ^^ Unnecessary, but I'm too lazy to clean up; and then there would be 2 and then 4 - that'd be weird *)
        have 4: "set w \<subseteq> {s. length s = 2}" using that unfolding a1 by auto
        have 5: "set ([False, False] \<up> (4 * 2 ^ length (enc_TM M) - Suc (Suc (length (enc_TM M))))) \<subseteq>
                 {s. length s = 2}" by auto
        have 6: "set (enc_TM M) \<subseteq> {s. length s = 2}" using enc_TM_doubletons by fastforce
        have 7: "\<forall>s\<in>set (enc_TM M). s \<noteq> [False, True]"
          using enc_TM_doubletons by auto
        have 8: "takeWhile (\<lambda>s. s \<in> alphabet L) (tl (dropWhile (\<lambda>s. s \<noteq> [False, True])
                 (enc_TM M @ [False, False] \<up> (4 * 2 ^ length (enc_TM M) - Suc (Suc (length (enc_TM M)))) @
                 [False, True] # w @ [[False, True]]))) = w"
          unfolding dropWhile_append using 7 apply simp
          unfolding takeWhile_append a1 apply simp
          apply (rule impI)
          apply (erule bexE)
          apply (erule conjE)
          apply (rule ballI)
          apply (rule disjCI)
          using that unfolding a1 by auto
        show "w \<in>\<^sub>L L"
          using 2 M_dec [OF 1] unfolding pre_reduction_def Let_def separator_def apply auto
          unfolding TM_decider.decides_def apply (drule conjunct2)
          apply simp
          apply (drule mp)
           apply (rule 4)
          apply (drule mp)
           apply (rule 5)
          apply (drule mp)
           apply (rule 6)
          unfolding 8 .
      qed
    qed

    (* The rest here asserts that \<phi> can be computed in polynomial time asymptotically.
       If I have enough time, I will do this as well - but maybe not. *)

    (* Part 1: Computability of \<phi>\<^sub>p\<^sub>r\<^sub>e in linear time *)
    have prered_is_funcomp_twice: "\<phi>\<^sub>p\<^sub>r\<^sub>e =
                                   (((@) (add_exp_pad' (add_al_prefix' (enc_TM M)) @ [$])) \<circ> (\<lambda>w. w @ [$]))"
      unfolding pre_reduction_def by auto
    have prered_computable: "computable_in_time
                             (\<lambda>n. 2 * n + 7 + length (add_exp_pad' (add_al_prefix' (enc_TM M))))
                             (((@) (map (inv bits_conversion) (add_exp_pad' (add_al_prefix' (enc_TM M)) @ [$]))) \<circ>
                             (\<lambda>w. w @ [FT]))"
    proof -
      note 1 = append_suffix_computable [of "[FT]", simplified]
      note 2 = add_const_prefix_computable
        [of "map (inv bits_conversion) (add_exp_pad' (add_al_prefix' (enc_TM M)) @ [$])"]
      note 3 = computable_in_time_compI [OF 1 2, unfolded max_Tf_constant [OF refl]]
      show "computable_in_time (\<lambda>n. 2 * n + 7 + length (add_exp_pad' (add_al_prefix' (enc_TM M))))
            (((@) (map (inv bits_conversion) (add_exp_pad' (add_al_prefix' (enc_TM M)) @ [$]))) \<circ>
            (\<lambda>w. w @ [FT]))" apply (rule computable_mono)
         apply (rule 3)
        by simp
    qed
    have bits_conv_inv_inv: "\<And>w. set w \<subseteq> {s. length s = 2} \<Longrightarrow>
                             map bits_conversion (((@) (map (inv bits_conversion)
                             (add_exp_pad' (add_al_prefix' (enc_TM M)) @ [$])) \<circ> (\<lambda>w. w @ [FT]))
                             (map (inv bits_conversion) w)) = \<phi>\<^sub>p\<^sub>r\<^sub>e w"
      unfolding prered_is_funcomp_twice apply auto
         apply (rule map_f_invf_is_id [OF bits_conversion_bij])
          apply (simp add: enc_TM_wf set_all_length_2_wf)
      unfolding separator_def apply simp_all
      by (rule map_f_invf_is_id [OF bits_conversion_bij])
    note typed_comp_in_time_sym_type [OF bits_conversion_bij prered_computable]
    hence "\<exists>Ma :: (nat, bool list, unit) TM. TM.TM.symbols Ma = {s. length s = 2} \<and>
       (\<forall>w\<in>{s. length s = 2}*. TM.computes_word Ma w (\<phi>\<^sub>p\<^sub>r\<^sub>e w)) \<and>
       (\<forall>w. TM.time_bounded_word Ma (\<lambda>n. 2 * n + 7 + length (add_exp_pad' (add_al_prefix' (enc_TM M)))) w)"
    proof auto
      fix M' :: "(nat, bool list, unit) TM"
      assume a1: "TM.TM.symbols M' = {s. length s = 2}" and
             a2: "\<forall>w\<in>{s. length s = 2}*. TM.computes_word M' w ([True, True] #
                  [True, False] # map (bits_conversion \<circ> inv bits_conversion) (enc_TM M) @
                  [False, False] \<up> (4 * 2 ^ length (enc_TM M) - Suc (Suc (length (enc_TM M)))) @
                  bits_conversion (inv bits_conversion $) #
                  map (bits_conversion \<circ> inv bits_conversion) w @ [[False, True]])" and
             a3: "\<forall>w. TM.time_bounded_word M'
                  (\<lambda>n. 9 + (2 * n + (length (enc_TM M) +
                  (4 * 2 ^ length (enc_TM M) - Suc (Suc (length (enc_TM M))))))) w"
      show "\<exists>Ma::(nat, bool list, unit) TM. TM.TM.symbols Ma = {s. length s = 2} \<and>
            (\<forall>w\<in>{s. length s = 2}*. TM.computes_word Ma w (\<phi>\<^sub>p\<^sub>r\<^sub>e w)) \<and>
            (\<forall>w. TM.time_bounded_word Ma (\<lambda>n. 9 + (2 * n +
            (length (enc_TM M) + (4 * 2 ^ length (enc_TM M) - Suc (Suc (length (enc_TM M))))))) w)"
        apply (rule exI [where x=M'])
        apply auto
        using a1 apply blast+
         apply (subst bits_conv_inv_inv [symmetric])
          apply simp_all
        using a2 apply blast
        using a3 ..
    qed
    then obtain M\<^sub>\<phi>\<^sub>p\<^sub>r\<^sub>e :: "(nat, bool list, unit) TM" where
      M\<^sub>\<phi>\<^sub>p\<^sub>r\<^sub>e_syms: "TM.TM.symbols M\<^sub>\<phi>\<^sub>p\<^sub>r\<^sub>e = {s. length s = 2}" and
      M\<^sub>\<phi>\<^sub>p\<^sub>r\<^sub>e_comp: "\<And>w. set w \<subseteq> {s. length s = 2} \<Longrightarrow> TM.computes_word M\<^sub>\<phi>\<^sub>p\<^sub>r\<^sub>e w (\<phi>\<^sub>p\<^sub>r\<^sub>e w)" and
      M\<^sub>\<phi>\<^sub>p\<^sub>r\<^sub>e_tb: "\<And>w. TM.time_bounded_word M\<^sub>\<phi>\<^sub>p\<^sub>r\<^sub>e
                (\<lambda>n. 2 * n + 7 + length (add_exp_pad' (add_al_prefix' (enc_TM M)))) w" by blast

    (* Part 2: Computability of reduce_LD_LD' in linear time *)
    (* Sorry for now; easy to see *)

    (* Part 3: Computability of adj_sq\<^sub>w' in quadratic time *)
    (* Sorry for now; see Java implementation *)

    (* Putting everything together: *)
    define M\<^sub>\<phi> :: "(nat, bool list, unit) TM_record" where "M\<^sub>\<phi> \<equiv> undefined"
    fix w :: "bool list list" and n :: nat
    show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M\<^sub>\<phi>)" sorry
    show "alphabet L\<^sub>0 \<subseteq> TM.TM.symbols (Abs_TM M\<^sub>\<phi>)" sorry
    define n0 :: nat where "n0 \<equiv> undefined"
    define k :: nat where "k \<equiv> undefined"
      (* Probably don't use t here as time bound, but some more fitting function *)
    show "t n \<le> n^k" if "n0 \<le> n" sorry
    assume a3: "set w \<subseteq> alphabet L"
    show "TM.computes_word (Abs_TM M\<^sub>\<phi>) w (\<phi> w)" sorry
    show "TM.time_bounded_word (Abs_TM M\<^sub>\<phi>) t w" sorry
    have bin'_wf_iff: "set xs \<subseteq> {s. length s = 2} \<longleftrightarrow> bin'_wf xs" for xs :: "bool list list"
      unfolding bin'_wf_def by blast
    show "set (\<phi> w) \<subseteq> alphabet L\<^sub>0"
      using a3 [unfolded a1] unfolding L\<^sub>0_def L\<^sub>D'_def SQ'_def apply simp
      unfolding bin'_wf_iff reduction_def pre_reduction_def Let_def apply (rule bin'_wf_adj_sq\<^sub>w'I)
      unfolding bin'_wf_red_LD_LD'_iff apply (rule bin'_wf_appI)
      unfolding add_exp_pad'_wf add_al_prefix'_bin'_wf_iff apply (rule enc_TM_wf)
      apply (rule bin'_wf_appI)
      unfolding separator_def apply fastforce
      apply (rule bin'_wf_appI)
       apply (rule bin'_wfI)
      by auto fastforce
  qed
qed

lemma lemma4_7: "DTIME_hard L\<^sub>0 t {[True, False], [True, True]}"
  using L_poly_reduction by auto
end \<comment> \<open>context \<^locale>\<open>lemma4_7\<close>\<close>
end
