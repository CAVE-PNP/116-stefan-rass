section\<open>The Time Hierarchy Theorem and the Language \<open>L\<^sub>0\<close>\<close>

theory L0
  imports SQ Complexity TM_Encoding Transformations
begin


subsection\<open>Preliminaries\<close>

lemma SQ_DTIME: "SQ \<in> DTIME(\<lambda>n. n^3)" sorry


locale UTM_Encoding =
  fixes enc\<^sub>U :: "('q, 's, 'l) TM \<times> 's list \<Rightarrow> bool list"
    and is_valid_enc\<^sub>U :: "bool list \<Rightarrow> bool"
    and dec\<^sub>U :: "bool list \<Rightarrow> ('q, 's, 'l) TM \<times> 's list"
    and L_invalid :: 'l
  assumes inj_enc\<^sub>U: "inj enc\<^sub>U"
    and valid_enc: "\<And>M w. TM.wf_input M w \<Longrightarrow> is_valid_enc\<^sub>U (enc\<^sub>U (M, w))"
    and enc_dec:   "\<And>M w. TM.wf_input M w \<Longrightarrow> dec\<^sub>U (enc\<^sub>U (M, w)) = (M, w)" (* TODO again, this is not possible with the current definitions, as label is an unrestricted function *)

      (* TODO is this necessary? could the UTM not just directly output the invalid label when it detects that an encoding is invalid? *)
    and invalid_rejects: "\<And>x. \<not> is_valid_enc\<^sub>U x \<Longrightarrow> let (M, w) = dec\<^sub>U x; c = TM.compute M w in TM.is_final M c \<and> TM.label M (state c) = L_invalid" (* a nicer version of: "\<exists>q\<^sub>0 s w. dec\<^sub>U x = (rejecting_TM q\<^sub>0 s, w)" *)
    and dec_enc: "\<And>x. is_valid_enc\<^sub>U x \<Longrightarrow> enc\<^sub>U (dec\<^sub>U x) = x" (* this should be easy to achieve *)

locale UTM = UTM: TM M\<^sub>U + UTM_Encoding enc\<^sub>U is_valid_enc\<^sub>U dec\<^sub>U False
  for M\<^sub>U :: "('q, bool) TM_decider" (* TODO make 'q = nat ? *)
    and enc\<^sub>U :: "('q, nat) TM_decider \<times> nat list \<Rightarrow> bool list"
    and is_valid_enc\<^sub>U dec\<^sub>U +
  assumes halts_iff: "\<And>M w. TM.halts   M w \<longleftrightarrow> TM.halts   M\<^sub>U (enc\<^sub>U (M, w))"
    and accepts_iff: "\<And>M w. TM_decider.accepts M w \<longleftrightarrow> TM_decider.accepts M\<^sub>U (enc\<^sub>U (M, w))"

locale timed_UTM = UTM M\<^sub>U  for M\<^sub>U :: "(nat, bool) TM_decider" +
  fixes T\<^sub>U :: "nat \<Rightarrow> nat" \<comment> \<open>Simulation time overhead of \<^term>\<open>M\<^sub>U\<close>.\<close>
  assumes sim_overhead: "\<And>M::(nat, nat) TM_decider. \<And>w. TM.halts M w \<Longrightarrow>
    TM.time M\<^sub>U (enc\<^sub>U (M, w)) \<le> T\<^sub>U (TM.time M w)"
    and overhead_min: "T\<^sub>U n \<ge> n" \<comment> \<open>This should be trivially true, but is required for the THT.\<close>


subsection\<open>The Time Hierarchy Theorem\<close>

locale tht_assms = TM_Encoding + timed_UTM +
  fixes T t :: "nat \<Rightarrow> nat"
  assumes fully_tconstr_T: "fully_time_constr T"

  \<comment> \<open>This assumption represents the statements containing \<open>lim\<close> @{cite rassOwf2017} and \<open>lim inf\<close> @{cite hopcroftAutomata1979}.
      \<^const>\<open>LIMSEQ\<close> (\<^term>\<open>X \<longlonglongrightarrow> x\<close>) was chosen, as it seems to match the intended meaning
      (@{thm LIMSEQ_def lim_sequentially}).
      The sources additionally specify \<^term>\<open>T\<^sub>U n = n * log 2 n\<close>.\<close>
    and T_dominates_t: "(\<lambda>n. T\<^sub>U (t n) / T n) \<longlonglongrightarrow> 0"
  \<comment> \<open>Additionally, \<open>T n\<close> is assumed not to be zero since in Isabelle,
      \<open>x / 0 = 0\<close> holds over the reals (@{thm division_ring_divide_zero}).
      Thus, the above assumption would trivially hold for \<open>T(n) = 0\<close>.\<close>
    and T_not_0: "\<forall>\<^sub>\<infinity>n. T n \<noteq> 0"

  \<comment> \<open>The following assumption is not found in @{cite rassOwf2017} or the primary source @{cite hopcroftAutomata1979},
    but is taken from the AAU lecture slides of \<^emph>\<open>Algorithms and Complexity Theory\<close>.
    \<^footnote>\<open>TODO properly cite this\<close>
    It patches a hole that allows one to prove \<^const>\<open>False\<close> from the Time Hierarchy Theorem below
    (\<open>time_hierarchy\<close>).
    This is demonstrated in \<^file>\<open>examples/THT_inconsistencies_MWE.thy\<close>.\<close>
    and t_min: "\<forall>\<^sub>\<infinity> n. n \<le> t n"
begin


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


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  ``The `diagonal-language' \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>L\<^sub>D := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.''
  @{cite rassOwf2017}\<close>

definition L\<^sub>D :: "bool lang"
  where "L\<^sub>D \<equiv> Lang UNIV (\<lambda>w. let M\<^sub>w = dec_TM_pad w in
                  TM_decider.rejects M\<^sub>w w \<and> TM.time_bounded_word M\<^sub>w T w)"

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
    Thus \<open>M\<close> accepts \<open>w\<close>, iff \<open>M\<^sub>w\<close> rejects \<open>w\<close> in time \<open>tcomp\<^sub>w T w\<close>.\<close>

  define L\<^sub>D_P where "L\<^sub>D_P \<equiv> \<lambda>w. let M\<^sub>w = dec_TM_pad w in
    TM_decider.rejects M\<^sub>w w \<and> TM.time_bounded_word M\<^sub>w T w"
  then have L\<^sub>D[simp]: "L\<^sub>D = Lang UNIV L\<^sub>D_P" unfolding L\<^sub>D_def by simp

  obtain M :: "(nat, bool) TM_decider" where "TM.symbols M = UNIV" and "TM.time_bounded M T"
    and *: "\<And>w. if L\<^sub>D_P w then TM_decider.accepts M w else TM_decider.rejects M w" sorry (* probably out of scope *)
  then have "TM_decider.decides M L\<^sub>D" unfolding TM_decider.decides_altdef4 by simp
  with \<open>TM.time_bounded M T\<close> show "L\<^sub>D \<in> DTIME T" by blast
qed

lemma LD_t: "L\<^sub>D \<notin> DTIME(t)"
proof -
  have "L \<noteq> L\<^sub>D" if "L \<in> DTIME(t)" for L
  proof -
    from \<open>L \<in> DTIME t\<close> obtain M\<^sub>w :: "(nat, bool) TM_decider"
      where "TM_decider.decides M\<^sub>w L" and "TM.time_bounded M\<^sub>w t" ..
    interpret TM_decider M\<^sub>w .

    define w' :: "bool list" where "w' = enc_TM M\<^sub>w"

    let ?n = "length (enc_TM M\<^sub>w) + 2"
    obtain l where "T l \<ge> t l" and "clog l \<ge> ?n"
    proof -
      obtain l\<^sub>1 :: nat where l1: "l \<ge> l\<^sub>1 \<Longrightarrow> T l > t l" for l using T_gt_t_ae by blast
      obtain l\<^sub>2 :: nat where l2: "l \<ge> l\<^sub>2 \<Longrightarrow> clog l \<ge> ?n" for l
      proof
        fix l :: nat
        assume "l \<ge> 2^?n"
        have "?n > 0" by simp
        then have "?n = clog (2^?n)" by (rule clog_exp[symmetric])
        also have "... \<le> clog l" using clog_mono \<open>l \<ge> 2^?n\<close> ..
        finally show "clog l \<ge> ?n" .
      qed

      let ?l = "max l\<^sub>1 l\<^sub>2"
      have "T ?l \<ge> t ?l" by (rule less_imp_le, rule l1) force
      moreover have "clog ?l \<ge> ?n" by (rule l2) force
      ultimately show ?thesis by (intro that) fast+
    qed

    from \<open>clog l \<ge> ?n\<close> obtain w
      where [simp]: "length w = l" and dec_w[simp]: "dec_TM_pad w = canonical_TM M\<^sub>w"
      by (rule embed_TM_in_len)

    have "w \<in>\<^sub>L L \<longleftrightarrow> w \<notin>\<^sub>L L\<^sub>D" if "alphabet L = UNIV"
    proof -
      from \<open>alphabet L = UNIV\<close> have "w \<in> (alphabet L)*" by blast
      with \<open>decides L\<close> have "wf_input w" by blast
      show ?thesis
      proof (rule iffI)
        assume "w \<in>\<^sub>L L"
        with \<open>decides L\<close> have "\<not> rejects w" unfolding decides_def by blast
        with \<open>wf_input w\<close> show "w \<notin>\<^sub>L L\<^sub>D" by (simp add: L\<^sub>D_def)
      next
        assume "w \<notin>\<^sub>L L\<^sub>D"
        moreover from \<open>T l \<ge> t l\<close> and \<open>time_bounded t\<close> have "time_bounded_word T w"
          by (fold \<open>length w = l\<close>) blast
        ultimately have "\<not> rejects w" using \<open>wf_input w\<close> by (force simp: L\<^sub>D_def)
        with \<open>decides L\<close> show "w \<in>\<^sub>L L" by (auto simp: \<open>alphabet L = UNIV\<close>)
      qed
    qed
    moreover have "L \<noteq> L\<^sub>D" if "alphabet L \<noteq> UNIV" using that unfolding L\<^sub>D_def by force
    ultimately show "L \<noteq> L\<^sub>D" by blast
  qed
  then show "L\<^sub>D \<notin> DTIME t" by blast
qed

theorem time_hierarchy: "L\<^sub>D \<in> DTIME(T) - DTIME(t)" using LD_T and LD_t ..

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

definition strip_sq_pad :: "bool list \<Rightarrow> bool list"
  where "strip_sq_pad w \<equiv> drop (suffix_len w) w"
definition decode_pair_l :: "bool list \<Rightarrow> nat"
  where "decode_pair_l w = length (takeWhile (\<lambda>x. x = True) (rev (strip_sq_pad w)))"
definition decode_pair_x :: "bool list \<Rightarrow> bool list"
  where "decode_pair_x w = rev (tl (dropWhile (\<lambda>x. x = True) (rev (strip_sq_pad w))))"
abbreviation decode_pair :: "bool list \<Rightarrow> nat \<times> bool list"
  where "decode_pair w \<equiv> (decode_pair_l w, decode_pair_x w)"

definition rev_suffix_len :: "bool list \<Rightarrow> nat"
  where "rev_suffix_len w = length w + 9"
definition encode_pair :: "nat \<Rightarrow> bool list \<Rightarrow> bool list"
  where "encode_pair l x = (let w' = x @ [False] @ True \<up> l in
            False \<up> (rev_suffix_len w') @ w')"

lemma encode_pair_altdef:
  "encode_pair l x = False \<up> (length x + l + 10) @ x @ [False] @ True \<up> l"
  unfolding encode_pair_def rev_suffix_len_def Let_def by simp

lemma strip_sq_pad_pair:
  fixes l x
  defines w: "w \<equiv> encode_pair l x"
    and w': "w' \<equiv> x @ [False] @ True \<up> l"
  shows "strip_sq_pad w = w'"
proof -
  let ?lw = "length w" and ?lw' = "length w'"
  have lw: "?lw = 2 * ?lw' + 9" unfolding w w' encode_pair_altdef by simp
  have lwh: "5 + ?lw div 2 = rev_suffix_len w'" unfolding lw rev_suffix_len_def by simp
  show "strip_sq_pad w = w'" unfolding strip_sq_pad_def suffix_len_def lwh
    unfolding w encode_pair_def Let_def w'[symmetric] by simp
qed

lemma decode_encode_pair:
  fixes l x
  defines w: "w \<equiv> encode_pair l x"
  shows "decode_pair w = (l, x)"
proof (unfold prod.inject, intro conjI)
  have rw: "rev (strip_sq_pad w) = True \<up> l @ False # rev x" unfolding w strip_sq_pad_pair by force
  show "decode_pair_l w = l" unfolding decode_pair_l_def rw by (subst takeWhile_tail) auto
  show "decode_pair_x w = x" unfolding decode_pair_x_def rw by (subst dropWhile_append3) auto
qed


lemma pair_adj_sq_eq:
  fixes w
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "decode_pair w' = decode_pair w"
proof -
  let ?sl = "suffix_len w" and ?lw = "length w" and ?lw' = "length w'"
  from len have sh: "shared_MSBs (?lw - ?sl) w w'" unfolding w' by (rule adj_sq_sh_pfx_half)
  from sh have l_eq: "?lw' = ?lw" ..

  from len have "?sl \<le> length w" by (rule suffix_min_len)
  then have "?lw - (?lw - ?sl) = ?sl" by (rule diff_diff_cancel)
  from sh have "drop (?lw' - (?lw - ?sl)) w' = drop (?lw - (?lw - ?sl)) w" ..
  then have "drop ?sl w' = drop ?sl w" unfolding l_eq \<open>?lw - (?lw - ?sl) = ?sl\<close> .
  then have sq_pad_eq: "strip_sq_pad w' = strip_sq_pad w"
    unfolding strip_sq_pad_def suffix_len_def l_eq .
  show "decode_pair w' = decode_pair w"
    unfolding decode_pair_x_def decode_pair_l_def sq_pad_eq ..
qed


subsubsection\<open>Definition\<close>

text\<open>From the proof of Lemma 4.6@{cite rassOwf2017}:

   ``To retain \<open>L\<^sub>D \<inter> SQ \<in> DTIME(T)\<close>, we must choose \<open>T\<close> so large that the decision
    \<open>w \<in> SQ\<close> is possible within the time limit incurred by \<open>T\<close>, so we add \<open>T(n) \<ge> n\<^sup>3\<close>
    to our hypothesis besides Assumption 4.4 (note that we do not need an optimal
    complexity bound here).''\<close>

locale lemma4_6 = TM_Encoding + timed_UTM +
  fixes T t l\<^sub>R :: "nat \<Rightarrow> nat"
  defines "l\<^sub>R \<equiv> \<lambda>n. 4 * n + 11"
  assumes T_dominates_t': "(\<lambda>n. T\<^sub>U ((t \<circ> l\<^sub>R) n) / T n) \<longlonglongrightarrow> 0"
    and t_mono: "mono t"
    and t_cubic: "\<forall>\<^sub>\<infinity>n. t(n) \<ge> n^3"
    and tht_assms': "tht_assms enc_TM is_valid_enc_TM dec_TM enc\<^sub>U is_valid_enc\<^sub>U dec\<^sub>U M\<^sub>U T\<^sub>U T t"
begin

lemma t'_ge_t: "t n \<le> (t \<circ> l\<^sub>R) n" unfolding l\<^sub>R_def comp_def
  using t_mono by (elim monoD) linarith


(* TODO document this approach *)

sublocale tht: tht_assms enc_TM is_valid_enc_TM dec_TM enc\<^sub>U is_valid_enc\<^sub>U dec\<^sub>U M\<^sub>U T\<^sub>U T "t \<circ> l\<^sub>R"
  using tht_assms' unfolding tht_assms_def tht_assms_axioms_def
proof (elim conj_forward)
  show "(\<lambda>n. T\<^sub>U ((t \<circ> l\<^sub>R) n) / T n) \<longlonglongrightarrow> 0" by (fact T_dominates_t')
  show "\<forall>\<^sub>\<infinity>n. n \<le> t n \<Longrightarrow> \<forall>\<^sub>\<infinity>n. n \<le> (t \<circ> l\<^sub>R) n"
  proof ae_nat_elim
    fix n assume "n \<le> t n"
    also note t'_ge_t
    finally show "n \<le> (t \<circ> l\<^sub>R) n" .
  qed
qed

text\<open>Note: this is not intended to replace \<^const>\<open>tht.L\<^sub>D\<close>.
  Instead, the further proof uses the similarity of \<open>L\<^sub>D\<close> and \<open>L\<^sub>D'\<close>
  to prove properties of \<open>L\<^sub>D'\<close> via reduction to \<open>L\<^sub>D\<close>.

  Construction: Given a word \<open>w\<close>.
  Split the word \<open>w\<close> into \<open>(l::nat, x::bool list)\<close> using \<^const>\<open>decode_pair\<close>.
  Define \<open>v\<close> as the \<open>l\<close> most-significant-bits of \<open>x\<close>.
  Remove the arbitrary-length \<open>1\<^sup>+0\<close>-prefix from \<open>v\<close> to retain the pure encoding of \<open>M\<^sub>v\<close>.
  If \<open>M\<^sub>v\<close> rejects \<open>v\<close> within \<open>T(len(x))\<close> steps, \<open>w \<in> L\<^sub>D'\<close> holds.

  Note that in this version, using \<^const>\<open>TM.time_bounded_word\<close> is not possible,
  as the word that determines the time bound (\<open>x\<close>) differs from the input word (\<open>v\<close>).
  (see \<open>TM.time_bounded_word_def\<close>)\<close>

definition L\<^sub>D' :: "bool lang"
  where "L\<^sub>D' \<equiv> Lang UNIV (\<lambda>w.
      let (l, x) = decode_pair w;
          v = drop (length x - l) x;
          M\<^sub>v = dec_TM_pad v in
      TM_decider.rejects M\<^sub>v v \<and> TM.is_final M\<^sub>v (TM.run M\<^sub>v (T (length x)) v)
    )"


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


subsubsection\<open>\<open>L\<^sub>D' \<notin> DTIME(t)\<close> via Reduction from \<open>L\<^sub>D\<close> to \<open>L\<^sub>D'\<close>\<close>

text\<open>Reduce \<open>L\<^sub>D\<close> to \<open>L\<^sub>D'\<close>:
    Given a word \<open>w\<close>, construct its counterpart \<open>w' := 1\<^sup>l0x0\<^sup>l\<^sup>+\<^sup>9\<close>, where \<open>l = length w\<close>.
    Decoding \<open>w'\<close> then yields \<open>(l, w)\<close> which results in the intermediate value \<open>v\<close>
    being equal to \<open>w\<close> in the definition of \<^const>\<open>L\<^sub>D'\<close>.\<close>

definition reduce_LD_LD' :: "bool list \<Rightarrow> bool list"
  where "reduce_LD_LD' w \<equiv> encode_pair (length w) w"

lemma reduce_LD_LD'_len: "length (reduce_LD_LD' w) = 4 * length w + 11"
  unfolding reduce_LD_LD'_def encode_pair_def rev_suffix_len_def by auto

lemma reduce_LD_LD'_correct:
  fixes w
  defines "w' \<equiv> reduce_LD_LD' w"
  shows "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L tht.L\<^sub>D"
proof -
  let ?M\<^sub>w = "dec_TM_pad w"
  interpret TM_decider ?M\<^sub>w .

  have *: "(let (l, x) = decode_pair w';
                  v = drop (length x - l) x;
                 M\<^sub>v = dec_TM_pad v in P M\<^sub>v x v) \<longleftrightarrow> P ?M\<^sub>w w w" for P
    unfolding w'_def reduce_LD_LD'_def decode_encode_pair Let_def prod.case by simp

  have "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> rejects w \<and> time_bounded_word T w"
    unfolding L\<^sub>D'_def member_lang_UNIV mem_Collect_eq * TM.time_bounded_word_def ..
  also have "... \<longleftrightarrow> w \<in>\<^sub>L tht.L\<^sub>D" by (simp add: tht.L\<^sub>D_def Let_def)
  finally show ?thesis .
qed

lemma LD'_t: "L\<^sub>D' \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  let ?f\<^sub>R = reduce_LD_LD'

  assume "L\<^sub>D' \<in> DTIME(t)"
  then have "tht.L\<^sub>D \<in> DTIME(t \<circ> l\<^sub>R)" unfolding comp_def
  proof (rule reduce_DTIME')
    show "\<forall>\<^sub>\<infinity>w. (?f\<^sub>R w \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L tht.L\<^sub>D) \<and> (length (?f\<^sub>R w) \<le> l\<^sub>R (length w))"
    proof (intro eventually_conj eventuallyI)
      fix w
      from reduce_LD_LD'_correct show "?f\<^sub>R w \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L tht.L\<^sub>D" .
      from reduce_LD_LD'_len show "length (?f\<^sub>R w) \<le> l\<^sub>R (length w)" unfolding l\<^sub>R_def by simp
    qed

    from t'_ge_t show "\<forall>\<^sub>\<infinity>x. t x \<le> t (l\<^sub>R x)" by simp

    show "superlinear t" by (fact t_superlinear)

    show "computable_in_time t reduce_LD_LD'" sorry \<comment> \<open>Assume that \<^const>\<open>reduce_LD_LD'\<close> can be computed in time \<open>O(n)\<close>.\<close>
  qed

  moreover from tht.time_hierarchy have "tht.L\<^sub>D \<notin> DTIME(t \<circ> l\<^sub>R)" ..
  ultimately show False by contradiction
qed


subsubsection\<open>\<open>L\<^sub>D' \<in> DTIME(T)\<close> analogous to the THT\<close>

lemma LD'_T: "L\<^sub>D' \<in> DTIME(T)"
proof -
  \<comment> \<open>For now this is a carbon copy of the proof of (@{thm tht.LD_T}).

    Ideally, if the TM constructed in the THT is feasible to construct in Isabelle/HOL,
    and its properties can be proven, the ``difficult parts'' could potentially be reused.
    It may suffice to add a pre-processing step for decoding the input word \<open>w\<close> into \<open>x, v\<close>,
    with \<open>v\<close> being the input for the universal TM part, and \<open>x\<close> the input for the stopwatch.

    Note: it seems feasible to construct this adapter and (if this approach works)
    reduce the \<open>sorry\<close> statements in the THT and this prove into one common assumption;
    the existence of the UTM with only \<open>log\<close> time overhead.\<close>

  define LD'_P where "LD'_P \<equiv> \<lambda>w. let (l, x) = decode_pair w;
          v = drop (length x - l) x;
          M\<^sub>v = dec_TM_pad v in
      TM_decider.rejects M\<^sub>v v \<and> TM.is_final M\<^sub>v (TM.run M\<^sub>v (T (length x)) v)"
  have [simp]: "L\<^sub>D' = Lang UNIV LD'_P" unfolding L\<^sub>D'_def LD'_P_def ..

  obtain M :: "(nat, bool) TM_decider" where "TM.symbols M = UNIV"
    and "TM.time_bounded M T"
    and *: "\<And>w. if LD'_P w then TM_decider.accepts M w else TM_decider.rejects M w" sorry (* probably out of scope *)
  from * have "TM_decider.decides M L\<^sub>D'" unfolding TM_decider.decides_altdef4 \<open>TM.symbols M = UNIV\<close> by simp
  with \<open>TM.time_bounded M T\<close> show "L\<^sub>D' \<in> DTIME(T)" by blast
qed


subsection\<open>The Hard Language \<open>L\<^sub>0\<close>\<close>

text\<open>``\<^bold>\<open>Lemma 4.6.\<close> Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.''\<close>

definition L\<^sub>0 :: "bool lang" where "L\<^sub>0 \<equiv> L\<^sub>D' \<inter>\<^sub>L SQ"


lemma L\<^sub>D'_adj_sq_iff:
  fixes w
  defines "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'"
  unfolding L\<^sub>D'_def member_lang_UNIV w'_def len[THEN pair_adj_sq_eq] ..

lemma L\<^sub>D'_L\<^sub>0_adj_sq_iff:
  fixes w
  defines "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "w' \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'"
  unfolding L\<^sub>0_def w'_def using len[THEN L\<^sub>D'_adj_sq_iff] adj_sq_word_correct by blast

lemma L0_t: "L\<^sub>0 \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>0 \<in> DTIME(t)"
  then have "L\<^sub>D' \<in> DTIME(t)"
  proof (rule reduce_DTIME)
    show "\<forall>\<^sub>\<infinity>w. (adj_sq\<^sub>w w \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D') \<and> (length (adj_sq\<^sub>w w) \<le> length w)"
    proof (intro ae_word_length_finiteI conjI)
      fix w :: "bool list"
      assume len: "length w \<ge> 9"
      then show "adj_sq\<^sub>w w \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'" by (fact L\<^sub>D'_L\<^sub>0_adj_sq_iff)
      from len show "length (adj_sq\<^sub>w w) \<le> length w"
        by (intro eq_imp_le sh_msbD) (fact adj_sq_sh_pfx_half)
    qed

    show "superlinear t" by (fact t_superlinear)

    show "computable_in_time t adj_sq\<^sub>w" sorry
    \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be computed by a TM in time \<open>n\<^sup>3\<close>.\<close>
  qed

  moreover have "L\<^sub>D' \<notin> DTIME(t)" by (fact LD'_t)
  ultimately show False by contradiction
qed


lemma L0_T: "L\<^sub>0 \<in> DTIME(T)"
proof -
  define T' where "T' \<equiv> \<lambda>n. max (T n) (n^3)"

  from LD'_T and SQ_DTIME have "L\<^sub>0 \<in> DTIME(T')" unfolding L\<^sub>0_def T'_def by (fact DTIME_int)
  then have "L\<^sub>0 \<in> DTIME(tcomp (\<lambda>n. 2 * real (T n)))"
  proof (elim DTIME_mono_ae, ae_nat_elim add: T_cubic)
    fix n
    assume "n \<ge> 2" and "n ^ 3 \<le> T n"
    then have "max (T n) (n^3) \<le> max (n + 1) (2 * T n)" by force
    also have "... = tcomp (\<lambda>n. real (2 * T n)) n" unfolding tcomp_nat_simps ..
    also have "... = tcomp (\<lambda>n. 2 * real (T n)) n" by simp
    finally show "T' n \<le> tcomp (\<lambda>n. 2 * real (T n)) n" unfolding T'_def .
  qed
  then have "L\<^sub>0 \<in> DTIME(tcomp T)"
  proof (elim DTIME_speed_up_rev)
    show "superlinear T" by (fact T_superlinear)
  qed simp
  with T_ge_tcomp_T_ae show "L\<^sub>0 \<in> DTIME(T)" by (elim DTIME_mono_ae) ae_nat_elim
qed


theorem L0_time_hierarchy: "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" using L0_T L0_t ..

theorem dens_L0: "dens L\<^sub>0 n \<le> dsqrt n"
proof -
  have "dens L\<^sub>0 n = dens (L\<^sub>D' \<inter>\<^sub>L SQ) n" unfolding L\<^sub>0_def ..
  also have "... \<le> dens SQ n" by (rule dens_intersect_le)
  also have "... = dsqrt n" by (rule dens_SQ)
  finally show ?thesis .
qed

lemmas lemma4_6 = L0_time_hierarchy dens_L0

end \<comment> \<open>context \<^locale>\<open>lemma4_6\<close>\<close>

end
