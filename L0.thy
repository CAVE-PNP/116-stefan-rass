section\<open>The Time Hierarchy Theorem and the Language \<open>L\<^sub>0\<close>\<close>

theory L0
  imports SQ Complexity
begin


subsection\<open>The Time Hierarchy Theorem\<close>

locale tht_assms =
  fixes T t :: "nat \<Rightarrow> nat"
  assumes fully_tconstr_T: "fully_tconstr T"

  \<comment> \<open>This assumption represents the statements containing \<open>lim\<close> @{cite rassOwf2017} and \<open>lim inf\<close> @{cite hopcroftAutomata1979}.
      \<^const>\<open>LIMSEQ\<close> (\<^term>\<open>X \<longlonglongrightarrow> x\<close>) was chosen, as it seems to match the intended meaning
      (@{thm LIMSEQ_def lim_sequentially}).\<close>
    and T_dominates_t: "(\<lambda>n. t n * log 2 (t n) / T n) \<longlonglongrightarrow> 0"
  \<comment> \<open>Additionally, \<open>T n\<close> is assumed not to be zero since in Isabelle,
      \<open>x / 0 = 0\<close> holds over the reals (@{thm division_ring_divide_zero}).
      Thus, the above assumption would trivially hold for \<open>T(n) = 0\<close>.\<close>
    and T_not_0: "MOST n. T n \<noteq> 0"

  \<comment> \<open>The following assumption is not found in @{cite rassOwf2017} or the primary source @{cite hopcroftAutomata1979},
    but is taken from the AAU lecture slides of \<^emph>\<open>Algorithms and Complexity Theory\<close>.
    \<^footnote>\<open>TODO properly cite this\<close>
    It patches a hole that allows one to prove \<^const>\<open>False\<close> from the Time Hierarchy Theorem below
    (\<open>time_hierarchy\<close>).
    This is demonstrated in \<^file>\<open>examples/THT_inconsistencies_MWE.thy\<close>.\<close>
    and t_min: "MOST n. n \<le> t n"
begin

lemma T_ge_t_log_t_MOST:
  fixes c :: real
  assumes "c \<ge> 0"
  shows "MOST n. c * t n * log 2 (t n) < T n"
proof (cases "c = 0")
  assume "c = 0"
  from T_not_0 show ?thesis unfolding \<open>c = 0\<close> by (MOST_intro) linarith
next
  assume "c \<noteq> 0"
  with \<open>c \<ge> 0\<close> have "c > 0" by simp
  from T_not_0 have "MOST n. real (T n) \<noteq> 0" by (MOST_intro) linarith
  with T_dominates_t and \<open>c > 0\<close> have "MOST n. c * \<bar>t n * log 2 (t n)\<bar> < \<bar>real (T n)\<bar>"
    by (subst (asm) dominates_altdef) presburger+

  then show "MOST n. c * t n * log 2 (t n) < T n"
  proof (MOST_intro)
    fix n
    from abs_ge_self and \<open>c \<ge> 0\<close> have "c * x \<le> c * \<bar>x\<bar>" for x by (rule mult_left_mono)
    then have "c * t n * log 2 (t n) \<le> c * \<bar>t n * log 2 (t n)\<bar>" by (subst mult.assoc)
    also assume "... < \<bar>real (T n)\<bar>"
    also have "... = T n" by simp
    finally show "c * t n * log 2 (t n) < T n" .
  qed
qed

lemma T_gt_t_MOST: "MOST n. T n > t n"
proof -
  from T_ge_t_log_t_MOST[of 1] have "MOST n. t n * log 2 (t n) < T n" unfolding mult_1 by argo
  with t_min show "MOST n. T n > t n"
  proof (MOST_intro)
    fix n :: nat
    assume "n \<ge> 2" also assume "t n \<ge> n"
    finally have "t n \<ge> 2" .
    then have "log 2 (t n) \<ge> 1" by force

    with \<open>t n \<ge> 2\<close> have "t n \<le> t n * log 2 (t n)" by simp
    also assume "... < T n"
    finally show "t n < T n" by simp
  qed
qed


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  ``The `diagonal-language' \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>L\<^sub>D := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.''
  @{cite rassOwf2017}\<close>

definition L\<^sub>D :: "lang"
  where LD_def[simp]: "L\<^sub>D \<equiv> {w. let M\<^sub>w = TM_decode_pad w in
                  rejects M\<^sub>w w \<and> time_bounded_word T M\<^sub>w w}"

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

  define LD_P where "LD_P \<equiv> \<lambda>w. let M\<^sub>w = TM_decode_pad w in
    rejects M\<^sub>w w \<and> time_bounded_word T M\<^sub>w w"

  obtain M where "time_bounded T M"
    and *: "\<And>w. if LD_P w then accepts M w else rejects M w" sorry \<comment> \<open>probably out of scope\<close>
  have "decides M L\<^sub>D" unfolding decides_altdef4
    unfolding LD_def mem_Collect_eq LD_P_def[symmetric] using * ..
  with \<open>time_bounded T M\<close> show "L\<^sub>D \<in> DTIME(T)" by blast
qed

lemma LD_t: "L\<^sub>D \<notin> DTIME(t)"
proof -
  have "L \<noteq> L\<^sub>D" if "L \<in> DTIME(t)" for L
  proof -
    from \<open>L \<in> DTIME(t)\<close> obtain M\<^sub>w where "decides M\<^sub>w L" and "time_bounded t M\<^sub>w" and "composable_tm0 M\<^sub>w" ..
    define w' where "w' = encode_TM M\<^sub>w"

    let ?n = "length (encode_TM M\<^sub>w) + 2"
    obtain l where "T(2*l) \<ge> t(2*l)" and "clog l \<ge> ?n"
    proof -
      obtain l\<^sub>1 :: nat where l1: "l \<ge> l\<^sub>1 \<Longrightarrow> T l > t l" for l using T_gt_t_MOST by blast
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
      have "T (2*?l) \<ge> t (2*?l)" by (rule less_imp_le, rule l1) force
      moreover have "clog ?l \<ge> ?n" by (rule l2) force
      ultimately show ?thesis by (intro that) fast+
    qed

    obtain w where "length w = l" and dec_w: "TM_decode_pad w = M\<^sub>w"
      using \<open>composable_tm0 M\<^sub>w\<close> \<open>clog l \<ge> ?n\<close> by (rule embed_TM_in_len)

    have "w \<in> L \<longleftrightarrow> w \<notin> L\<^sub>D"
    proof
      assume "w \<in> L"
      moreover from \<open>decides M\<^sub>w L\<close> have "w \<notin> L \<longleftrightarrow> rejects M\<^sub>w w" unfolding decides_def by blast
      ultimately have "\<not> rejects M\<^sub>w w" by blast
      then show "w \<notin> L\<^sub>D" unfolding LD_def mem_Collect_eq dec_w by presburger
    next
      assume "w \<notin> L\<^sub>D"
      moreover have "time_bounded_word T M\<^sub>w w"
      proof (rule time_bounded_word_mono)
        from \<open>T(2*l) \<ge> t(2*l)\<close> show "real (T (tape_size <w>\<^sub>t\<^sub>p)) \<ge> real (t (tape_size <w>\<^sub>t\<^sub>p))"
          unfolding tape_size_input \<open>length w = l\<close> by (rule of_nat_mono)
        from \<open>time_bounded t M\<^sub>w\<close> show "time_bounded_word t M\<^sub>w w" ..
      qed
      ultimately have "\<not> rejects M\<^sub>w w" unfolding LD_def dec_w mem_Collect_eq Let_def by blast
      with \<open>decides M\<^sub>w L\<close> show "w \<in> L" unfolding decides_def by blast
    qed
    then show "L \<noteq> L\<^sub>D" by blast
  qed
  then show "L\<^sub>D \<notin> DTIME(t)" by blast
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

definition strip_sq_pad :: "word \<Rightarrow> word"
  where "strip_sq_pad w \<equiv> drop (suffix_len w) w"
definition decode_pair_l :: "word \<Rightarrow> nat"
  where "decode_pair_l w = length (takeWhile (\<lambda>x. x = True) (rev (strip_sq_pad w)))"
definition decode_pair_x :: "word \<Rightarrow> word"
  where "decode_pair_x w = rev (tl (dropWhile (\<lambda>x. x = True) (rev (strip_sq_pad w))))"
abbreviation decode_pair :: "word \<Rightarrow> nat \<times> word"
  where "decode_pair w \<equiv> (decode_pair_l w, decode_pair_x w)"

definition rev_suffix_len :: "word \<Rightarrow> nat"
  where "rev_suffix_len w = length w + 9"
definition encode_pair :: "nat \<Rightarrow> word \<Rightarrow> word"
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

locale lemma4_6 =
  fixes T t l\<^sub>R :: "nat \<Rightarrow> nat"
  defines "l\<^sub>R \<equiv> \<lambda>n. 4 * n + 11"
  assumes T_dominates_t': "(\<lambda>n. (t \<circ> l\<^sub>R) n * log 2 ((t \<circ> l\<^sub>R) n) / T n) \<longlonglongrightarrow> 0"
    and t_mono: "mono t"
    and t_cubic: "MOST n. t(n) \<ge> n^3"
    and tht_assms: "tht_assms T t" (* TODO inline when finalized *)
begin

lemma t'_ge_t: "t n \<le> (t \<circ> l\<^sub>R) n" unfolding l\<^sub>R_def comp_def
  using t_mono by (elim monoD) linarith

(* TODO document this approach *)

sublocale tht: tht_assms T "t \<circ> l\<^sub>R"
  using tht_assms and T_dominates_t'
proof (unfold tht_assms_def, elim conjE, intro conjI)
  assume "MOST n. n \<le> t n"
  thus "MOST n. n \<le> (t \<circ> l\<^sub>R) n"
  proof (MOST_intro)
    fix n assume "n \<le> t n"
    also note t'_ge_t
    finally show "n \<le> (t \<circ> l\<^sub>R) n" .
  qed
qed


text\<open>Note: this is not intended to replace \<^const>\<open>tht.L\<^sub>D\<close>.
  Instead, the further proof uses the similarity of \<open>L\<^sub>D\<close> and \<open>L\<^sub>D'\<close>
  to prove properties of \<open>L\<^sub>D'\<close> via reduction to \<open>L\<^sub>D\<close>.

  Construction: Given a word \<open>w\<close>.
  Split the word \<open>w\<close> into \<open>(l::nat, x::word)\<close> using \<^const>\<open>decode_pair\<close>.
  Define \<open>v\<close> as the \<open>l\<close> most-significant-bits of \<open>x\<close>.
  Remove the arbitrary-length \<open>1\<^sup>+0\<close>-prefix from \<open>v\<close> to retain the pure encoding of \<open>M\<^sub>v\<close>.
  If \<open>M\<^sub>v\<close> rejects \<open>v\<close> within \<open>T(len(x))\<close> steps, \<open>w \<in> L\<^sub>D'\<close> holds.

  Note that in this version, using \<^const>\<open>time_bounded_word\<close> is not possible,
  as the word that determines the time bound (\<open>x\<close>) differs from the input word (\<open>v\<close>).
  For simplicity, a predicate similar to the shorter but equivalent
  term for \<^const>\<open>time_bounded_word\<close> is used (@{thm time_bounded_altdef}).\<close>

definition L\<^sub>D' :: lang
  where LD'_def: "L\<^sub>D' \<equiv> {w.
      let (l, x) = decode_pair w;
          v = drop (length x - l) x;
          M\<^sub>v = TM_decode_pad v in
      rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x))
    }"


subsubsection\<open>Preliminaries\<close>

lemma T_cubic: "MOST n. T(n) \<ge> n^3"
proof (MOST_intro add: t_cubic tht.T_gt_t_MOST)
  fix n assume "n^3 \<le> t n"
  also from t'_ge_t have "... \<le> (t \<circ> l\<^sub>R) n" .
  also assume "... < T n"
  finally show "T(n) \<ge> n^3" by (fact order_less_imp_le)
qed

lemma t_superlinear: "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N"
proof (intro allI, MOST_intro add: t_cubic)
  fix N :: real and n :: nat
  assume n_min: "n \<ge> max 1 (nat \<lceil>N\<rceil>)" and "t(n) \<ge> n^3"

  from n_min have "n \<ge> 1" by (rule max.boundedE)

  from n_min have "N \<le> n" by simp
  also from \<open>n \<ge> 1\<close> have "... \<le> n^2" using pos2 by (intro of_nat_mono self_le_power) auto
  also have "n^2 \<le> t(n)/n"
  proof (subst pos_le_divide_eq)
    from \<open>n \<ge> 1\<close> show "0 < real n" by force
    have "n^2 * n = n^3" by algebra
    also note \<open>n^3 \<le> t(n)\<close>
    finally show "n\<^sup>2 * real n \<le> t n" by (fold of_nat_mult) linarith
  qed
  finally show "t(n)/n \<ge> N" .
qed


subsubsection\<open>\<open>L\<^sub>D' \<notin> DTIME(t)\<close> via Reduction from \<open>L\<^sub>D\<close> to \<open>L\<^sub>D'\<close>\<close>

text\<open>Reduce \<open>L\<^sub>D\<close> to \<open>L\<^sub>D'\<close>:
    Given a word \<open>w\<close>, construct its counterpart \<open>w' := 1\<^sup>l0x0\<^sup>l\<^sup>+\<^sup>9\<close>, where \<open>l = length w\<close>.
    Decoding \<open>w'\<close> then yields \<open>(l, w)\<close> which results in the intermediate value \<open>v\<close>
    being equal to \<open>w\<close> in the definition of \<^const>\<open>L\<^sub>D'\<close>.\<close>

definition reduce_LD_LD' :: "word \<Rightarrow> word"
  where "reduce_LD_LD' w \<equiv> encode_pair (length w) w"

lemma reduce_LD_LD'_len: "length (reduce_LD_LD' w) = 4 * length w + 11"
  unfolding reduce_LD_LD'_def encode_pair_def rev_suffix_len_def by auto

lemma reduce_LD_LD'_correct:
  fixes w
  defines w: "w' \<equiv> reduce_LD_LD' w"
  shows "w' \<in> L\<^sub>D' \<longleftrightarrow> w \<in> tht.L\<^sub>D"
proof -
  let ?M\<^sub>w = "TM_decode_pad w"
  have "w' \<in> L\<^sub>D' \<longleftrightarrow> rejects ?M\<^sub>w w \<and> time_bounded_word T ?M\<^sub>w w"
    unfolding LD'_def w reduce_LD_LD'_def mem_Collect_eq decode_encode_pair
    unfolding diff_self_eq_0 drop_0 Let_def prod.case unfolding time_bounded_altdef ..
  also have "... \<longleftrightarrow> w \<in> tht.L\<^sub>D" unfolding tht.LD_def mem_Collect_eq Let_def ..
  finally show ?thesis .
qed


lemma LD'_t: "L\<^sub>D' \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  let ?f\<^sub>R = reduce_LD_LD'

  assume "L\<^sub>D' \<in> DTIME(t)"
  then have "tht.L\<^sub>D \<in> DTIME(t \<circ> l\<^sub>R)" unfolding comp_def
  proof (rule reduce_DTIME')
    show "MOST w. (?f\<^sub>R w \<in> L\<^sub>D' \<longleftrightarrow> w \<in> tht.L\<^sub>D) \<and> (length (?f\<^sub>R w) \<le> l\<^sub>R (length w))"
    proof (intro eventually_conj eventuallyI)
      fix w
      from reduce_LD_LD'_correct show "?f\<^sub>R w \<in> L\<^sub>D' \<longleftrightarrow> w \<in> tht.L\<^sub>D" .
      from reduce_LD_LD'_len show "length (?f\<^sub>R w) \<le> l\<^sub>R (length w)" unfolding l\<^sub>R_def by simp
    qed

    from t'_ge_t show "MOST x. real (t x) \<le> real (t (l\<^sub>R x))"
      unfolding comp_def by (intro eventuallyI of_nat_mono)

    show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N" by (fact t_superlinear)

    show "computable_in_time t reduce_LD_LD'" sorry \<comment> \<open>Assume that \<^const>\<open>reduce_LD_LD'\<close> can be computed in time \<open>O(n)\<close>.\<close>
  qed

  moreover from tht.time_hierarchy have "tht.L\<^sub>D \<notin> DTIME(t \<circ> l\<^sub>R)" ..
  ultimately show False by contradiction
qed


subsubsection\<open>\<open>L\<^sub>D' \<in> DTIME(T)\<close> analogous to the THT\<close>

lemma LD'_T: "L\<^sub>D' \<in> DTIME(T)"
proof -
  \<comment> \<open>For now this is a carbon copy of the ``proof'' of this part of the THT (@{thm tht.time_hierarchy}).

    Ideally, if the TM constructed in the THT is feasible to construct in Isabelle/HOL,
    and its properties can be proven, the ``difficult parts'' could potentially be reused.
    It may suffice to add a pre-processing step for decoding the input word \<open>w\<close> into \<open>x, v\<close>,
    with \<open>v\<close> being the input for the universal TM part, and \<open>x\<close> the input for the stopwatch.

    Note: it seems feasible to construct this adapter and (if this approach works)
    reduce the \<open>sorry\<close> statements in the THT and this prove into one common assumption;
    the existence of the UTM with only \<open>log\<close> time overhead.
    However, such a construction is not sensible for the current TM model,
    as multiple tapes and arbitrary alphabets would be necessary required.\<close>

  define LD'_P where "LD'_P \<equiv> \<lambda>w. let (l, x) = decode_pair w;
          v = drop (length x - l) x;
          M\<^sub>v = TM_decode_pad v in
      rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x))"

  obtain M where "time_bounded T M"
    and *: "\<And>w. if LD'_P w then accepts M w else rejects M w" sorry (* probably out of scope *)
  have "decides M L\<^sub>D'" unfolding decides_altdef4
    unfolding LD'_def mem_Collect_eq LD'_P_def[symmetric] using * ..
  with \<open>time_bounded T M\<close> show "L\<^sub>D' \<in> DTIME(T)" by blast
qed


subsection\<open>The Hard Language \<open>L\<^sub>0\<close>\<close>

text\<open>``\<^bold>\<open>Lemma 4.6.\<close> Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.''\<close>

definition L\<^sub>0 :: lang
  where L0_def: "L\<^sub>0 \<equiv> L\<^sub>D' \<inter> SQ"


lemma LD'_adj_sq_iff:
  fixes w
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "w' \<in> L\<^sub>D' \<longleftrightarrow> w \<in> L\<^sub>D'"
  unfolding LD'_def mem_Collect_eq w' len[THEN pair_adj_sq_eq] ..

lemma LD'_L0_adj_sq_iff:
  fixes w
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "w' \<in> L\<^sub>0 \<longleftrightarrow> w \<in> L\<^sub>D'"
  unfolding L0_def w' using len[THEN LD'_adj_sq_iff] adj_sq_word_correct by blast

lemma L0_t: "L\<^sub>0 \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>0 \<in> DTIME(t)"
  then have "L\<^sub>D' \<in> DTIME(t)"
  proof (rule reduce_DTIME)
    show "MOST w. (adj_sq\<^sub>w w \<in> L\<^sub>0) = (w \<in> L\<^sub>D') \<and> length (adj_sq\<^sub>w w) \<le> length w"
    proof (intro MOST_word_lengthI exI allI impI conjI)
      fix w :: word assume len: "length w \<ge> 9"
      from len show "adj_sq\<^sub>w w \<in> L\<^sub>0 \<longleftrightarrow> w \<in> L\<^sub>D'" by (fact LD'_L0_adj_sq_iff)
      from len show "length (adj_sq\<^sub>w w) \<le> length w"
        by (intro eq_imp_le sh_msbD) (fact adj_sq_sh_pfx_half)
    qed

    show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N" by (fact t_superlinear)

    show "computable_in_time t adj_sq\<^sub>w" sorry \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be computed in time \<open>O(t(n))\<close>.\<close>
  qed

  moreover have "L\<^sub>D' \<notin> DTIME(t)" by (fact LD'_t)
  ultimately show False by contradiction
qed


lemma SQ_DTIME: "SQ \<in> DTIME(\<lambda>n. n^3)" sorry

lemma L0_T: "L\<^sub>0 \<in> DTIME(T)"
proof -
  let ?T' = "\<lambda>n. real (max (T n) (n^3))"

  from LD'_T and SQ_DTIME have "L\<^sub>0 \<in> DTIME(?T')"
    unfolding L0_def of_nat_max by (rule DTIME_int)
  then show "L\<^sub>0 \<in> DTIME(T)"
  proof (rule DTIME_mono_MOST, MOST_intro add: T_cubic)
    fix n :: nat
    have "n \<le> n^3" by simp
    also assume "n^3 \<le> T(n)"
    finally have "T(n) \<ge> n" .

    from \<open>T(n) \<ge> n^3\<close> have *: "max (T n) (n ^ 3) = T n" by simp
    from \<open>T(n) \<ge> n\<close> show "T n \<ge> ?T' n" unfolding * by simp
  qed
qed


theorem L0_time_hierarchy: "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" using L0_T L0_t ..

theorem dens_L0: "dens L\<^sub>0 n \<le> dsqrt n"
proof -
  have "dens L\<^sub>0 n = dens (L\<^sub>D' \<inter> SQ) n" unfolding L0_def ..
  also have "... \<le> dens SQ n" by (subst Int_commute) (rule dens_intersect_le)
  also have "... = dsqrt n" by (rule dens_SQ)
  finally show ?thesis .
qed

lemmas lemma4_6 = L0_time_hierarchy dens_L0

end \<comment> \<open>context \<^locale>\<open>lemma4_6\<close>\<close>


lemma lemma4_6:
  fixes T t :: "nat \<Rightarrow> nat"
  defines "l\<^sub>R \<equiv> \<lambda>n. 4 * n + 11"
  defines "t' \<equiv> t \<circ> l\<^sub>R"
  assumes "fully_tconstr T"
    and T_dominates_t': "(\<lambda>n. t' n * log 2 (t' n) / T n) \<longlonglongrightarrow> 0"
    and T_not_0: "MOST n. T n \<noteq> 0"
    and t_cubic: "MOST n. t n \<ge> n^3"
    and "mono t"
  defines L0: "L\<^sub>0 \<equiv> lemma4_6.L\<^sub>0 T"
  shows "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" and "dens L\<^sub>0 n \<le> dsqrt n"
proof -
  let ?t' = "t \<circ> (\<lambda>n. 4 * n + 11)"

  have "lemma4_6 T t"
  proof (unfold_locales)
    show "(\<lambda>n. ?t' n * log 2 (?t' n) / T n) \<longlonglongrightarrow> 0" by (fold t'_def l\<^sub>R_def) fact
    show "mono t"
      and "fully_tconstr T"
      and "MOST n. T n \<noteq> 0"
      and "MOST n. t n \<ge> n^3"
      by fact+

    from \<open>MOST n. t n \<ge> n^3\<close> show t_min: "MOST n. t n \<ge> n"
    proof (MOST_intro)
      fix n :: nat
      have "n \<le> n^3" by simp
      also assume "n^3 \<le> t n"
      finally show "t n \<ge> n" .
    qed

    let ?T = "\<lambda>n. real (T n)"
    from T_not_0 have *: "MOST n. ?T n \<noteq> 0" by simp

    with T_dominates_t' show "(\<lambda>n. t n * log 2 (t n) / T n) \<longlonglongrightarrow> 0"
    proof (rule dominates_mono)
      from t_min show "MOST n. \<bar>t n * log 2 (t n)\<bar> \<le> \<bar>t' n * log 2 (t' n)\<bar>"
      proof (MOST_intro)
        fix n :: nat
        assume "n \<ge> 2" and "n \<le> t n"
        then have "t n \<ge> 2" by linarith

        also have t_t': "t n \<le> t' n" unfolding l\<^sub>R_def t'_def comp_def
          using \<open>mono t\<close> by (elim monoD) linarith
        finally have "t' n \<ge> 2" .

        with t_t' \<open>t n \<ge> 2\<close> have log_t_t': "log 2 (t n) \<le> log 2 (t' n)"
          by (subst log_le_cancel_iff) linarith+

        have "\<bar>f n * log 2 (f n)\<bar> = f n * log 2 (f n)" if "f n \<ge> 2" for f :: "nat \<Rightarrow> nat"
          using that by force
        note ** = this[of t, OF \<open>t n \<ge> 2\<close>] this[of t', OF \<open>t' n \<ge> 2\<close>]

        from t_t' have "t n * log 2 (t n) \<le> t' n * log 2 (t n)"
          using \<open>t n \<ge> 2\<close> by (intro mult_right_mono of_nat_mono) auto
        also from log_t_t' have "... \<le> t' n * log 2 (t' n)"
          using \<open>t n \<ge> 2\<close> by (intro mult_left_mono) linarith+
        finally
        show "\<bar>t n * log 2 (t n)\<bar> \<le> \<bar>t' n * log 2 (t' n)\<bar>" unfolding ** .
      qed
    qed
  qed
  then show "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" and "dens L\<^sub>0 n \<le> dsqrt n"
    unfolding L0 by (fact lemma4_6.lemma4_6)+
qed

thm_oracles lemma4_6 \<comment> \<open>shows \<open>skip_proof\<close> (the \<^emph>\<open>oracle\<close> used by \<open>sorry\<close>)\<close>


end
