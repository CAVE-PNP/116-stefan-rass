section\<open>Alternative \<open>L\<^sub>D\<close> (Bridge to Lemma 4.6)\<close>

theory LD_Issues
  imports L0
begin


subsection\<open>Encoding\<close>

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


subsection\<open>Definition\<close>

locale tht_assms' =
  fixes T t l\<^sub>R :: "nat \<Rightarrow> nat"
  defines "l\<^sub>R \<equiv> \<lambda>n. 4 * n + 11"
  assumes T_dominates_t': "(\<lambda>n. (t \<circ> l\<^sub>R) n * log 2 ((t \<circ> l\<^sub>R) n) / T n) \<longlonglongrightarrow> 0"
    and t_mono': "mono t"
    and tht_assms: "tht_assms T t" (* TODO inline when finalized *)
begin

lemma t'_ge_t: "t n \<le> (t \<circ> l\<^sub>R) n" unfolding l\<^sub>R_def comp_def
  using t_mono' by (elim monoD) linarith

sublocale tht_assms T "t \<circ> l\<^sub>R"
  using tht_assms and T_dominates_t'
proof (unfold tht_assms_def, elim conjE, intro conjI)
  assume "ae n. n \<le> t n"
  thus "ae n. n \<le> (t \<circ> l\<^sub>R) n"
  proof (ae_intro_nat)
    fix n assume "n \<le> t n"
    also note t'_ge_t
    finally show "n \<le> (t \<circ> l\<^sub>R) n" .
  qed
qed


text\<open>Note: this is not intended to replace \<^const>\<open>L\<^sub>D\<close>.
  Instead, the further proof uses the similarity of \<open>L\<^sub>D\<close> and \<open>L\<^sub>D''\<close>
  to prove properties of \<open>L\<^sub>D''\<close> via reduction to \<open>L\<^sub>D\<close>.

  Construction: Given a word \<open>w\<close>.
  Split the word \<open>w\<close> into \<open>(l::nat, x::word)\<close> using \<^const>\<open>decode_pair\<close>.
  Define \<open>v\<close> as the \<open>l\<close> most-significant-bits of \<open>x\<close>.
  Remove the arbitrary-length \<open>1\<^sup>+0\<close>-prefix from \<open>v\<close> to retain the pure encoding of \<open>M\<^sub>v\<close>.
  If \<open>M\<^sub>v\<close> rejects \<open>v\<close> within \<open>T(len(x))\<close> steps, \<open>w \<in> L\<^sub>D''\<close> holds.

  Note that in this version, using \<^const>\<open>time_bounded_word\<close> is not possible,
  as the word that determines the time bound (\<open>x\<close>) differs from the input word (\<open>v\<close>).
  The alternative version shown in @{thm time_bounded_altdef} is used for simplicity.\<close>

definition L\<^sub>D'' :: lang
  where "L\<^sub>D'' \<equiv> {w.
      let (l, x) = decode_pair w;
          v = drop (length x - l) x;
          M\<^sub>v = TM_decode_pad v in
      rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x))
    }"

definition L\<^sub>0'' :: lang
  where "L\<^sub>0'' \<equiv> L\<^sub>D'' \<inter> SQ"


lemma L\<^sub>D''_adj_sq_iff:
  fixes w
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "w' \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D''"
  unfolding L\<^sub>D''_def mem_Collect_eq w' len[THEN pair_adj_sq_eq] ..

lemma L\<^sub>D''_L\<^sub>0''_adj_sq_iff:
  fixes w
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "w' \<in> L\<^sub>0'' \<longleftrightarrow> w \<in> L\<^sub>D''"
  unfolding L\<^sub>0''_def w' using len[THEN L\<^sub>D''_adj_sq_iff] adj_sq_word_correct by blast


subsection\<open>\<open>L\<^sub>D'' \<notin> DTIME(t)\<close> via Reduction from \<open>L\<^sub>D\<close> to \<open>L\<^sub>D''\<close>\<close>

text\<open>Reduce \<open>L\<^sub>D\<close> to \<open>L\<^sub>D''\<close>:
    Given a word \<open>w\<close>, construct its counterpart \<open>w' := 1\<^sup>l0x0\<^sup>l\<^sup>+\<^sup>9\<close>, where \<open>l = length w\<close>.
    Decoding \<open>w'\<close> then yields \<open>(l, w)\<close> which results in the intermediate value \<open>v\<close>
    being equal to \<open>w\<close> in the definition of \<^const>\<open>L\<^sub>D''\<close>.\<close>

definition reduce_LD_LD'' :: "word \<Rightarrow> word"
  where "reduce_LD_LD'' w \<equiv> encode_pair (length w) w"

lemma reduce_LD_LD''_len: "length (reduce_LD_LD'' w) = 4 * length w + 11"
  unfolding reduce_LD_LD''_def encode_pair_def rev_suffix_len_def by auto

lemma reduce_LD_LD''_correct:
  fixes w
  defines w'': "w'' \<equiv> reduce_LD_LD'' w"
  shows "w'' \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D"
proof -
  let ?M\<^sub>w = "TM_decode_pad w"
  have "w'' \<in> L\<^sub>D'' \<longleftrightarrow> rejects ?M\<^sub>w w \<and> time_bounded_word T ?M\<^sub>w w"
    unfolding L\<^sub>D''_def w'' reduce_LD_LD''_def mem_Collect_eq decode_encode_pair
    unfolding diff_self_eq_0 drop_0 Let_def prod.case unfolding time_bounded_altdef ..
  also have "... \<longleftrightarrow> w \<in> L\<^sub>D" unfolding LD_def mem_Collect_eq Let_def ..
  finally show ?thesis .
qed


end \<comment> \<open>context \<^locale>\<open>tht_assms'\<close>\<close>
locale tht_sq_assms' = tht_assms' +
  assumes t_cubic': "ae n. t(n) \<ge> n^3"
begin

lemma mono_comp:
  assumes "mono f" and "mono g"
  shows "mono (f \<circ> g)"
  using assms by (simp add: mono_def) 

lemma l\<^sub>R_mono: "mono l\<^sub>R" unfolding l\<^sub>R_def by (intro monoI) simp
lemma t_l\<^sub>R_mono: "mono (t \<circ> l\<^sub>R)" using t_mono' l\<^sub>R_mono by (rule mono_comp)

sublocale tht_sq_assms T "t \<circ> l\<^sub>R"
  using t_l\<^sub>R_mono tht_assms_axioms
proof (unfold tht_sq_assms_def tht_sq_assms_axioms_def, intro conjI)
  from t_cubic' show "ae n. (t \<circ> l\<^sub>R) n \<ge> n^3"
  proof (ae_intro_nat)
    fix n assume "n^3 \<le> t(n)"
    also note t'_ge_t
    finally show "(t \<circ> l\<^sub>R) n \<ge> n^3" .
  qed
qed

lemma t_superlinear': "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N"
proof (intro allI, ae_intro_nat add: t_cubic')
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


lemma L\<^sub>D''_t: "L\<^sub>D'' \<notin> DTIME(t)" \<comment> \<open>The proof is similar to that of @{thm tht_sq_assms.L0_t}.\<close>
proof (rule ccontr, unfold not_not)
  let ?f\<^sub>R = reduce_LD_LD''

  assume "L\<^sub>D'' \<in> DTIME(t)"
  then have "L\<^sub>D \<in> DTIME(t \<circ> l\<^sub>R)" unfolding comp_def
  proof (rule reduce_DTIME')
    show "ae w. (?f\<^sub>R w \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D) \<and> (length (?f\<^sub>R w) \<le> l\<^sub>R (length w))"
    proof (intro ae_conjI ae_everyI)
      fix w
      from reduce_LD_LD''_correct show "?f\<^sub>R w \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D" .
      from reduce_LD_LD''_len show "length (?f\<^sub>R w) \<le> l\<^sub>R (length w)" unfolding l\<^sub>R_def by simp
    qed

    from t'_ge_t show "ae x. real (t x) \<le> real (t (l\<^sub>R x))"
      unfolding comp_def by (intro ae_everyI of_nat_mono)

    show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N" by (fact t_superlinear')

    show "computable_in_time t reduce_LD_LD''" sorry \<comment> \<open>Assume that \<^const>\<open>reduce_LD_LD''\<close> can be computed in time \<open>O(n)\<close>.\<close>
  qed

  moreover from time_hierarchy have "L\<^sub>D \<notin> DTIME(t \<circ> l\<^sub>R)" ..
  ultimately show False by contradiction
qed


subsection\<open>\<open>L\<^sub>D'' \<in> DTIME(T)\<close> via Reduction from \<open>L\<^sub>D''\<close> to \<open>L\<^sub>D\<close>\<close>

lemma L\<^sub>D''_T: "L\<^sub>D'' \<in> DTIME(T)"
proof -
  \<comment> \<open>For now this is a carbon copy of the ``proof'' of this part of the THT (@{thm time_hierarchy}).

    Ideally, if the TM constructed in the THT is feasible to construct in Isabelle/HOL,
    and its properties can be proven, the ``difficult parts'' could potentially be reused.
    It may suffice to add a pre-processing step for decoding the input word \<open>w\<close> into \<open>x, v\<close>,
    with \<open>v\<close> being the input for the universal TM part, and \<open>x\<close> the input for the stopwatch.

    Note: it seems feasible to construct this adapter and (if this approach works)
    reduce the \<open>sorry\<close> statements in the THT and this prove into one common assumption;
    the existence of the UTM with only \<open>log\<close> time overhead.
    However, such a construction is not sensible for the current TM model,
    as multiple tapes and arbitrary alphabets would be necessary required.\<close>

  define L\<^sub>D''_P where "L\<^sub>D''_P \<equiv> \<lambda>w. let (l, x) = decode_pair w;
          v = drop (length x - l) x;
          M\<^sub>v = TM_decode_pad v in
      rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x))"

  obtain M where "time_bounded T M"
    and *: "\<And>w. if L\<^sub>D''_P w then accepts M w else rejects M w" sorry (* probably out of scope *)
  have "decides M L\<^sub>D''" unfolding decides_altdef4
    unfolding L\<^sub>D''_def mem_Collect_eq L\<^sub>D''_P_def[symmetric] using * ..
  with \<open>time_bounded T M\<close> show "L\<^sub>D'' \<in> DTIME(T)" by blast
qed


text\<open>``\<^bold>\<open>Lemma 4.6.\<close> Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.''\<close>

lemma L0''_t: "L\<^sub>0'' \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>0'' \<in> DTIME(t)"
  then have "L\<^sub>D'' \<in> DTIME(t)"
  proof (rule reduce_DTIME)
    show "almost_everywhere (\<lambda>w. (adj_sq\<^sub>w w \<in> L\<^sub>0'') = (w \<in> L\<^sub>D'') \<and> length (adj_sq\<^sub>w w) \<le> length w)"
    proof (intro ae_word_lengthI exI allI impI conjI)
      fix w :: word assume len: "length w \<ge> 9"
      from len show "adj_sq\<^sub>w w \<in> L\<^sub>0'' \<longleftrightarrow> w \<in> L\<^sub>D''" by (fact L\<^sub>D''_L\<^sub>0''_adj_sq_iff)
      from len show "length (adj_sq\<^sub>w w) \<le> length w"
        by (intro eq_imp_le sh_msbD) (fact adj_sq_sh_pfx_half)
    qed

    show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N" by (fact t_superlinear')

    show "computable_in_time t adj_sq\<^sub>w" sorry \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be computed in time \<open>O(t(n))\<close>.\<close>
  qed

  moreover have "L\<^sub>D'' \<notin> DTIME(t)" by (fact L\<^sub>D''_t)
  ultimately show False by contradiction
qed

lemma L0''_T: "L\<^sub>0'' \<in> DTIME(T)"
proof -
  let ?T' = "\<lambda>n. real (max (T n) (n^3))"
  from T_cubic obtain n\<^sub>0 where *: "T(n) \<ge> n^3" if "n \<ge> n\<^sub>0" for n by blast

  from L\<^sub>D''_T and SQ_DTIME have "L\<^sub>0'' \<in> DTIME(?T')"
    unfolding L\<^sub>0''_def of_nat_max by (rule DTIME_int')
  then show "L\<^sub>0'' \<in> DTIME(T)"
  proof (rule DTIME_mono_ae)
    fix n assume "n \<ge> n\<^sub>0"
    with * have "T(n) \<ge> n^3" .
    then show "T n \<ge> ?T' n" by simp
  qed
qed

theorem L0''_time_hierarchy: "L\<^sub>0'' \<in> DTIME(T) - DTIME(t)" using L0''_T L0''_t ..

theorem dens_L0'': "dens L\<^sub>0'' n \<le> dsqrt n"
proof -
  have "dens L\<^sub>0'' n = dens (L\<^sub>D'' \<inter> SQ) n" unfolding L\<^sub>0''_def ..
  also have "... \<le> dens SQ n" by (subst Int_commute) (rule dens_intersect_le)
  also have "... = dsqrt n" by (rule dens_SQ)
  finally show ?thesis .
qed

lemmas lemma4_6'' = L0''_time_hierarchy dens_L0''

end \<comment> \<open>context \<^locale>\<open>tht_sq_assms\<close>\<close>

\<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


lemma lemma4_6'':
  fixes T t :: "nat \<Rightarrow> nat"
  defines "l\<^sub>R \<equiv> \<lambda>n. 4 * n + 11"
  defines "t' \<equiv> t \<circ> l\<^sub>R"
  assumes "fully_tconstr T"
    and T_dominates_t': "(\<lambda>n. t' n * log 2 (t' n) / T n) \<longlonglongrightarrow> 0"
    and T_not_0: "ae n. T n \<noteq> 0"
    and t_cubic: "ae n. t n \<ge> n^3"
    and "mono t"
  defines "L\<^sub>0 \<equiv> tht_assms'.L\<^sub>0'' T"
  shows "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" and "dens L\<^sub>0 n \<le> dsqrt n"
proof -
  let ?t' = "t \<circ> (\<lambda>n. 4 * n + 11)"

  have "tht_sq_assms' T t"
  proof (unfold_locales)
    show "(\<lambda>n. ?t' n * log 2 (?t' n) / T n) \<longlonglongrightarrow> 0" by (fold t'_def l\<^sub>R_def) fact
    show "mono t"
      and "fully_tconstr T"
      and "ae n. T n \<noteq> 0"
      and "ae n. t n \<ge> n^3"
      by fact+

    from \<open>ae n. t n \<ge> n^3\<close> show t_min: "ae n. t n \<ge> n"
    proof (ae_intro_nat)
      fix n :: nat
      have "n \<le> n^3" by simp
      also assume "n^3 \<le> t n"
      finally show "t n \<ge> n" .
    qed

    let ?T = "\<lambda>n. real (T n)"
    from T_not_0 have *: "ae n. ?T n \<noteq> 0" by simp
  
    with T_dominates_t' show "(\<lambda>n. t n * log 2 (t n) / T n) \<longlonglongrightarrow> 0"
    proof (rule dominates_mono)
      from t_min show "ae n. \<bar>t n * log 2 (t n)\<bar> \<le> \<bar>t' n * log 2 (t' n)\<bar>"
      proof (ae_intro_nat)
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
    unfolding L\<^sub>0_def by (fact tht_sq_assms'.lemma4_6'')+
qed

thm_oracles lemma4_6'' \<comment> \<open>shows \<open>skip_proof\<close> (the \<^emph>\<open>oracle\<close> used by \<open>sorry\<close>)\<close>

end
