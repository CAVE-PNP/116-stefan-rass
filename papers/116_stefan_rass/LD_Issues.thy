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

context tht_assms
begin

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


end \<comment> \<open>context \<^locale>\<open>tht_assms\<close>\<close>
context tht_sq_assms begin

lemma L\<^sub>D''_t: "L\<^sub>D'' \<notin> DTIME(t)" \<comment> \<open>The proof is similar to that of @{thm tht_sq_assms.L0_t}.\<close>
proof (rule ccontr, unfold not_not)
  let ?f\<^sub>R = reduce_LD_LD'' and ?l\<^sub>R = "\<lambda>n. 4*n + 11"

  assume "L\<^sub>D'' \<in> DTIME(t)"
  then have "L\<^sub>D \<in> DTIME(t \<circ> ?l\<^sub>R)" unfolding comp_def
  proof (rule reduce_DTIME')
    show "ae w. (?f\<^sub>R w \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D) \<and> (length (?f\<^sub>R w) \<le> ?l\<^sub>R (length w))"
    proof (rule ae_conjI)
      from reduce_LD_LD''_correct show "ae w. ?f\<^sub>R w \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D" by (rule ae_everyI)
      from reduce_LD_LD''_len show "ae w. length (?f\<^sub>R w) \<le> ?l\<^sub>R (length w)"
        by (intro ae_everyI) simp
    qed

    from t_mono have "t(n) \<le> t(?l\<^sub>R n)" for n by (rule monoD) linarith
    then show "ae x. real (t x) \<le> real (t (?l\<^sub>R x))" by (intro ae_everyI of_nat_mono)

    show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N" by (fact t_superlinear)

    show "computable_in_time t reduce_LD_LD''" sorry \<comment> \<open>Assume that \<^const>\<open>reduce_LD_LD''\<close> can be computed in time \<open>O(n)\<close>.\<close>
  qed
  then have "L\<^sub>D \<in> DTIME(t)" sorry \<comment> \<open>False for super-polynomial \<open>t\<close>.
      Example: \<open>t(n) := 2\<^sup>n\<close>, then \<open>t(?l\<^sub>R n) = 2\<^sup>4\<^sup>n\<^sup>+\<^sup>1\<^sup>1 = 16\<^sup>n \<cdot> 2\<^sup>1\<^sup>1 \<in> \<omega>(t(n))\<close>.\<close>

  moreover from time_hierarchy have "L\<^sub>D \<notin> DTIME(t)" ..
  ultimately show False by contradiction
qed


subsection\<open>\<open>L\<^sub>D'' \<in> DTIME(T)\<close> via Reduction from \<open>L\<^sub>D''\<close> to \<open>L\<^sub>D\<close>\<close>

lemma L\<^sub>D''_T: "L\<^sub>D'' \<in> DTIME(T)"
proof (rule reduce_DTIME)
  from time_hierarchy show "L\<^sub>D \<in> DTIME(T)" ..

  define f\<^sub>R where "f\<^sub>R \<equiv> \<lambda>w. let (l, x) = decode_pair w in drop (length x - l) x"

  \<comment> \<open>This is very likely incorrect, as \<open>v\<close> and \<open>x\<close> are not necessarily equal.
    The different time-bound could lead to differences in membership;
    False positives when increased time-bounds allow \<open>M\<^sub>v\<close> compute additional steps and reject \<open>v\<close>,
    or false negatives when shorter time-bounds do not afford \<open>M\<^sub>v\<close> enough time.\<close>
  have "f\<^sub>R w \<in> L\<^sub>D \<longleftrightarrow> w \<in> L\<^sub>D''" for w
  proof -
    have "f\<^sub>R w \<in> L\<^sub>D \<longleftrightarrow> (let (l, x) = decode_pair w; v = drop (length x - l) x; M\<^sub>v = TM_decode_pad v
           in rejects M\<^sub>v v \<and> time_bounded_word T M\<^sub>v v)"
      unfolding LD_def mem_Collect_eq unfolding f\<^sub>R_def Let_def prod.case ..
    also have "... \<longleftrightarrow> (let (l, x) = decode_pair w; v = drop (length x - l) x; M\<^sub>v = TM_decode_pad v
           in rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T v)))"
      unfolding time_bounded_altdef ..
    also have "... \<longleftrightarrow> (let (l, x) = decode_pair w; v = drop (length x - l) x; M\<^sub>v = TM_decode_pad v
           in rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x)))" sorry \<comment> \<open>not possible\<close>
    also have "... \<longleftrightarrow> w \<in> L\<^sub>D''"
      unfolding L\<^sub>D''_def mem_Collect_eq time_bounded_def ..
    finally show ?thesis .
  qed
  moreover have "length (f\<^sub>R w) \<le> length w" for w
  proof -
    have "length (f\<^sub>R w) \<le> length (decode_pair_x w)" unfolding f\<^sub>R_def by simp
    also have "... \<le> length (strip_sq_pad w)" unfolding decode_pair_x_def
      unfolding Let_def prod.case length_rev length_tl dropWhile_eq_drop length_drop by simp
    also have "... \<le> length w" unfolding strip_sq_pad_def by simp
    finally show ?thesis .
  qed
  ultimately show "almost_everywhere (\<lambda>w. (f\<^sub>R w \<in> L\<^sub>D) = (w \<in> L\<^sub>D'') \<and> length (f\<^sub>R w) \<le> length w)"
    by blast

  show "computable_in_time T f\<^sub>R" unfolding f\<^sub>R_def sorry \<comment> \<open>Assume that \<^term>\<open>f\<^sub>R\<close> can be evaluated in \<open>O(n)\<close>.\<close>

  show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N" by (fact T_superlinear)
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

    show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N" by (fact t_superlinear)

    show "computable_in_time t adj_sq\<^sub>w" sorry \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be computed in time \<open>O(t(n))\<close>.\<close>
  qed

  moreover have "L\<^sub>D'' \<notin> DTIME(t)" by (fact L\<^sub>D''_t)
  ultimately show False by contradiction
qed

lemma L0''_T: "L\<^sub>0'' \<in> DTIME(T)"
proof -
  let ?T' = "\<lambda>n. real (max (T n) (n^3))"
  from T_cubic2 obtain n\<^sub>0 where *: "T(n) \<ge> n^3" if "n \<ge> n\<^sub>0" for n by blast

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


end
