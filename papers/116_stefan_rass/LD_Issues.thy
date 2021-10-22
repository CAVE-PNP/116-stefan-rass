theory LD_Issues
  imports L0
begin


\<comment> \<open>Decode a pair of \<open>(l, x) \<in> \<nat> \<times> {0,1}*\<close> from its encoded form \<open>w \<in> {0,1}*\<close>.

  The encoding defined by this should have \<open>l\<close> encoded in the upper (more significant) bits of \<open>l\<parallel>x\<close>.

  \<open>w\<close> is related to \<open>(l, x)\<close> through the regular expression \<open>1\<^sup>l0x{0,1}\<^sup>k\<close>,
  where \<^term>\<open>k = suffix_len w\<close>.
  If \<open>w\<close> does not match the expression, default values \<open>l = 0, x = []\<close> are assigned.

  Construction:
  To ensure the required property for Lemma 4.6, the lower ~half of \<open>w\<close>
  (the \<^term>\<open>suffix_len w\<close> least-significant-bits) is dropped.
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


context tht_assms
begin

\<comment> \<open>Alternative \<open>L\<^sub>D\<close>.

  Note: this is not intended to replace \<^const>\<open>L\<^sub>D\<close>.
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
          M\<^sub>v = decode_TM (strip_al_prefix v) in
      rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x))
    }"

definition L\<^sub>0'' :: lang
  where [simp]: "L\<^sub>0'' \<equiv> L\<^sub>D'' \<inter> SQ"


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


lemma L\<^sub>D''_t: "L\<^sub>D'' \<notin> DTIME(t)"
  sorry (* TODO *)

lemma L\<^sub>D''_T: "L\<^sub>D'' \<in> DTIME(T)"
  sorry (* TODO *)

end \<comment> \<open>context \<^locale>\<open>tht_assms\<close>\<close>


context tht_sq_assms
begin

text\<open>Lemma 4.6. Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.\<close>

lemma L0''_t: "L\<^sub>0'' \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>0'' \<in> DTIME(t)"
  then obtain M\<^sub>0 where "decides M\<^sub>0 L\<^sub>0''" and "time_bounded t M\<^sub>0" ..

  \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be realized by a TM in time \<open>n\<^sup>3\<close>.\<close>
  define T\<^sub>R where "T\<^sub>R \<equiv> \<lambda>n::nat. n^3"
  obtain M\<^sub>R where "tm_wf0 M\<^sub>R"
    and M\<^sub>R_correct: "\<And>w. {input w} M\<^sub>R {input (adj_sq\<^sub>w w)}"
    and "time_bounded T\<^sub>R M\<^sub>R"
    unfolding T\<^sub>R_def using T_lower_bound
    sorry

  define M where "M \<equiv> M\<^sub>R |+| M\<^sub>0"
  define t' where "t' = (\<lambda>n. real (tcomp T\<^sub>R n + tcomp t n))"

  have "L\<^sub>D'' \<in> DTIME(t')"
  proof (intro DTIME_ae ae_word_lengthI exI conjI)
    fix w :: word
    assume len: "length w \<ge> 9"

    from \<open>decides M\<^sub>0 L\<^sub>0''\<close> have "decides_word M\<^sub>0 L\<^sub>0'' (adj_sq\<^sub>w w)" ..
    moreover from len have "adj_sq\<^sub>w w \<in> L\<^sub>0'' \<longleftrightarrow> w \<in> L\<^sub>D''" by (rule L\<^sub>D''_L\<^sub>0''_adj_sq_iff)
    ultimately show "decides_word M L\<^sub>D'' w" unfolding M_def
      using M\<^sub>R_correct \<open>tm_wf0 M\<^sub>R\<close> by (rule reduce_decides)

    from \<open>time_bounded t M\<^sub>0\<close> have "time_bounded_word t M\<^sub>0 (adj_sq\<^sub>w w)" ..
    moreover from \<open>time_bounded T\<^sub>R M\<^sub>R\<close> have "time_bounded_word T\<^sub>R M\<^sub>R w" ..
    moreover from len have "length (adj_sq\<^sub>w w) \<le> length w"
      by (intro eq_imp_le sh_msbD) (rule adj_sq_sh_pfx_half)
    ultimately show "time_bounded_word t' M w" unfolding M_def t'_def
      using M\<^sub>R_correct by (intro reduce_time_bounded)
  qed

  then have "L\<^sub>D'' \<in> DTIME(t)" sorry
  \<comment> \<open>This is not correct, since \<^term>\<open>t\<close> could be arbitrarily small.
    Let \<open>t(n) = n\<close> and \<open>T(n) = n\<^sup>3\<close>. Then \<open>DTIME(t)\<close> is limited by \<open>tcomp t n = n + 1\<close>
    and \<open>DTIME(T)\<close> by \<open>tcomp t n = n\<^sup>3\<close> (for \<open>n > 1\<close>).\<close>

  moreover have "L\<^sub>D'' \<notin> DTIME(t)" by (fact L\<^sub>D''_t)
  ultimately show False by contradiction
qed

lemma L0''_T: "L\<^sub>0'' \<in> DTIME(T)"
proof -
  let ?T' = "\<lambda>n. real (max (T n) (n^3))"
  from T_lower_bound have "?T' = T" by (intro ext, unfold of_nat_eq_iff) (rule max_absorb1)

  from L\<^sub>D''_T and SQ_DTIME have "L\<^sub>0'' \<in> DTIME(?T')"
    unfolding L\<^sub>0''_def of_nat_max by (rule DTIME_int')
  then show "L\<^sub>0'' \<in> DTIME(T)" unfolding \<open>?T' = T\<close> .
qed

theorem L0''_time_hierarchy: "L\<^sub>0'' \<in> DTIME(T) - DTIME(t)" using L0''_T L0''_t ..

theorem dens_L0'': "dens L\<^sub>0'' n \<le> dsqrt n"
proof -
  have "dens L\<^sub>0'' n = dens (L\<^sub>D'' \<inter> SQ) n" unfolding L\<^sub>0''_def ..
  also have "... \<le> dens SQ n" by (subst Int_commute) (rule dens_intersect_le)
  also have "... = dsqrt n" by (rule dens_SQ)
  finally show ?thesis .
qed

lemmas lemma4_6 = L0_time_hierarchy dens_L0

end \<comment> \<open>context \<^locale>\<open>tht_sq_assms\<close>\<close>


end
