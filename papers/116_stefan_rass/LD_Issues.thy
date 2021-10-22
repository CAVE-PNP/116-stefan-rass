theory LD_Issues
  imports L0
begin


section\<open>Alternative \<open>L\<^sub>D\<close> (Bridge to Lemma 4.6)\<close>

subsection\<open>Encoding\<close>

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


subsection\<open>\<open>L\<^sub>D'' \<notin> DTIME(t)\<close> via Reduction to \<open>L\<^sub>D\<close>\<close>

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


\<comment> \<open>The following proof is similar to that of @{thm tht_sq_assms.L0_t}.\<close>
lemma L\<^sub>D''_t: "L\<^sub>D'' \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>D'' \<in> DTIME(t)"
  then obtain M'' where "decides M'' L\<^sub>D''" and "time_bounded t M''" (* and "tm_wf0 M'" *) ..

  \<comment> \<open>Assume that \<^const>\<open>reduce_LD_LD''\<close> can be realized by a TM in time \<open>O(n)\<close>.\<close>
  define T\<^sub>R where "T\<^sub>R \<equiv> \<lambda>n::nat. n"
  obtain M\<^sub>R where "tm_wf0 M\<^sub>R"
    and M\<^sub>R_correct: "\<And>w. {input w} M\<^sub>R {input (reduce_LD_LD'' w)}"
    and "time_bounded T\<^sub>R M\<^sub>R"
    sorry

  define M where "M \<equiv> M\<^sub>R |+| M''"
  define t' where "t' = (\<lambda>n. tcomp T\<^sub>R n + tcomp t n)"

  have "L\<^sub>D \<in> DTIME(t')"
  proof (intro in_dtimeI allI)
    fix w :: word

    from \<open>decides M'' L\<^sub>D''\<close> have "decides_word M'' L\<^sub>D'' (reduce_LD_LD'' w)" ..
    moreover have "reduce_LD_LD'' w \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D" by (rule reduce_LD_LD''_correct)
    ultimately show "decides_word M L\<^sub>D w" unfolding M_def
      using M\<^sub>R_correct[of w] \<open>tm_wf0 M\<^sub>R\<close> by (rule reduce_decides)

    \<comment> \<open>This second part (M is \<open>t'\<close>-time-bounded) is considerably harder to show
      than for @{thm tht_sq_assms.L0_t}.
      Since the length of \<^term>\<open>reduce_LD_LD'' w\<close> is always greater than the length of \<^term>\<open>w\<close>
      (@{thm reduce_LD_LD''_len}),
      the existing @{thm reduce_time_bounded} does not hold in this case.

      Evaluating the time complexity given the differing word-lengths yields a new
      \<open>t'(n) := T\<^sub>R(n) + t(4n + 11)\<close>.
      The speed-up theorem does not help here, since for super-polynomial \<open>t\<close>,
      \<open>t(4n + 11)\<close> is not proportional to \<open>t(n)\<close>.\<close>

    from \<open>time_bounded t M''\<close> have "time_bounded_word t M'' (reduce_LD_LD'' w)" ..
    moreover from \<open>time_bounded T\<^sub>R M\<^sub>R\<close> have "time_bounded_word T\<^sub>R M\<^sub>R w" ..
    ultimately show "time_bounded_word t' M w" unfolding M_def t'_def
      using M\<^sub>R_correct reduce_LD_LD''_len sorry
  qed

  have t'_t: "real (t' n) \<le> 4 * real (t n)" if "n \<ge> 1" for n
  proof -
    have "tcomp T\<^sub>R n = n + 1" unfolding T\<^sub>R_def max_def ceiling_of_nat by simp
    then have "tcomp T\<^sub>R n + tcomp t n = (n + 1) + tcomp t n" by simp
    also have "... \<le> 2 * tcomp t n" unfolding mult_2 add_le_cancel_right by simp
    finally have "t' n \<le> 2 * tcomp t n" unfolding t'_def of_nat_le_iff .

    also have "... \<le> 2 * (2 * t n)"
    proof (intro mult_le_mono2)
      have "tcomp t n \<le> tcomp (\<lambda>n. 2 * t n) n"
        unfolding ceiling_of_nat nat_int by (intro max.mono) auto
      also have "... = 2 * t n"
      proof -
        have "n + 1 \<le> 2 * n" using \<open>n \<ge> 1\<close> by simp
        also have "... \<le> 2 * t n" using t_min by simp
        finally have "n + 1 \<le> 2 * t n" .
        then show ?thesis unfolding ceiling_of_nat nat_int by (fact max_absorb2)
      qed
      finally show "tcomp t n \<le> 2 * t n" .
    qed
    finally have "t' n \<le> 4 * t n" by simp
    then have "real (t' n) \<le> real (4 * t n)" by (fact of_nat_mono)
    also have "... = 4 * real (t n)" by simp
    finally show ?thesis .
  qed
  then have "L\<^sub>D \<in> DTIME(\<lambda>n. 4 * real (t n))" using \<open>L\<^sub>D \<in> DTIME(t')\<close> by (rule DTIME_mono_ae)

  \<comment> \<open>With the current assumptions, \<open>t\<close> is not necessarily super-linear.
    A similar requirement exists in the proof of @{thm L0_t} (and `L0''_t`, see below),
    that requires \<open>t\<close> to be at least cubic.\<close>
  moreover have "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. N \<le> real (t n) / real n" sorry
  ultimately have "L\<^sub>D \<in> DTIME(t)" by (intro DTIME_speed_up_rev[of 4 t]) auto

  moreover from time_hierarchy have "L\<^sub>D \<notin> DTIME(t)" ..
  ultimately show False by contradiction
qed

lemma L\<^sub>D''_T: "L\<^sub>D'' \<in> DTIME(T)"
  sorry (* TODO *)


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
    and \<open>DTIME(T)\<close> by \<open>tcomp t n = n\<^sup>3\<close> (for \<open>n > 1\<close>).

    For speed-up to help in this case, \<^term>\<open>t\<close> must grow at least as fast as \<^term>\<open>T\<^sub>R\<close>.
    (also, \<^term>\<open>t\<close> must be super-linear. See @{thm linear_time_speed_up}})
    \<^term>\<open>T\<^sub>R\<close> is assumed to be \<open>n\<^sup>3\<close>, which allows a naive algorithm for \<^const>\<open>adj_square\<close>.
    According to Wikipedia, the currently optimal algorithm for computing the square root on a TM
    seems to be Newton's method with Harvey-Hoeven multiplication with complexity \<open>O(n log(n))\<close>.\<close>

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
