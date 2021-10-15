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

definition (in tht_assms) L\<^sub>D'' :: lang
  where "L\<^sub>D'' \<equiv> {w.
      let (l, x) = decode_pair w;
          v = drop (length x - l) x;
          M\<^sub>v = decode_TM (strip_al_prefix v) in
      rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x))
    }"

lemma L\<^sub>D''_adj_sq_iff:
  fixes w
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes len: "length w \<ge> 9"
  shows "w' \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D''"
  unfolding L\<^sub>D''_def mem_Collect_eq w' len[THEN pair_adj_sq_eq] ..

end \<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


end
