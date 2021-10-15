theory LD_Issues
  imports L0
begin


\<comment> \<open>Decode a pair of words \<open>(l, x) \<in> {0,1}* \<times> {0,1}*\<close> from its encoded form "\<open>l\<parallel>x \<in> {0,1}*\<close>".

  The encoding defined by this should have \<open>l\<close> encoded in the upper (more significant) bits of \<open>l\<parallel>x\<close>.

  This is undefined for now, as the restricted alphabet does not allow the obvious method
  of using a separation symbol that can not occur in \<open>l\<close>.
  (It suffices to restrict this condition to \<open>l\<close>, since after encountering the symbol
  the "rest" of \<open>w\<close> is determined \<open>x\<close>.)

  A possible solution for this would be to use another encoding for \<open>l\<close>,
  such as \<^const>\<open>decode_word\<close>, defined in \<^theory>\<open>OWF.Complexity\<close>.
  However, this method may have unintended side-effects, as the encoding increases the length,
  which is critical in proving some of the further lemmas.\<close>

\<comment> \<open>what if \<open>l = 1\<^sup>n\<close> and \<open>\<cent> = 0\<close>? then \<open>w = 1\<^sup>l0w\<close>\<close>

definition decode_pair :: "word \<Rightarrow> word \<times> word"
  where "decode_pair \<equiv> undefined"


context tht_assms
begin

\<comment> \<open>Alternative \<open>L\<^sub>D\<close>.

  Note: this is not intended to replace \<^const>\<open>L\<^sub>D\<close>.
  The further proof uses the similarity of \<open>L\<^sub>D\<close> and \<open>L\<^sub>D''\<close>
  to prove properties of \<open>L\<^sub>D''\<close> via reduction to \<open>L\<^sub>D\<close>.

  Construction: Given a word \<open>w\<close>.
  Split the word \<open>w\<close> into \<open>(l, x)\<close> using \<^const>\<open>decode_pair\<close>.
  Define \<open>v\<close> as the \<open>log\<^sub>2(l)\<close> most-significant-bits of \<open>x\<close>.
  Remove the arbitrary-length \<open>1\<^sup>+0\<close>-prefix from \<open>v\<close> to retain the pure encoding of \<open>M\<^sub>v\<close>.
  If \<open>M\<^sub>v\<close> rejects \<open>v\<close> within \<open>T(len(x))\<close> steps, \<open>w \<in> L\<^sub>D''\<close> holds.

  Note that in this version, using \<^const>\<open>time_bounded_word\<close> is not possible,
  as the word that determines the time bound (\<open>x\<close>) differs from the input word (\<open>v\<close>).
  The alternative version shown in @{thm time_bounded_altdef} is used for simplicity.\<close>

definition (in tht_assms) L\<^sub>D'' :: lang
  where "L\<^sub>D'' \<equiv> {w. 
      let (l, x) = decode_pair w;
          v = drop (length x - clog (l)\<^sub>2) x;
          M\<^sub>v = decode_TM (strip_al_prefix v) in
      rejects M\<^sub>v v \<and> is_final (steps0 (1, <v>\<^sub>t\<^sub>p) M\<^sub>v (tcomp\<^sub>w T x))
    }"

end \<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


context tht_sq_assms
begin

lemma
  fixes w
  defines "w' \<equiv> adj_sq\<^sub>w w"
  defines "l \<equiv> fst (decode_pair w)"
    and "x \<equiv> snd (decode_pair w)"
    and "l' \<equiv> fst (decode_pair w')"
    and "x' \<equiv> snd (decode_pair w')"
  defines "v \<equiv> drop (length x - clog (l)\<^sub>2) x"
    and "v' \<equiv> drop (length x' - clog (l')\<^sub>2) x'"
    (* need some assumption that fixes the length of l in a way that allows this to work *)
  shows "v' = v"
proof -
  oops


lemma L\<^sub>D_adj_sq_iff:
  fixes w
  defines l: "l \<equiv> fst (decode_pair w)"
    and w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes "length w \<ge> 20"
    and "clog (l)\<^sub>2 \<le> clog (length w)" (* new *)
  shows "w' \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D''"
proof -
  from \<open>length w \<ge> 20\<close> have "shared_MSBs (clog (length w)) w w'" unfolding w' by (rule adj_sq_sh_pfx_log)
  then have "length w' = length w" by (elim sh_msbE[symmetric])
  oops

end \<comment> \<open>\<^locale>\<open>tht_sq_assms\<close>\<close>


lemma (* relation between two similar, but not equivalent propositions *)
  assumes "tm_wf0 M_w"
    and "M_w \<noteq> Rejecting_TM"
  shows "TM_decode_pad w = M_w \<longleftrightarrow> strip_al_prefix (strip_exp_pad w) = encode_TM M_w"
proof (rule iffI)
  assume *: "TM_decode_pad w = M_w"
  with assms(2) have h1: "is_encoded_TM (strip_al_prefix (strip_exp_pad w))"
    unfolding TM_decode_pad_def decode_TM_def by argo

  then have h2: "\<exists>!M. strip_al_prefix (strip_exp_pad w) = encode_TM M"
    unfolding is_encoded_TM_def apply (rule ex_ex1I)
    using encode_TM_inj unfolding inj_def by presburger

  from assms(2) * have h3: "tm_wf0 (THE M. strip_al_prefix (strip_exp_pad w) = encode_TM M)"
    unfolding TM_decode_pad_def decode_TM_def h1[THEN if_P] filter_wf_TMs_def by argo

  show "strip_al_prefix (strip_exp_pad w) = encode_TM M_w"
    unfolding *[symmetric] TM_decode_pad_def
    unfolding decode_TM_def h1[THEN if_P]
    unfolding filter_wf_TMs_def h3[THEN if_P]
    using h2[THEN theI_unique] by blast
next
  assume *: "strip_al_prefix (strip_exp_pad w) = encode_TM M_w"
  show "TM_decode_pad w = M_w" unfolding TM_decode_pad_def *
    by (rule codec_TM) fact
qed

end
