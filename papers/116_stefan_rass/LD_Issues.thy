theory LD_Issues
  imports L0
begin

lemma
  assumes "tm_wf0 M_w"
    and "M_w \<noteq> Rejecting_TM"
  shows "TM_decode_pad w = M_w \<longleftrightarrow> strip_al_prefix (strip_exp_pad w) = encode_TM M_w"
proof (intro iffI)
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


context tht_assms
begin

text\<open>Alternative formulation, intended to fix the issues of \<^const>\<open>L\<^sub>D\<close> for Lemma 4.6
  and \<^const>\<open>L\<^sub>D'\<close> for the THT.\<close>

definition L\<^sub>D'' :: lang
  where LD''_def: "L\<^sub>D'' \<equiv> {w. \<exists>M\<^sub>w. w = encode_TM M\<^sub>w \<and> rejects M\<^sub>w w \<and> time_bounded_word T M\<^sub>w w}"

definition L\<^sub>D''' :: lang
  where LD'''_def: "L\<^sub>D''' \<equiv> {w. let M\<^sub>w = TM_decode_pad w in
                  (\<exists>M\<^sub>w. w = encode_TM M\<^sub>w) \<and> rejects M\<^sub>w w \<and> time_bounded_word T M\<^sub>w w}"


theorem time_hierarchy': "L\<^sub>D' \<in> DTIME(T) - DTIME(t)"
proof
  show "L\<^sub>D' \<in> DTIME(T)" sorry (* unchanged *)

  have "L \<noteq> L\<^sub>D'" if "L \<in> DTIME(t)" for L
  proof -
    from \<open>L \<in> DTIME(t)\<close> obtain M\<^sub>w where "decides M\<^sub>w L" and "time_bounded t M\<^sub>w" and "tm_wf0 M\<^sub>w" ..

    let ?n = "length (encode_TM M\<^sub>w) + 2"
    obtain l where "T(2*l) \<ge> t(2*l)" and "clog l \<ge> ?n" sorry (* unchanged *)
    obtain w where "length w = l" and dec_w: "TM_decode_pad w = M\<^sub>w"
      using \<open>tm_wf0 M\<^sub>w\<close> \<open>clog l \<ge> ?n\<close> by (rule embed_TM_in_len)

    let ?w = "strip_al_prefix (strip_exp_pad w)"
    have "?w \<in> L \<longleftrightarrow> w \<notin> L\<^sub>D'"
    proof
      assume "?w \<in> L"
      moreover from \<open>decides M\<^sub>w L\<close> have "?w \<notin> L \<longleftrightarrow> rejects M\<^sub>w ?w" unfolding decides_def by blast
      ultimately have "\<not> rejects M\<^sub>w ?w" by blast
      then show "w \<notin> L\<^sub>D'" unfolding LD'_def mem_Collect_eq dec_w Let_def by presburger
    next
      assume "w \<notin> L\<^sub>D'"
      moreover have "time_bounded_word T M\<^sub>w ?w" sorry (* probably works *)
      ultimately have "\<not> rejects M\<^sub>w ?w" unfolding LD'_def dec_w mem_Collect_eq Let_def by blast
      with \<open>decides M\<^sub>w L\<close> show "?w \<in> L" unfolding decides_def by blast
    qed

    have "w \<in> L \<longleftrightarrow> w \<notin> L\<^sub>D'"
    proof
      assume "w \<in> L"
      moreover from \<open>decides M\<^sub>w L\<close> have "w \<notin> L \<longleftrightarrow> rejects M\<^sub>w w" unfolding decides_def by blast
      ultimately have "\<not> rejects M\<^sub>w w" by blast
      then show "w \<notin> L\<^sub>D'" unfolding LD'_def mem_Collect_eq dec_w Let_def by presburger (* nope *)
    next
      assume "w \<notin> L\<^sub>D'"
      moreover have "time_bounded_word T M\<^sub>w w"
      proof (rule time_bounded_word_mono)
        from \<open>T(2*l) \<ge> t(2*l)\<close> show "real (T (tape_size <w>\<^sub>t\<^sub>p)) \<ge> real (t (tape_size <w>\<^sub>t\<^sub>p))"
          unfolding tape_size_input \<open>length w = l\<close> by (rule of_nat_mono)
        from \<open>time_bounded t M\<^sub>w\<close> show "time_bounded_word t M\<^sub>w w" ..
      qed
      ultimately have "\<not> rejects M\<^sub>w w" unfolding LD'_def dec_w mem_Collect_eq Let_def by blast (* nope *)
      with \<open>decides M\<^sub>w L\<close> show "w \<in> L" unfolding decides_def by blast
    qed
    then show "L \<noteq> L\<^sub>D'" by blast
  qed
  then show "L\<^sub>D' \<notin> DTIME(t)" by blast
qed

theorem time_hierarchy'': "L\<^sub>D'' \<in> DTIME(T) - DTIME(t)"
proof
  show "L\<^sub>D'' \<in> DTIME(T)" sorry (* unchanged *)

  have "L \<noteq> L\<^sub>D''" if "L \<in> DTIME(t)" for L
  proof -
    from \<open>L \<in> DTIME(t)\<close> obtain M\<^sub>w where "decides M\<^sub>w L" and "time_bounded t M\<^sub>w" and "tm_wf0 M\<^sub>w" ..

    let ?n = "length (encode_TM M\<^sub>w) + 2"
    obtain l where "T(2*l) \<ge> t(2*l)" and "clog l \<ge> ?n" sorry (* unchanged *)
    obtain w where "length w = l" and dec_w: "TM_decode_pad w = M\<^sub>w"
      using \<open>tm_wf0 M\<^sub>w\<close> \<open>clog l \<ge> ?n\<close> by (rule embed_TM_in_len)

    have "w \<in> L \<longleftrightarrow> w \<notin> L\<^sub>D''"
    proof
      assume "w \<in> L"
      moreover from \<open>decides M\<^sub>w L\<close> have "w \<notin> L \<longleftrightarrow> rejects M\<^sub>w w" unfolding decides_def by blast
      ultimately have "\<not> rejects M\<^sub>w w" by blast
      then show "w \<notin> L\<^sub>D''" unfolding LD''_def mem_Collect_eq dec_w Let_def by presburger (* nope *)
    next
      assume "w \<notin> L\<^sub>D''"
      moreover have "time_bounded_word T M\<^sub>w w"
      proof (rule time_bounded_word_mono)
        from \<open>T(2*l) \<ge> t(2*l)\<close> show "real (T (tape_size <w>\<^sub>t\<^sub>p)) \<ge> real (t (tape_size <w>\<^sub>t\<^sub>p))"
          unfolding tape_size_input \<open>length w = l\<close> by (rule of_nat_mono)
        from \<open>time_bounded t M\<^sub>w\<close> show "time_bounded_word t M\<^sub>w w" ..
      qed
      ultimately have "\<not> rejects M\<^sub>w w" unfolding LD''_def dec_w mem_Collect_eq Let_def by blast (* nope *)
      with \<open>decides M\<^sub>w L\<close> show "w \<in> L" unfolding decides_def by blast
    qed
    then show "L \<noteq> L\<^sub>D''" by blast
  qed
  then show "L\<^sub>D'' \<notin> DTIME(t)" by blast
qed

end (* context tht_assms *)


context tht_sq_assms
begin

lemma L\<^sub>D_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D''"
proof -
  from \<open>length w \<ge> 20\<close> have "shared_MSBs (clog (length w)) w w'" unfolding w' by (rule adj_sq_sh_pfx_log)
  then have "length w' = length w" by (elim sh_msbE[symmetric])
  then have len: "tape_size <w'>\<^sub>t\<^sub>p = tape_size <w>\<^sub>t\<^sub>p" unfolding tape_size_input by (rule arg_cong)
  from l have dec: "TM_decode_pad w' = TM_decode_pad w" unfolding w' by (rule adj_sq_TM_dec)
  from l have pad: "strip_exp_pad w' = strip_exp_pad w" unfolding w' by (rule adj_sq_exp_pad)
  show "w' \<in> L\<^sub>D'' \<longleftrightarrow> w \<in> L\<^sub>D''" unfolding LD''_def mem_Collect_eq unfolding dec pad len
  oops

end (* context tht_sq_assms *)


end
