section \<open>Encoding TMs as (Binary) Strings\<close>

theory TM_Encoding
  imports Goedel_Numbering Complexity
    "Supplementary/Misc" "HOL-Library.Sublist"
begin

text\<open>As defined in @{cite \<open>ch.~4.2\<close> rassOwf2017} (outlined in @{cite \<open>ch.~3.1\<close> rassOwf2017})
  the decoding of a TM \<open>M\<close> from a binary word \<open>w\<close> includes:

    \<^item> Exponential padding. ``all but the most significant \<open>\<lceil>log(len(w))\<rceil>\<close> bits are ignored''
    \<^item> Arbitrary-length \<open>1\<^sup>+0\<close> prefix. ``from [the result] we drop all preceding 1-bits and the first 0-bit''
    \<^item> Code description. ``let \<open>\<rho>(M) \<in> \<Sigma>\<^sup>*\<close> denote a complete description of a TM M in string form''.

  Recall the definition of \<^typ>\<open>bin\<close> (see \<^file>\<open>Binary.thy\<close>),
  which causes the MSB to be the \<^const>\<open>last\<close> element of the list,
  which is the \<^emph>\<open>rightmost\<close> one when explicitly referring to lists in Isabelle.\<close>


subsection\<open>Canonical Form\<close> (* TODO motivate, document *)

definition next_fun_wrapper :: "['x, nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> nat \<Rightarrow> 'x, 'q, 's option list, nat] \<Rightarrow> 'x"
  where "next_fun_wrapper default_val k \<Sigma> Q f q hds i \<equiv> if q \<in> Q \<and> length hds = k \<and> set hds \<subseteq> options \<Sigma> \<and> i < k then f q hds i else default_val"

abbreviation next_state_wrapper :: "[nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> 'q, 'q, 's option list] \<Rightarrow> 'q"
  where "next_state_wrapper k \<Sigma> Q f q hds \<equiv> next_fun_wrapper q k \<Sigma> Q (\<lambda>q hds i. f q hds) q hds 0"
abbreviation next_write_wrapper :: "[nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> nat \<Rightarrow> 's option, 'q, 's option list, nat] \<Rightarrow> 's option"
  where "next_write_wrapper k \<Sigma> Q f q hds i \<equiv> next_fun_wrapper (hds ! i) k \<Sigma> Q f q hds i"
abbreviation next_move_wrapper :: "[nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> nat \<Rightarrow> head_move, 'q, 's option list, nat] \<Rightarrow> head_move"
  where "next_move_wrapper k \<Sigma> Q f q hds i \<equiv> next_fun_wrapper No_Shift k \<Sigma> Q f q hds i"

lemma next_fun_wrapper_default[simp]:
  fixes k \<Sigma> Q f val and M :: "('q, 's, 'l) TM_record"
  defines "f' \<equiv> next_fun_wrapper val k \<Sigma> Q f"
  defines "f'' \<equiv> next_fun_wrapper val (tape_count M) (symbols M) (states M) f"
  shows "q \<notin> Q \<Longrightarrow> f' q hds i = val"
    and "length hds \<noteq> k \<Longrightarrow> f' q hds i = val"
    and "\<not> set hds \<subseteq> options \<Sigma> \<Longrightarrow> f' q hds i = val"
    and "\<not> i < k \<Longrightarrow> f' q hds i = val"
    and "\<not> wf_hds_rec M hds \<Longrightarrow> f'' q hds i = val"
  unfolding assms next_fun_wrapper_def by (blast intro!: if_not_P)+

lemma next_fun_wrapper_simps[simp]:
  fixes k \<Sigma> Q f val and M :: "('q, 's, 'l) TM_record"
  defines "f' \<equiv> next_fun_wrapper val k \<Sigma> Q f"
  defines "f'' \<equiv> next_fun_wrapper val (tape_count M) (symbols M) (states M) f"
  shows "q \<in> Q \<Longrightarrow> length hds = k \<Longrightarrow> set hds \<subseteq> options \<Sigma> \<Longrightarrow> i < k \<Longrightarrow> f' q hds i = f q hds i"
    and "q \<in> states M \<Longrightarrow> wf_hds_rec M hds \<Longrightarrow> i < tape_count M \<Longrightarrow> f'' q hds i = f q hds i"
  unfolding assms next_fun_wrapper_def using assms(2-) by (blast intro!: if_P)+

lemma (in TM) next_fun_wrapper_TM_simps:
  fixes f val c
  defines "q \<equiv> state c"
    and "hds \<equiv> heads c"
    and "f' \<equiv> next_fun_wrapper val k \<Sigma> Q f"
  assumes "wf_config c"
  shows "i < k \<Longrightarrow> f' q hds i = f q hds i"
    and "f' q hds 0 = f q hds 0"
proof -
  from \<open>wf_config c\<close> show "i < k \<Longrightarrow> f' q hds i = f q hds i" for i
    unfolding assms by (subst next_fun_wrapper_simps) blast+
  then show "f' q hds 0 = f q hds 0" by blast
qed


definition canonical_TM_rec :: "('q, 's, 'l) TM_record \<Rightarrow> ('q, 's, 'l) TM_record"
  where "canonical_TM_rec M \<equiv> M\<lparr>
    label := (\<lambda>q. if q \<in> states M then label M q else undefined),
    next_state := next_state_wrapper (tape_count M) (symbols M) (states M) (next_state M),
    next_write := next_write_wrapper (tape_count M) (symbols M) (states M) (next_write M),
    next_move := next_move_wrapper (tape_count M) (symbols M) (states M) (next_move M)
  \<rparr>"

lemma canonical_TM_rec_simps[simp]:
  fixes M :: "('q, 's, 'l) TM_record"
  defines "M' \<equiv> canonical_TM_rec M"
  shows "tape_count M' = tape_count M"
    and "symbols M' = symbols M"
    and "states M' = states M"
    and "initial_state M' = initial_state M"
    and "final_states M' = final_states M"
    and "label M' = (\<lambda>q. if q \<in> states M then label M q else undefined)" (* TODO consider using  *)
    and "next_state M' = next_state_wrapper (tape_count M) (symbols M) (states M) (next_state M)"
    and "next_write M' = next_write_wrapper (tape_count M) (symbols M) (states M) (next_write M)"
    and "next_move M' = next_move_wrapper (tape_count M) (symbols M) (states M) (next_move M)"
    and "wf_hds_rec M' = wf_hds_rec M"
    and "more M' = more M"
  unfolding M'_def canonical_TM_rec_def by (induction M) force+


lemma canonical_TM_valid: "valid_TM M \<Longrightarrow> valid_TM (canonical_TM_rec M)"
proof (unfold_locales, unfold canonical_TM_rec_simps)
  assume "valid_TM M" then interpret valid_TM .

  fix q hds assume q: "q \<in> states M" and hds: "wf_hds_rec M hds"
  then show "next_state_wrapper (tape_count M) (symbols M) (states M) (next_state M) q hds \<in> states M"
    unfolding next_fun_wrapper_simps(2)[OF q hds axioms(1)] by (fact axioms(7))
  fix i assume i: "i < tape_count M"
  with q hds show "next_write_wrapper (tape_count M) (symbols M) (states M) (next_write M) q hds i \<in> tape_symbols_rec M"
    unfolding next_fun_wrapper_simps(2)[OF q hds i] by (fact axioms(8))
qed (fact valid_TM.axioms)+


locale Canonical_TM = TM M for M :: "('q, 's, 'l) TM"
begin

lemma M'_valid: "valid_TM (canonical_TM_rec M_rec)" using valid_TM_axioms by (fact canonical_TM_valid)

definition "M' \<equiv> Abs_TM (canonical_TM_rec M_rec)"

sublocale M': TM M' .

lemma M'_rec: "M'.M_rec = (canonical_TM_rec M_rec)"
  unfolding M'_def by (blast intro: Abs_TM_inverse M'_valid)
lemmas M'_fields = M'.TM_fields_defs[unfolded M'_rec canonical_TM_rec_simps TM_record.simps TM_fields_defs[symmetric]]
lemmas [simp] = M'_fields(1-6)
lemmas M'_next_fun_wrapper_simps[simp] = M'.next_fun_wrapper_TM_simps[unfolded M'_fields]

lemma wf_config_eq[simp]: "M'.wf_config c \<longleftrightarrow> wf_config c" unfolding TM.wf_config_def M'_fields ..

lemma step_eq[simp]:
  assumes [simp, intro]: "wf_config c"
  shows "M'.step c = step c"
proof (cases "is_final c")
  let ?q = "state c" and ?tps = "tapes c" and ?hds = "heads c"

  assume "\<not> is_final c"
  then have "M'.step c = M'.step_not_final c" by simp
  also have "... = step_not_final c"
  proof (intro step_not_final_eqI1)
    show "M'.\<delta>\<^sub>q ?q ?hds = \<delta>\<^sub>q ?q ?hds" unfolding M'_fields by simp

    have "M'.\<delta>\<^sub>a ?q ?hds = \<delta>\<^sub>a ?q ?hds" unfolding TM.next_actions_altdef M'_fields(1)
    proof (rule list.map_cong0)
      fix i assume "i \<in> set [0..<k]"
      then show "(M'.\<delta>\<^sub>w ?q ?hds i, M'.\<delta>\<^sub>m ?q ?hds i) = (\<delta>\<^sub>w ?q ?hds i, \<delta>\<^sub>m ?q ?hds i)"
        unfolding M'_fields by auto
    qed
    then show "tapes (M'.step_not_final c) = tapes (step_not_final c)" by force
  qed (simp add: TM_config.case_eq_if)
  also from \<open>\<not> is_final c\<close> have "... = step c" by simp
  finally show ?thesis .
qed simp

corollary steps_eq[simp]: "wf_config c \<Longrightarrow> M'.steps n c = steps n c"
proof (induction n arbitrary: c)
  case (Suc n)
  then show "M'.steps (Suc n) c = steps (Suc n) c" unfolding funpow_Suc_right comp_def
    unfolding step_eq[OF \<open>wf_config c\<close>] by (blast dest: wf_step)
qed simp

lemma initial_config_eq[simp]: "M'.c\<^sub>0 w = c\<^sub>0 w" by (simp add: TM.initial_config_def)
corollary run_eq: "wf_input w \<Longrightarrow> M'.run n w = run n w" by simp

corollary compute_eq[simp]: "wf_input w \<Longrightarrow> M'.compute w = compute w"
  unfolding TM.compute_altdef2 TM.is_final_def by simp

end

abbreviation "canonical_TM \<equiv> Canonical_TM.M'"

lemmas canonical_TM_fields = Canonical_TM.M'_fields
declare canonical_TM_fields(1-6)[simp]

lemma [simp]:
  shows canonical_TM_acc: "TM_decider.F\<^sub>A (canonical_TM M) = TM_decider.F\<^sub>A M"
    and canonical_TM_rej: "TM_decider.F\<^sub>R (canonical_TM M) = TM_decider.F\<^sub>R M"
proof -
  let ?M' = "canonical_TM M"
  have "TM.F ?M' = TM.F M" by simp
  moreover have "TM.label ?M' q = TM.label M q" if "q \<in> TM.F ?M'" for q using that by auto
  ultimately show "TM_decider.F\<^sub>A ?M' = TM_decider.F\<^sub>A M" and "TM_decider.F\<^sub>R ?M' = TM_decider.F\<^sub>R M"
    by (fact acc_eqI, fact rej_eqI)
qed

lemma [simp]:
  assumes "TM.wf_input M w"
  shows canonical_TM_accepts: "TM_decider.accepts (canonical_TM M) w \<longleftrightarrow> TM_decider.accepts M w"
    and canonical_TM_rejects: "TM_decider.rejects (canonical_TM M) w \<longleftrightarrow> TM_decider.rejects M w"
  by (auto simp: TM_decider.rejects_def TM_decider.accepts_def Canonical_TM.compute_eq["OF" assms])

lemma canonical_TM_time_bounded[simp]:
  assumes "TM.wf_input M w"
  shows "TM.time_bounded_word (canonical_TM M) T w \<longleftrightarrow> TM.time_bounded_word M T w"
  unfolding TM.time_bounded_word_def using assms by (simp add: Canonical_TM.run_eq)

lemma canonical_TM_rec_idem[simp]: "canonical_TM_rec (canonical_TM_rec M) = canonical_TM_rec M"
  by (rule TM_record.equality) (simp only: canonical_TM_rec_simps If_If next_fun_wrapper_def)+

lemma canonical_TM_idem[simp]: "canonical_TM (canonical_TM M) = canonical_TM M"
  unfolding Rep_TM_inject[symmetric] Canonical_TM.M'_rec canonical_TM_rec_idem ..


subsection\<open>Code Description\<close>

type_synonym bin_symbol = "bool option"

type_synonym binTM = "(nat, bool, bool) TM"


locale TM_Encoding = (* TODO fix bool this early? *)
  fixes enc_TM :: "binTM \<Rightarrow> bool list"
    and is_valid_enc_TM :: "bool list \<Rightarrow> bool"
    and dec_TM :: "bool list \<Rightarrow> binTM"
  assumes valid_enc: "\<And>M. is_valid_enc_TM (enc_TM M)"
    and inj_enc_TM: "inj_on enc_TM (range canonical_TM)"
    and enc_dec_TM: "\<And>M. dec_TM (enc_TM M) = canonical_TM M"
    and dec_enc_TM: "\<And>x. is_valid_enc_TM x \<Longrightarrow> enc_TM (dec_TM x) = x" (* this should be easy to achieve *)
    and invalid_enc_TM_rejects: "\<And>x. \<not> is_valid_enc_TM x \<Longrightarrow> TM_decider.rejects (dec_TM x) w" (* a nicer version of: "\<exists>q\<^sub>0 s. dec\<^sub>U x = (rejecting_TM q\<^sub>0 s)" *)

(*
consts bin_TM_enc :: "binTM \<Rightarrow> bin"

specification (bin_TM_enc)
  bin_TM_enc_inj: "inj bin_TM_enc" sorry


definition bin_TM_dec :: "bin \<Rightarrow> binTM" where
  "bin_TM_dec \<equiv> inv bin_TM_enc"

lemma bin_TM_enc_inv: "bin_TM_dec (bin_TM_enc M) = M"
  unfolding bin_TM_dec_def using bin_TM_enc_inj by simp


text\<open>Instantiate the \<^const>\<open>Rej_TM.Rejecting_TM\<close> for \<^typ>\<open>binTM\<close> for the requirement of
 "every string over \<open>{0, 1}\<^sup>*\<close> represents some TM (easy to assure by executing
  an invalid code as a canonic TM that instantly halts and rejects its input)".\<close>

interpretation bin_Rej_TM: Rej_TM "{}::bin_symbol set" "0::nat"
  by (rule Rej_TM.intro) (fact finite.emptyI)

abbreviation bin_rejM :: binTM
  where "bin_rejM \<equiv> Abs_wf_TM bin_Rej_TM.Rejecting_TM"

lemma bin_rejM_simps: "Rep_wf_TM bin_rejM = \<lparr>
    tape_count = 1,
    states = {0},
    start_state = 0,
    final_states = {0},
    accepting_states = {},
    symbols = {blank_class.Bk},
    next_state = \<lambda>q w. 0,
    next_action = \<lambda>q w. [TM.action.Nop]
  \<rparr>"
  using bin_Rej_TM.TM_axioms bin_Rej_TM.Rejecting_TM_def
  by (subst Abs_wf_TM_inverse) auto

lemma wf_bin_rejM: "TM (Rep_wf_TM bin_rejM)"
  using Rep_wf_TM by blast

text\<open>The function that assigns a word to every TM, represented as \<open>\<rho>(M)\<close> in the paper.\<close>

abbreviation TM_encode :: "binTM \<Rightarrow> bin"
  where "TM_encode \<equiv> bin_TM_enc"

definition is_encoded_TM :: "bool list \<Rightarrow> bool"
  where "is_encoded_TM w = (\<exists>M. w = TM_encode M)"

definition TM_decode :: "bool list \<Rightarrow> binTM"
  where "TM_decode w = (if is_encoded_TM w then bin_TM_dec w else bin_rejM)"


lemma TM_codec: "TM_decode (TM_encode M) = M"
  unfolding TM_decode_def is_encoded_TM_def bin_TM_enc_inv by force

lemma decode_TM_wf: "TM (Rep_wf_TM (TM_decode w))"
  using Rep_wf_TM by blast
*)

subsubsection\<open>Exponential Padding\<close>

definition add_exp_pad :: "bool list \<Rightarrow> bool list"
  where [simp]: "add_exp_pad w = (let l = length w in False \<up> (2^l - l) @ w)"

definition strip_exp_pad :: "bool list \<Rightarrow> bool list"
  where [simp]: "strip_exp_pad w = (let l = length w in drop (l - nat_log_ceil 2 l) w)"


value "strip_exp_pad (add_exp_pad [])"

lemma exp_pad_Nil: "strip_exp_pad [] = []" by force

lemma exp_pad_correct[simp]: "w \<noteq> [] \<Longrightarrow> strip_exp_pad (add_exp_pad w) = w"
proof -
  let ?l = "length w"
  let ?pad = "False \<up> (2 ^ ?l - ?l)"
  let ?wp = "?pad @ w"

  assume "w \<noteq> []"
  then have "?l > 0" ..
  then have l_clog2: "nat_log_ceil 2 (2 ^ ?l) = ?l" by (intro log2.ceil_exp)

  have len_pad: "length ?pad = 2 ^ ?l - ?l" by simp
  have len_wp: "length ?wp = 2^?l" unfolding length_append len_pad by simp

  have *: "length ?wp - nat_log_ceil 2 (length ?wp) = length ?pad" unfolding len_wp l_clog2 len_pad ..
  show "strip_exp_pad (add_exp_pad w) = w"
    unfolding add_exp_pad_def strip_exp_pad_def Let_def * by force
qed

lemma exp_pad_suffix: "suffix w (add_exp_pad w)"
  unfolding add_exp_pad_def Let_def by (blast intro: suffixI)

lemma add_exp_pad_len: "length (add_exp_pad w) = 2 ^ length w" by (simp add: Let_def)

lemma drop_diff_length: "n \<le> length xs \<Longrightarrow> length (drop (length xs - n) xs) = n" by simp

lemma strip_exp_pad_len:
  assumes "w \<noteq> []"
  defines "l \<equiv> length w"
  shows "length (strip_exp_pad w) = nat_log_ceil 2 l"
proof -
  from \<open>w \<noteq> []\<close> have "l > 0" unfolding l_def ..
  with log2.ceil_le have "nat_log_ceil 2 l \<le> l" .

  have "length (strip_exp_pad w) = l - (l - nat_log_ceil 2 l)"
    unfolding strip_exp_pad_def l_def[symmetric] Let_def length_drop ..
  also have "... = nat_log_ceil 2 l" using \<open>nat_log_ceil 2 l \<le> l\<close> by (rule diff_diff_cancel)
  finally show ?thesis .
qed


subsection\<open>Arbitrary-length \<open>1\<^sup>+0\<close> prefix\<close>

definition add_al_prefix :: "bool list \<Rightarrow> bool list" where
  "add_al_prefix w = w @ [False, True]"

definition has_al_prefix :: "bool list \<Rightarrow> bool"
  where "has_al_prefix w = (\<exists>n>0. \<exists>w'. w = w' @ [False] @ True \<up> n)"

definition strip_al_prefix :: "bool list \<Rightarrow> bool list"
  where "strip_al_prefix w = rev (drop 1 (dropWhile (\<lambda>b. b = True) (rev w)))"

lemmas alp_simps[simp] = add_al_prefix_def has_al_prefix_def strip_al_prefix_def

lemma add_alp_min: "add_al_prefix w \<noteq> []"
  and add_alp_correct: "has_al_prefix (add_al_prefix w)"
  and alp_correct: "strip_al_prefix (add_al_prefix w) = w"
  and alp_Nil: "strip_al_prefix [] = []" by force+

lemma replicate_takeWhile: "takeWhile (\<lambda>x. x = a) xs = a \<up> length (takeWhile (\<lambda>x. x = a) xs)"
proof (intro replicate_eqI)
  fix y
  assume "y \<in> set (takeWhile (\<lambda>x. x = a) xs)"
  thus "y = a" by (blast dest: set_takeWhileD conjunct2)
qed (rule refl)

lemma replicate_While: "(a \<up> length (takeWhile (\<lambda>x. x = a) xs)) @ dropWhile (\<lambda>x. x = a) xs = xs"
  by (fold replicate_takeWhile) (rule takeWhile_dropWhile_id)

lemma strip_alp_correct1:
  assumes "has_al_prefix w"
  obtains n where "n > 0"
    and "w = strip_al_prefix w @ [False] @ True \<up> n"
proof
  let ?dw = "dropWhile (\<lambda>b. b = True) (rev w)"
  define n where "n \<equiv> length (takeWhile (\<lambda>b. b = True) (rev w))"

  obtain nO wO where "nO > 0" and "w = wO @ [False] @ True \<up> nO"
    using \<open>has_al_prefix w\<close> unfolding has_al_prefix_def by blast
  then have r0: "rev w = True \<up> nO @ False # rev wO" by simp
  moreover from r0 have r1: "rev w = True \<up> nO @ ?dw" by (simp add: dropWhile_append3)
  ultimately have dw_split: "?dw = False # drop 1 ?dw" by simp

  have r2: "rev w = True \<up> n @ ?dw" unfolding n_def replicate_While ..
  also have "... = True \<up> n @ False # drop 1 ?dw" by (fold dw_split) (fact refl)
  finally have "w = rev (True \<up> n @ False # drop 1 ?dw)" by (unfold rev_swap)

  also have "... = strip_al_prefix w @ [False] @ True \<up> n" by force
  finally show "w = strip_al_prefix w @ [False] @ True \<up> n" .

  from r1 r2 have "True \<up> nO @ ?dw = True \<up> n @ ?dw" by (rule subst)
  then have "n = nO" unfolding append_same_eq by simp
  then show "n > 0" using \<open>nO > 0\<close> by blast
qed

lemma strip_alp_correct2:
  "prefix (strip_al_prefix w) w" (is "prefix ?w' w")
proof -
  \<comment> \<open>The following definitions are constructed to fit in the following proof;
    their values are not important.\<close>
  define n where "n \<equiv> Suc (length (takeWhile (\<lambda>b. b) (rev w)))"
  define m where "m \<equiv> length (rev w) - n"

  have "?w' = rev (drop n (rev w))" unfolding n_def strip_al_prefix_def dropWhile_eq_drop by force
  also have "... = take m w" unfolding m_def rev_drop rev_rev_ident ..
  finally have "?w' = take m w" . \<comment> \<open>for some \<open>m\<close>\<close>
  show "prefix ?w' w" unfolding \<open>?w' = take m w\<close> by (rule take_is_prefix)
qed

lemma strip_alp_altdef: "strip_al_prefix (w @ False # True \<up> n) = w"
proof -
  let ?T = "(\<lambda>b. b = True)" and ?Tn = "True \<up> n"
  let ?d = "dropWhile ?T (rev (w @ False # ?Tn))"
  have h0: "x \<in> set ?Tn \<Longrightarrow> ?T x" for x by simp

  have "?d = dropWhile ?T (?Tn @ False # rev w)" by simp
  also have "... = dropWhile ?T (False # rev w)" using h0 by (rule dropWhile_append2)
  also have "... = False # rev w" by simp
  finally have h1: "drop 1 ?d = rev w" by (rule forw_subst) force
  show "strip_al_prefix (w @ False # True \<up> n) = w"
    unfolding strip_al_prefix_def h1 by (rule rev_rev_ident)
qed


subsubsection\<open>Assembling components\<close>
context TM_Encoding
begin

definition enc_TM_pad :: "binTM \<Rightarrow> bool list"
  where "enc_TM_pad M = add_exp_pad (add_al_prefix (enc_TM M))"

definition dec_TM_pad :: "bool list \<Rightarrow> binTM"
  where "dec_TM_pad w = dec_TM (strip_al_prefix (strip_exp_pad w))"

lemma TM_codec_TM_pad: "dec_TM_pad (enc_TM_pad M) = canonical_TM M"
  unfolding dec_TM_pad_def enc_TM_pad_def
  unfolding exp_pad_correct[OF add_alp_min] alp_correct enc_dec_TM ..

lemma wf_TM_has_enc: "\<exists>w. dec_TM_pad w = canonical_TM M"
  using TM_codec_TM_pad by blast


subsubsection\<open>Proving required properties\<close>

text\<open>From @{cite \<open>ch.~3.1\<close> rassOwf2017}:

  ``The encoding that we will use [...] will have the following properties:

  1. every string over \<open>{0, 1}\<^sup>*\<close> represents some TM [...],''\<close>

theorem dec_TM_pad_wf: "valid_TM (Rep_TM (dec_TM_pad w))"
  unfolding dec_TM_pad_def using Rep_TM by blast


text\<open>``2. every TM is represented by infinitely many strings. [...]''\<close>

theorem TM_inf_encs: "infinite {w. dec_TM_pad w = canonical_TM M}"
proof (intro infinite_lists allI bexI CollectI)
  \<comment> \<open>Proof follows the structure of @{thm infinite_lists}:
    For every \<open>l \<in> \<nat>\<close> there exists a word \<open>w\<close> with \<open>length w \<ge> l\<close> that is also in the set.\<close>
  fix l
  define w' where w': "w' = (enc_TM M) @ False # True \<up> l"
  define w where w: "w = add_exp_pad w'"

  show "l \<le> length w" unfolding w w' by force

  have "dec_TM_pad w = dec_TM (strip_al_prefix w')" unfolding w w' dec_TM_pad_def
    by (subst exp_pad_correct) blast+
  also have "... = dec_TM (enc_TM M)" unfolding w' strip_alp_altdef ..
  also have "... = canonical_TM M" by (fact enc_dec_TM)
  finally show "dec_TM_pad w = canonical_TM M" .
qed


text\<open>From @{cite \<open>ch.~4.2\<close> rassOwf2017}:

  ``[The encoding] assures several properties [...]:

  1. [...] an arbitrary word \<open>w'\<close> encoding a TM has at least
             \<open>2\<^bsup>ℓ - \<lceil>log ℓ\<rceil>\<^esup> \<ge> 2\<^bsup>ℓ - log ℓ - 1\<^esup>\<close>
     equivalents \<open>w\<close> in the set \<open>{0, 1}\<^sup>ℓ\<close> that map to \<open>w'\<close>.
     Thus, if a TM \<open>M\<close> is encoded within \<open>ℓ\<close> bits, then [the above equation] counts
     how many equivalent codes for \<open>M\<close> are found at least in \<open>{0, 1}\<^sup>ℓ\<close>.''\<close>

theorem num_equivalent_encodings:
  fixes M w
  defines "l \<equiv> length w"
  assumes "l > 0"
    and "dec_TM_pad w = M"
  shows "2^(l - nat_log_ceil 2 l) \<le> card {w. length w = l \<and> dec_TM_pad w = M}" (is "?lhs \<le> card ?A")
proof -
  from \<open>l > 0\<close> have "w \<noteq> []" unfolding l_def ..
  from \<open>l > 0\<close> have "nat_log_ceil 2 l \<le> l" by (rule log2.ceil_le)

  define w' where "w' \<equiv> strip_exp_pad w"
  have lw': "length w' = nat_log_ceil 2 l" unfolding w'_def l_def using \<open>w \<noteq> []\<close> by (rule strip_exp_pad_len)

  have "?lhs = card {pad::bin. length pad = l - nat_log_ceil 2 l}" using card_bin_len_eq ..
  also have "... = card ((\<lambda>pad. pad @ w') ` {pad. length pad = l - nat_log_ceil 2 l})"
    using card_image[symmetric] inj_imp_inj_on inj_append_L .
  also have "... = card {pad @ w' | pad. length pad = l - nat_log_ceil 2 l}"
    by (intro arg_cong[where f=card]) (rule image_Collect)
  also have "... \<le> card {w. length w = l \<and> dec_TM_pad w = M}"
  proof (intro card_mono)
    show "finite {w. length w = l \<and> dec_TM_pad w = M}" using finite_bin_len_eq by simp
    show "{pad @ w' | pad. length pad = l - nat_log_ceil 2 l} \<subseteq> {w. length w = l \<and> dec_TM_pad w = M}"
    proof safe
      fix pad::bin
      assume lp: "length pad = l - nat_log_ceil 2 l"
      show lpw': "length (pad @ w') = l" unfolding length_append lp lw'
        using \<open>nat_log_ceil 2 l \<le> l\<close> by (rule le_add_diff_inverse2)

      have h1: "drop (l - nat_log_ceil 2 l) pad = []" using lp by (intro drop_all) (rule eq_imp_le)
      have h2: "l - nat_log_ceil 2 l - length pad = 0" unfolding lp by simp
      have h3: "drop (l - nat_log_ceil 2 l) (pad @ w') = w'" unfolding drop_append h1 h2 by simp
      show "dec_TM_pad (pad @ w') = M" unfolding dec_TM_pad_def strip_exp_pad_def
        unfolding lpw' Let_def h3 unfolding w'_def
        using \<open>dec_TM_pad w = M\<close> by (fold dec_TM_pad_def)
    qed
  qed
  finally show ?thesis .
qed


text\<open>``2. The retraction of preceding 1-bits creates the needed infinitude of
        equivalent encodings of every possible TM \<open>M\<close>, as \<^emph>\<open>we can embed any code \<open>\<rho>(M)\<close>
        in a word of length \<open>ℓ\<close> for which \<open>log ℓ > len (\<rho>(M))\<close>.\<close>
        We will need this to prove the hierarchy theorem in Section 4.3.''\<close>

theorem embed_TM_in_len:
  fixes M l
  assumes min_word_len: "nat_log_ceil 2 l \<ge> length (enc_TM M) + 2" \<comment> \<open>The \<open>+2\<close> bits are required for the \<open>1\<^sup>+0\<close>-prefix.

        Note: this theorem technically also holds when the assumption @{thm min_word_len} reads
        \<^term>\<open>nat_log_ceil 2 l > length (enc_TM M) \<longleftrightarrow> nat_log_ceil 2 l \<ge> length (enc_TM M) + 1\<close>,
        but only due to \<^const>\<open>strip_al_prefix\<close> allowing the absence of preceding ones.
        If it were to enforce the constraint of a correct \<open>1\<^sup>+0\<close>-prefix,
        this would no longer be the case.
        Additionally, in the stronger version allows the case of \<^term>\<open>l = 0\<close>,
        so \<^term>\<open>l > 0\<close> would have to be added to the assumption.\<close>
  obtains w
  where "length w = l"
    and "dec_TM_pad w = canonical_TM M"
proof
  have "l > 0" by (rule ccontr) (use min_word_len in simp)
  hence "nat_log_ceil 2 l \<le> l" by (rule log2.ceil_le)

  let ?\<rho>M = "enc_TM M" let ?l\<rho> = "length ?\<rho>M"
  define al_prefix where "al_prefix \<equiv> False # True \<up> (nat_log_ceil 2 l - ?l\<rho> - 1)"
  define w' where "w' \<equiv> ?\<rho>M @ al_prefix"
  have w'_correct: "strip_al_prefix w' = ?\<rho>M" unfolding w'_def al_prefix_def strip_alp_altdef ..
  have "length w' = ?l\<rho> + length al_prefix" unfolding w'_def by simp
  also have "... = ?l\<rho> + (nat_log_ceil 2 l - ?l\<rho> - 1) + 1" unfolding add_left_cancel al_prefix_def
    unfolding length_Cons length_replicate by presburger
  also have "... = nat_log_ceil 2 l - 1 + 1" unfolding add_right_cancel using min_word_len
    by (subst diff_commute, intro le_add_diff_inverse) fastforce
  also have "... = nat_log_ceil 2 l" by (intro le_add_diff_inverse2) (simp add: leI)
  finally have w'_len: "length w' = nat_log_ceil 2 l" .

  define exp_pad where "exp_pad \<equiv> False \<up> (l - nat_log_ceil 2 l)"
  define w where "w \<equiv> exp_pad @ w'"
  have exp_len: "length exp_pad = l - nat_log_ceil 2 l" unfolding exp_pad_def by (rule length_replicate)
  have dexp: "drop (l - nat_log_ceil 2 l) exp_pad = []" unfolding exp_pad_def by force

  have "length w = l - nat_log_ceil 2 l + nat_log_ceil 2 l" unfolding w_def length_append
    unfolding exp_pad_def w'_len length_replicate ..
  also have "... = l" using \<open>nat_log_ceil 2 l \<le> l\<close> by (fact le_add_diff_inverse2)
  finally show "length w = l" .

  have w_correct: "strip_exp_pad w = w'" unfolding strip_exp_pad_def \<open>length w = l\<close> Let_def
    unfolding w_def drop_append dexp exp_len by simp

  show "dec_TM_pad w = canonical_TM M" unfolding dec_TM_pad_def w_correct w'_correct
    by (fact enc_dec_TM)
qed

end \<comment> \<open>\<^locale>\<open>TM_Encoding\<close>\<close>

end
