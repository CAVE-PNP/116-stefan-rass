theory Composition
  imports TM Complexity
begin

locale TM_switch = TM_abbrevs + M1: TM M1 for M1 :: "('q1, 's, 'l1) TM" +
  fixes f :: "'l1 \<Rightarrow> ('q2, 's, 'l2) TM"
  assumes f_tape_count[simp]: "\<And>l. l \<in> M1.labels \<Longrightarrow> TM.k (f l) = M1.k"
    and symbols_eq[simp]: "\<And>l. l \<in> M1.labels \<Longrightarrow> TM.\<Sigma> (f l) = M1.\<Sigma>"
begin

lemma tape_symbols_eq[simp]: "\<And>l. l \<in> M1.labels \<Longrightarrow> TM.\<Sigma>\<^sub>t\<^sub>p (f l) = M1.\<Sigma>\<^sub>t\<^sub>p" by simp

lemmas f_simps = f_tape_count symbols_eq tape_symbols_eq


abbreviation (input) "switch_TM_states \<equiv> Inl ` M1.Q \<union> Inr ` {(l,q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)}"
abbreviation (input) "switch_TM_next_state q hds \<equiv>
  case q of Inl q1 \<Rightarrow>
    let q1' = M1.\<delta>\<^sub>q q1 hds in
    if q1' \<in> M1.F
    then let l = M1.label q1' in Inr (l, TM.q\<^sub>0 (f l))
    else Inl q1'
  | Inr (l, q2) \<Rightarrow> Inr (l, TM.\<delta>\<^sub>q (f l) q2 hds)"
abbreviation (input) "switch_TM_next_write q hds i \<equiv>
  case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>w q1 hds i | Inr (l, q2) \<Rightarrow> TM.\<delta>\<^sub>w (f l) q2 hds i"
abbreviation (input) "switch_TM_next_move q hds i \<equiv>
  case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>m q1 hds i | Inr (l, q2) \<Rightarrow> TM.\<delta>\<^sub>m (f l) q2 hds i"

definition switch_TM_rec :: "('q1 + ('l1 \<times> 'q2), 's, 'l2) TM_record"
  where "switch_TM_rec \<equiv> \<lparr>
    TM_record.tape_count = M1.k,
    symbols = M1.\<Sigma>,
    states = switch_TM_states,
    initial_state = Inl M1.q\<^sub>0,
    final_states = Inr ` {(l,q). l \<in> M1.labels \<and> q \<in> TM.F (f l)},
    label = \<lambda>q. case q of Inr (l, q2) \<Rightarrow> TM.label (f l) q2,
    next_state = switch_TM_next_state,
    next_write = switch_TM_next_write,
    next_move  = switch_TM_next_move
  \<rparr>"

lemma valid_switch_TM: "valid_TM switch_TM_rec" unfolding switch_TM_rec_def
proof (intro valid_TM_I)
  let ?Q = switch_TM_states and ?\<delta>\<^sub>q = switch_TM_next_state and ?\<delta>\<^sub>w = switch_TM_next_write

  have h1: "{(l, q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)} = (\<Union>l\<in>M1.labels. Pair l ` TM.Q (f l))" by blast
  have "finite (\<Union>l\<in>M1.labels. Pair l ` TM.Q (f l))" by blast
  then show "finite ?Q" unfolding h1 by blast

  fix q hds
  assume q: "q \<in> ?Q"
  assume hds: "length hds = M1.k" "set hds \<subseteq> M1.\<Sigma>\<^sub>t\<^sub>p"

  show "?\<delta>\<^sub>q q hds \<in> ?Q" using q
  proof (induction q)
    case (Inl q1)
    then have q1: "q1 \<in> M1.Q" by blast
    with hds show ?case unfolding sum.case Let_def by (induction rule: ifI) blast+
  next
    case (Inr q2)
    then have "q2 \<in> {(l, q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)}" by blast
    then show ?case unfolding sum.case
    proof (induction q2)
      case (Pair l q2')
      then have l: "l \<in> M1.labels" and q2': "q2' \<in> TM.Q (f l)" by blast+
      with hds have "TM.\<delta>\<^sub>q (f l) q2' hds \<in> TM.Q (f l)" by force
      with l show ?case unfolding prod.case by blast
    qed
  qed

  fix i
  assume i: "i < M1.k"

  show "?\<delta>\<^sub>w q hds i \<in> M1.\<Sigma>\<^sub>t\<^sub>p" using q
  proof (induction q)
    case (Inl q1)
    then have q1: "q1 \<in> M1.Q" by blast
    with hds i show ?case unfolding sum.case by blast
  next
    case (Inr q2)
    then have "q2 \<in> {(l, q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)}" by blast
    then show ?case unfolding sum.case
    proof (induction q2)
      case (Pair l q2')
      then have l: "l \<in> M1.labels" and q2': "q2' \<in> TM.Q (f l)" by blast+
      with hds i have "TM.\<delta>\<^sub>w (f l) q2' hds i \<in> TM.\<Sigma>\<^sub>t\<^sub>p (f l)"
        by (intro TM.next_write_valid) (unfold f_simps[OF l])
      then show ?case using l by simp
    qed
  qed
qed (use M1.symbol_axioms(2) in blast)+

end \<comment> \<open>\<^locale>\<open>TM_switch\<close>\<close>

end
