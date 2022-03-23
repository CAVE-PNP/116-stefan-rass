subsection\<open>TM Composition\<close>

theory Composition
  imports TM TM_Hoare
begin

subsubsection\<open>Reordering Tapes\<close>

(* TODO document this section *)

(* TODO consider renaming \<open>is\<close>. it stands for indices, but is a somewhat bad name since it is also an Isabelle keyword *)
definition reorder :: "(nat option list) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "reorder is xs ys = map2 (\<lambda>i x. case is ! i of None \<Rightarrow> x | Some i' \<Rightarrow> nth_or i' x ys) [0..<length xs] xs"

value "reorder [Some 0, Some 2, Some 1, None] [w,x,y,z] [a,b,c]"

lemma reorder_length[simp]: "length (reorder is xs ys) = length xs" unfolding reorder_def by simp

lemma reorder_Nil[simp]: "reorder is xs [] = xs"
  unfolding reorder_def nth_or_Nil case_option_same prod.snd_def[symmetric] by simp

lemma reorder_nth[simp]:
  assumes "i < length xs"
  shows "reorder is xs ys ! i = (case is ! i of None \<Rightarrow> xs ! i | Some i' \<Rightarrow> nth_or i' (xs ! i) ys)"
  using assms unfolding reorder_def by (subst nth_map2) auto

lemma reorder_map[simp]: "map f (reorder is xs ys) = reorder is (map f xs) (map f ys)"
proof -
  let ?m = "\<lambda>d i x. case is ! i of None \<Rightarrow> d x | Some i' \<Rightarrow> nth_or i' (d x) (map f ys)"
  let ?m' = "\<lambda>d (i, x). ?m d i x" and ?id = "\<lambda>x. x"
  have "map f (reorder is xs ys) =
    map (\<lambda>(i, x). f (case is ! i of None \<Rightarrow> x | Some i' \<Rightarrow> nth_or i' x ys)) (zip [0..<length xs] xs)"
    unfolding reorder_def map_map comp_def by force
  also have "... = map2 (?m f) [0..<length xs] xs" unfolding option.case_distrib nth_or_map ..
  also have "... = map ((?m' ?id) \<circ> (\<lambda>(i, x). (i, f x))) (zip [0..<length xs] xs)" by fastforce
  also have "... = map (?m' ?id) (map (\<lambda>(i, x). (i, f x)) (zip [0..<length xs] xs))" by force
  also have "... = map2 (?m ?id) [0..<length xs] (map f xs)"
    unfolding zip_map_map[symmetric] list.map_ident ..
  also have "... = reorder is (map f xs) (map f ys)" unfolding reorder_def by simp
  finally show ?thesis .
qed


definition reorder_inv :: "(nat option list) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "reorder_inv is ys = map
    (\<lambda>i. ys ! (LEAST i'. i'<length is \<and> is ! i' = Some i))
    [0..<if set is \<subseteq> {None} then 0 else Suc (Max (Option.these (set is)))]"


lemma card_these_helper: "card (Option.these (set xs)) \<le> length xs"
proof -
  have "card (Option.these (set xs)) \<le> card (set xs)" by (rule card_these) blast
  also have "... \<le> length xs" by (rule card_length)
  finally show ?thesis .
qed

lemma reorder_inv:
  assumes [simp]: "length xs = length is"
    and items_match: "Option.these (set is) = {0..<length ys}"
  shows "reorder_inv is (reorder is xs ys) = ys"
proof -
  define zs where "zs \<equiv> reorder is xs ys"
  have lz: "length zs = length xs" unfolding zs_def reorder_length ..

  have *: "(if set is \<subseteq> {None} then 0 else Suc (Max (Option.these (set is)))) = length ys"
  proof (rule ifI)
    assume "set is \<subseteq> {None}"
    then have "Option.these (set is) = {}" unfolding these_empty_eq subset_singleton_iff .
    then have "{0..<length ys} = {}" unfolding items_match .
    then show "0 = length ys" by simp
  next
    assume "\<not> set is \<subseteq> {None}"
    then have "Option.these (set is) \<noteq> {}" unfolding these_empty_eq subset_singleton_iff .
    then have "0 < length ys" unfolding items_match by simp
    then show "Suc (Max (Option.these (set is))) = length ys"
      unfolding items_match Max_atLeastLessThan_nat[OF \<open>length ys > 0\<close>] by simp
  qed

  have "length ys = card (Option.these (set is))" unfolding items_match by simp
  also have "... \<le> length is" by (rule card_these_helper)
  finally have ls: "length is \<ge> length ys" .

  have "reorder_inv is (reorder is xs ys) = map ((!) ys) [0..<length ys]"
    unfolding reorder_inv_def zs_def[symmetric] lz *
  proof (intro list.map_cong0)
    fix n assume "n \<in> set [0..<length ys]"
    then have [simp]: "n < length ys" by simp
    then have *: "[0..<length ys] ! n = n" by simp

    define i where "i = (LEAST i. i < length is \<and> is ! i = Some n)"

    from \<open>n < length ys\<close> have "n \<in> Option.these (set is)" unfolding items_match by simp
    then have "Some n \<in> set is" unfolding these_altdef by force
    then have ex_i[simp]: "\<exists>i. i < length is \<and> is ! i = Some n" unfolding in_set_conv_nth .

    then have "i < length is \<and> is ! i = Some n" unfolding i_def by (rule LeastI_ex)
    then have [simp]: "i < length is" and [simp]: "is ! i = Some n" by blast+
    then have [simp]: "[0..<length is] ! i = i" by simp

    show "zs ! (LEAST i'. i' < length is \<and> is ! i' = Some n) = ys ! n"
      unfolding i_def[symmetric] zs_def reorder_def by simp
  qed
  then show ?thesis unfolding map_nth .
qed

definition reorder_config :: "(nat option list) \<Rightarrow> 's tape list \<Rightarrow> ('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "reorder_config is tps c = TM_config (state c) (reorder is tps (tapes c))"

lemma reorder_config_length[simp]: "length (tapes (reorder_config p tps c)) = length tps"
  unfolding reorder_config_def by simp

lemma reorder_config_simps[simp]:
  shows reorder_config_state: "state (reorder_config is tps c) = state c"
    and reorder_config_tapes: "tapes (reorder_config is tps c) = reorder is tps (tapes c)"
  unfolding reorder_config_def by simp_all


locale TM_reorder_tapes =
  fixes M :: "('q, 's::finite) TM"
    and "is" :: "nat option list"
  assumes items_match: "Option.these (set is) = {0..<TM.tape_count M}"
begin
sublocale TM .

abbreviation "k' \<equiv> length is"

abbreviation "r \<equiv> reorder is"
abbreviation "rc \<equiv> reorder_config is"
abbreviation r_inv ("r\<inverse>") where "r_inv \<equiv> reorder_inv is"

lemma k_k': "k \<le> k'"
proof -
  have "k = card {0..<k}" by simp
  also have "... = card (Option.these (set is))" unfolding items_match ..
  also have "... \<le> card (set is)" by (rule card_these) blast
  also have "... \<le> k'" by (rule card_length)
  finally show "k \<le> k'" .
qed

definition reorder_tapes_rec :: "('q, 's) TM_record"
  where "reorder_tapes_rec \<equiv>
    M_rec \<lparr>
      tape_count := k',
      next_state := \<lambda>q hds. \<delta>\<^sub>q q (r\<inverse> hds),
      next_write := \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>w q (r\<inverse> hds) i) | None \<Rightarrow> hds ! i,
      next_move  := \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>m q (r\<inverse> hds) i) | None \<Rightarrow> No_Shift
    \<rparr>"

lemma reorder_tapes_rec_simps: "reorder_tapes_rec = \<lparr>
  TM_record.tape_count = k',
  states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sup>+,
  next_state = \<lambda>q hds. \<delta>\<^sub>q q (r\<inverse> hds),
  next_write = \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>w q (r\<inverse> hds) i) | None \<Rightarrow> hds ! i,
  next_move  = \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>m q (r\<inverse> hds) i) | None \<Rightarrow> No_Shift
\<rparr>" unfolding reorder_tapes_rec_def by simp

definition "M' \<equiv> Abs_TM reorder_tapes_rec"

lemma M'_valid: "is_valid_TM reorder_tapes_rec"
  unfolding reorder_tapes_rec_simps
proof (unfold_locales, unfold TM_record.simps)
  from at_least_one_tape and k_k' show "1 \<le> k'" by simp
qed (fact TM_axioms)+

sublocale M': TM M' .

lemma M'_rec: "M'.M_rec = reorder_tapes_rec" using Abs_TM_inverse M'_valid by (auto simp add: M'_def)
lemmas M'_fields = M'.TM_fields_defs[unfolded M'_rec reorder_tapes_rec_simps TM_record.simps]
lemmas [simp] = M'_fields(1-6)

lemma reorder_step:
  assumes "wf_config c"
    and l_tps': "length (tapes c') = k'"
  shows "M'.step (rc (tapes c') c) = rc (tapes c') (step c)"
    (is "M'.step (?rc c) = ?rc (step c)")
proof (cases "is_final c")
  assume "is_final c"
  then have "M'.is_final (?rc c)" by simp
  then have "M'.step (?rc c) = (?rc c)" by fast
  also from \<open>is_final c\<close> have "... = ?rc (step c)" by simp
  finally show ?thesis .
next
  let ?c' = "?rc c"
  let ?q = "state c" and ?q' = "state ?c'"
  let ?tps = "tapes c" and ?hds = "heads c"

  let ?rt = "r (tapes c')"
  let ?hds' = "r (heads c') ?hds" and ?tps' = "?rt ?tps"

  from \<open>wf_config c\<close> have l_tps: "length (tapes c) = k" by simp
  then have l_hds: "length (heads c) = k" by simp
  from l_tps' have l_hds': "length (heads c') = k'" by simp

  moreover have "Option.these (set is) = {0..<length ?hds}" unfolding l_hds items_match ..
  ultimately have r_inv_hds[simp]: "reorder_inv is (reorder is (heads c') ?hds) = ?hds" by (rule reorder_inv)

  assume "\<not> is_final c"
  then have "M'.step ?c' = M'.step_not_final ?c'" by simp
  also have "... = ?rc (step_not_final c)"
  proof (intro TM_config.expand conjI)
    have "state (M'.step_not_final ?c') = M'.\<delta>\<^sub>q ?q ?hds'"
      unfolding M'.step_not_final_def by (simp add: Let_def)
    also have "... = \<delta>\<^sub>q ?q ?hds" unfolding M'_fields by simp
    also have "... = state (?rc (step_not_final c))" by simp
    finally show "state (M'.step_not_final ?c') = state (?rc (step_not_final c))" .

    from k_k' have min_k_k': "min k M'.k = k" by simp
    have lr: "length (reorder is (tapes c') x) = M'.k" for x by (simp add: l_tps')

    have "tapes (M'.step_not_final ?c') = map2 tape_action (M'.\<delta>\<^sub>a ?q ?hds') ?tps'"
      unfolding M'.step_not_final_def by (simp add: Let_def)
    also have "... = r (tapes c') (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps)"
    proof (rule M'.step_not_final_eqI)
      fix i assume "i < M'.k"
      then have [simp]: "i < k'" by simp

      show "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i) =
        ?rt (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps) ! i"
      proof (induction "is ! i")
        case None
        then have [simp]: "is ! i = None" ..
        from \<open>i < k'\<close> have "reorder is xs ys ! i = xs ! i" if "length xs = k'" for xs ys :: "'x list"
          using that by simp
        note * = this[OF l_tps'] this[OF l_hds']
        from \<open>i < k'\<close> have [simp]: "map head (tapes c') ! i = head (tapes c' ! i)"
          by (intro nth_map) (unfold l_tps')
        show ?case unfolding M'_fields * by simp
      next
        case (Some i')
        then have [simp]: "is ! i = Some i'" ..

        from \<open>i < k'\<close> have "i \<in> {0..<k'}" by simp
        then have "Some i' \<in> set is" unfolding \<open>Some i' = is ! i\<close> using \<open>i < k'\<close> nth_mem by blast
        then have "i' \<in> {0..<k}" unfolding items_match[symmetric] in_these_eq .
        then have [simp]: "i' < k" by simp

        then have nth_i': "nth_or i' x xs = xs ! i'" if "length xs = k" for x :: 'x and xs
          unfolding nth_or_def \<open>length xs = k\<close> by (rule if_P)
        from \<open>i < k'\<close> have "i < length (tapes c')" unfolding l_tps' .
        then have r_nth_or: "reorder is (tapes c') tps ! i = nth_or i' (tapes c' ! i) tps" for tps
          by simp

        have \<delta>\<^sub>w': "M'.\<delta>\<^sub>w ?q ?hds' i = \<delta>\<^sub>w (state c) (heads c) i'"
         and \<delta>\<^sub>m': "M'.\<delta>\<^sub>m ?q ?hds' i = \<delta>\<^sub>m (state c) (heads c) i'"
          unfolding M'_fields by simp_all

        have "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i) =
              tape_action (   \<delta>\<^sub>w ?q ?hds i',    \<delta>\<^sub>m ?q ?hds i') (?tps ! i')"
          unfolding \<delta>\<^sub>w' \<delta>\<^sub>m' unfolding r_nth_or nth_i'[OF l_tps] ..
        also have "... = tape_action (\<delta>\<^sub>a ?q ?hds ! i') (?tps ! i')" by simp
        also have "... = map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps ! i'" by (auto simp add: l_tps)
        also have "... = ?rt (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps) ! i"
          unfolding r_nth_or by (rule nth_i'[symmetric]) (simp add: l_tps)
        finally show ?case .
      qed
    qed (fact lr)+
    also have "... = tapes (?rc (step_not_final c))" by (simp add: Let_def)
    finally show "tapes (M'.step_not_final ?c') = tapes (?rc (step_not_final c))" .
  qed
  also from \<open>\<not> is_final c\<close> have "... = ?rc (step c)" by simp
  finally show ?thesis .
qed

corollary reorder_steps:
  fixes c c' :: "('q, 's) TM_config"
  assumes wfc: "wf_config c"
    and wfc': "length (tapes c') = k'"
  shows "M'.steps n (rc (tapes c') c) = rc (tapes c') (steps n c)"
proof (induction n)
  case (Suc n)
  from \<open>wf_config c\<close> have wfcs: "wf_config (steps n c)" by blast
  show ?case unfolding funpow.simps comp_def Suc.IH reorder_step[OF wfcs wfc'] ..
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

corollary reorder_run':
  fixes c' :: "('q, 's) TM_config"
  assumes "length (tapes c') = k'"
  shows "M'.steps n (rc (tapes c') (initial_config w)) = rc (tapes c') (run n w)"
  unfolding run_def reorder_steps[OF wf_initial_config assms] ..

lemma init_conf_eq:
  assumes "\<forall>i<k'. i = 0 \<longleftrightarrow> is ! i = Some 0"
  shows "M'.initial_config w = rc (\<langle>\<rangle> \<up> k') (initial_config w)"
  (is "?c0' = rc (\<langle>\<rangle> \<up> k') ?c0")
proof (rule TM_config_eq)
  let ?r = "reorder is (\<langle>\<rangle> \<up> k')" and ?rc = "reorder_config is (\<langle>\<rangle> \<up> k')"
  let ?t0 = "\<lambda>k. <w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1)"

  show "tapes ?c0' = tapes (?rc ?c0)"
  proof (rule nth_equalityI)
    fix i assume "i < length (tapes ?c0')"
    then have "i < k'" by simp

    then have "(<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (M'.k - 1)) ! i = ?r (<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1)) ! i" unfolding M'_fields
    proof (induction i)
      case 0
      with assms have [simp]: "is ! 0 = Some 0" by blast
      from \<open>0 < k'\<close> show ?case by (subst reorder_nth) auto
    next
      case (Suc i)
      with assms have "is ! Suc i \<noteq> Some 0" by blast

      have h1: "k' = Suc (k' - 1)" using M'.at_least_one_tape
        unfolding M'_fields by (intro Suc_pred') linarith
      have h2: "\<langle>\<rangle> \<up> k' = \<langle>\<rangle> # \<langle>\<rangle> \<up> (k' - 1)" by (subst h1) simp

      from \<open>Suc i < k'\<close> have h3: "(\<langle>\<rangle> \<up> k') ! Suc i = \<langle>\<rangle>" by simp
      then have h4: "(\<langle>\<rangle> \<up> (k' - 1)) ! i = \<langle>\<rangle>" unfolding h2 unfolding nth_Cons_Suc .

      from \<open>Suc i < k'\<close> have "Suc i < length (\<langle>\<rangle> \<up> k')" by simp
      note reorder_i = reorder_nth[OF this]

      show ?case unfolding nth_Cons_Suc unfolding reorder_i h3 h4
      proof (induction "is ! Suc i")
        case None thus ?case by simp
      next
        case (Some i')
        then have i': "is ! Suc i = Some i'" ..
        from \<open>is ! Suc i \<noteq> Some 0\<close> have "i' > 0" unfolding i' by simp
        then obtain i'' where i'': "i' = Suc i''" by (rule lessE)

        from items_match and \<open>Suc i < k'\<close> have "i' < k" using i'
          by (metis atLeastLessThan_iff in_these_eq nth_mem)

        then have "i' < length (?t0 k)" by simp
        then show ?case unfolding i' i'' by simp
      qed
    qed
    then show "tapes ?c0' ! i = tapes (?rc ?c0) ! i"
      unfolding TM.initial_config_def reorder_config_def TM_config.sel .
  qed simp
qed simp

corollary reorder_run:
  fixes c' :: "('q, 's) TM_config"
  assumes "\<forall>i<k'. i = 0 \<longleftrightarrow> is ! i = Some 0"
  shows "M'.run n w = rc (\<langle>\<rangle> \<up> k') (run n w)"
proof -
  let ?rc = "rc (tapes (conf q\<^sub>0 (\<langle>\<rangle> \<up> k')))"
  have "M'.run n w = M'.steps n (?rc (initial_config w))"
    unfolding M'.run_def init_conf_eq[OF assms] by simp
  also have "... = ?rc (run n w)" by (subst reorder_run') auto
  finally show ?thesis by simp
qed

corollary reorder_time:
  fixes c' :: "('q, 's) TM_config"
  assumes "\<forall>i<k'. i = 0 \<longleftrightarrow> is ! i = Some 0"
  shows "M'.time w = time w"
  unfolding TM.time_altdef reorder_run[OF assms] by simp

end \<comment> \<open>\<^locale>\<open>TM_reorder_tapes\<close>\<close>


context TM
begin

definition reorder_tapes :: "nat option list \<Rightarrow> ('q, 's::finite) TM"
  where "reorder_tapes is \<equiv> TM_reorder_tapes.M' M is"

corollary reorder_tapes_steps:
  fixes c c' :: "('q, 's) TM_config"
  assumes "wf_config c"
    and "length (tapes c') = length is"
    and "Option.these (set is) = {0..<k}"
  shows "TM.steps (reorder_tapes is) n (reorder_config is (tapes c') c) = reorder_config is (tapes c') (steps n c)"
  unfolding reorder_tapes_def using assms
  by (intro TM_reorder_tapes.reorder_steps) (unfold_locales)

definition tape_offset :: "nat \<Rightarrow> nat \<Rightarrow> nat option list"
  where "tape_offset a b \<equiv> None\<up>a @ (map Some [0..<k]) @ None\<up>b"

lemma tape_offset_length[simp]: "length (tape_offset a b) = a + k + b"
  unfolding tape_offset_def by simp

lemma tape_offset_valid: "Option.these (set (tape_offset a b)) = {0..<k}"
proof -
  let ?o = "tape_offset a b"
  have [simp]: "set ?o = set (None \<up> a) \<union> Some ` {0..<k} \<union> set (None \<up> b)"
    unfolding tape_offset_def by force
  have [simp]: "Option.these (set (None \<up> i)) = {}" for i by (induction i) auto
  show "Option.these (set ?o) = {0..<k}" by simp
qed

theorem tape_offset_steps:
  fixes c c' :: "('q, 's) TM_config"
    and a b :: nat
  defines "is \<equiv> tape_offset a b"
  assumes "wf_config c"
    and "length (tapes c') = length is"
  shows "TM.steps (reorder_tapes is) n (reorder_config is (tapes c') c) = reorder_config is (tapes c') (steps n c)"
  using assms tape_offset_valid unfolding reorder_tapes_def is_def
  by (intro TM_reorder_tapes.reorder_steps) (unfold_locales)

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


locale TM_tape_offset =
  fixes M :: "('q, 's::finite) TM"
    and a b :: nat
begin
sublocale TM M .

abbreviation "is \<equiv> tape_offset a b"

sublocale TM_reorder_tapes M "is" using tape_offset_valid by unfold_locales


lemma tape_offset_helper[intro]:
  assumes "a = 0"
  shows "\<forall>i<k'. i = 0 \<longleftrightarrow> is ! i = Some 0"
proof (intro allI impI)
  fix i assume "i < k'"
  show "(i = 0) = (is ! i = Some 0)"
  proof (cases "i < k")
    assume "i < k"
    have "is ! i = (map Some [0..<k] @ None \<up> b) ! i" unfolding \<open>a = 0\<close> TM.tape_offset_def by simp
    also from \<open>i < k\<close> have "... = map Some [0..<k] ! i" by (subst nth_append, intro if_P) simp
    also from \<open>i < k\<close> have "... = Some i" by force
    finally show ?thesis by simp
  next
    assume "\<not> i < k"
    with \<open>i < k'\<close> have "i - k < b" unfolding tape_offset_length \<open>a = 0\<close> by (subst less_diff_conv2) presburger+
    have "is ! i = (map Some [0..<k] @ None \<up> b) ! i" unfolding \<open>a = 0\<close> TM.tape_offset_def by simp
    also from \<open>\<not> i < k\<close> have "... = (None \<up> b) ! (i - k)" by (subst nth_append) fastforce
    also from \<open>i - k < b\<close> have "... = None" by (rule nth_replicate)
    finally have "is ! i \<noteq> Some 0" by simp
    moreover from \<open>\<not> i < k\<close> and at_least_one_tape have "i \<noteq> 0" by simp
    ultimately show ?thesis by blast
  qed
qed

end \<comment> \<open>\<^locale>\<open>TM_tape_offset\<close>\<close>


subsubsection\<open>Change Alphabet\<close>

locale TM_map_alphabet =
  fixes M :: "('q, 's1::finite) TM"
    and f :: "'s1 \<Rightarrow> 's2::finite"
  assumes inj_f: "inj f"
begin
sublocale TM .

abbreviation f' where "f' \<equiv> map_option f"
definition f_inv ("f\<inverse>") where "f_inv \<equiv> inv f"
abbreviation f'_inv ("f''\<inverse>") where "f'_inv \<equiv> map_option f_inv"

lemma inv_f_f[simp]: "f_inv (f x) = x" "f_inv \<circ> f = (\<lambda>x. x)"
  unfolding comp_def f_inv_def using inj_f by simp_all
lemma inv_f'_f'[simp]: "f'_inv (f' x) = x" "f'_inv \<circ> f' = (\<lambda>x. x)"
  by (simp_all add: comp_def option.map_comp option.map_ident)
lemma map_f'_inv: "map f'_inv (map f' xs) = xs" by simp


definition fc where "fc \<equiv> map_conf_tapes f"

lemma fc_simps[simp]:
  shows "state (fc c) = state c"
    and "tapes (fc c) = map (map_tape f) (tapes c)"
  unfolding fc_def TM_config.map_sel by (rule refl)+

definition map_alph_rec :: "('q, 's2) TM_record"
  where "map_alph_rec \<equiv> \<lparr>
    TM_record.tape_count = k,
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sup>+,
    next_state = \<lambda>q hds. if set hds \<subseteq> range f' then \<delta>\<^sub>q q (map f'_inv hds) else q,
    next_write = \<lambda>q hds i. if set hds \<subseteq> range f' then f' (\<delta>\<^sub>w q (map f'_inv hds) i) else hds ! i,
    next_move  = \<lambda>q hds i. if set hds \<subseteq> range f' then \<delta>\<^sub>m q (map f'_inv hds) i else N
  \<rparr>"

lemma M'_valid: "is_valid_TM map_alph_rec"
  unfolding map_alph_rec_def
proof (unfold_locales, unfold TM_record.simps)
  fix q hds assume "q \<in> Q"
  then show "(if set hds \<subseteq> range f' then \<delta>\<^sub>q q (map f'\<inverse> hds) else q) \<in> Q" by simp
qed (fact TM_axioms)+

definition "M' \<equiv> Abs_TM map_alph_rec"
sublocale M': TM M' .

lemma M'_rec: "M'.M_rec = map_alph_rec" using Abs_TM_inverse M'_valid by (auto simp add: M'_def)
lemmas M'_fields = M'.TM_fields_defs[unfolded M'_rec map_alph_rec_def TM_record.simps]
lemmas [simp] = M'_fields(1-6)

lemma map_step:
  assumes [simp]: "length (tapes c) = k"
  shows "M'.step (fc c) = fc (step c)"
proof (cases "is_final c") (* TODO extract this pattern as lemma *)
  assume "is_final c"
  then show ?thesis by simp
next
  let ?c' = "fc c"
  let ?q = "state c" and ?q' = "state ?c'"
  let ?tps = "tapes c" and ?hds = "heads c"

  let ?ft = "map (map_tape f)"
  let ?hds' = "map f' ?hds" and ?tps' = "?ft ?tps"

  assume "\<not> is_final c"
  then have "M'.step ?c' = M'.step_not_final ?c'" by simp
  also have "... = fc (step_not_final c)"
  proof (rule TM_config_eq)
    have set_hds'[intro]: "set ?hds' \<subseteq> range f'" by blast
    then show "state (M'.step_not_final ?c') = state (fc (step_not_final c))"
      unfolding fc_simps TM.step_not_final_simps M'_fields by (simp add: comp_def tape.map_sel)

    show "tapes (M'.step_not_final ?c') = tapes (fc (step_not_final c))"
      unfolding TM.step_not_final_simps
    proof (intro TM.step_not_final_eqI, unfold fc_simps map_head_tapes)
      fix i assume "i < M'.k"
      then have [simp]: "i < k" by simp

      then have **: "?tps' ! i = map_tape f (tapes c ! i)" by simp
      have *: "(if set ?hds' \<subseteq> range f' then a else b) = a" for a b :: 'x by (blast intro: if_P)

      have "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i)
          = tape_action (f' (\<delta>\<^sub>w ?q ?hds i), \<delta>\<^sub>m ?q ?hds i) (?tps' ! i)"
        unfolding M'_fields * map_f'_inv ..
      also have "... = tape_action (f' (\<delta>\<^sub>w ?q ?hds i), \<delta>\<^sub>m ?q ?hds i) (map_tape f (?tps ! i))"
        by (subst nth_map) auto
      also have "... = map_tape f (tape_action (\<delta>\<^sub>w ?q ?hds i, \<delta>\<^sub>m ?q ?hds i) (?tps ! i))" by simp
      also have "... = ?ft (tapes (step_not_final c)) ! i" by simp
      finally show "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i) =
         ?ft (tapes (step_not_final c)) ! i" .
    qed simp_all
  qed
  also from \<open>\<not> is_final c\<close> have "... = fc (step c)" by simp
  finally show ?thesis .
qed

corollary map_steps:
  assumes l_tps: "length (tapes c) = k"
  shows "M'.steps n (fc c) = fc (steps n c)"
  using assms
proof (induction n)
  case (Suc n)
  then have IH: "M'.steps n (fc c) = fc (steps n c)" by blast
  from \<open>length (tapes c) = k\<close> have l_tpss: "length (tapes (steps n c)) = k" by (rule steps_l_tps)

  show ?case unfolding funpow.simps comp_def IH map_step[OF l_tpss] ..
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

corollary map_run[simp]: "M'.run n (map f w) = fc (run n w)"
proof -
  have *: "M'.initial_config (map f w) = fc (initial_config w)"
    unfolding TM.initial_config_def by (rule TM_config_eq) auto
  show "M'.run n (map f w) = fc (run n w)" unfolding TM.run_def * map_steps[OF init_conf_len] ..
qed

corollary map_time[simp]: "M'.time (map f w) = time w" unfolding TM.time_altdef map_run by simp


end \<comment> \<open>\<^locale>\<open>TM_map_alphabet\<close>\<close>

context TM
begin


definition map_alphabet :: "('s \<Rightarrow> 's2::finite) \<Rightarrow> ('q, 's2) TM"
  where "map_alphabet f \<equiv> TM_map_alphabet.M' M f"

theorem map_alphabet_steps:
  fixes f :: "'s \<Rightarrow> 's2::finite"
  assumes "length (tapes c) = k"
    and "inj f"
  shows "TM.steps (map_alphabet f) n (map_conf_tapes f c) = map_conf_tapes f (steps n c)"
proof -
  interpret TM_map_alphabet M f using \<open>inj f\<close> by (unfold_locales)
  from \<open>length (tapes c) = k\<close> have "M'.steps n (fc c) = fc (steps n c)" by (rule map_steps)
  then show ?thesis unfolding map_alphabet_def fc_def .
qed

end


subsubsection\<open>Simple Composition\<close>

locale simple_TM_comp = TM_abbrevs +
  fixes M1 :: "('q1, 's::finite) TM"
    and M2 :: "('q2, 's::finite) TM"
  assumes k[simp]: "TM.tape_count M1 = TM.tape_count M2"
begin
sublocale M1: TM M1 .
sublocale M2: TM M2 .

text\<open>Note: the current definition will not work correctly when execution starts from one of
  \<^term>\<open>M1\<close>' final states (\<^term>\<open>state c \<in> Inl ` M1.F\<close>).
  In this case, it would just execute the actions specified by \<^const>\<open>M1.\<delta>\<^sub>a\<close>,
  even though it should (immediately) proceed to \<^const>\<open>M2.q\<^sub>0\<close>.

  However, the behavior for \<^const>\<open>TM.run\<close> (starting in the \<^const>\<open>TM.initial_state\<close>) is as expected.
  If \<^term>\<open>M1.q\<^sub>0 \<in> M1.F\<close> then the resulting TM will start directly with \<^const>\<open>M2.q\<^sub>0\<close>.

  While it is possible to patch the behavior for arbitrary execution with unchanged ``normal'' behavior
  (by checking if the current state is final in the transition function),
  this adds complexity and the annoying property that the resulting TM will
  perform one additional step to transition to \<^const>\<open>M2.q\<^sub>0\<close>.
  This would cause the running time to be greater than the running time of \<^term>\<open>M1\<close> and \<^term>\<open>M2\<close> combined.\<close>
  (* this "bug" is also present in \<open>tm_comp\<close> for the old TM defs *)

definition comp_rec :: "('q1 + 'q2, 's) TM_record"
  where "comp_rec \<equiv> \<lparr>
    TM_record.tape_count = M1.k,
    states = Inl ` M1.Q \<union> Inr ` M2.Q,
    initial_state = if M1.q\<^sub>0 \<in> M1.F then Inr M2.q\<^sub>0 else Inl M1.q\<^sub>0,
    final_states = Inr ` M2.F,
    accepting_states = Inr ` M2.F\<^sub>A,
    next_state = \<lambda>q hds. case q of Inl q1 \<Rightarrow> let q1' = M1.\<delta>\<^sub>q q1 hds in
                                             if q1' \<in> M1.F then Inr M2.q\<^sub>0 else Inl q1'
                                 | Inr q2 \<Rightarrow> Inr (M2.\<delta>\<^sub>q q2 hds),
    next_write = \<lambda>q hds i. case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>w q1 hds i | Inr q2 \<Rightarrow> M2.\<delta>\<^sub>w q2 hds i,
    next_move  = \<lambda>q hds i. case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>m q1 hds i | Inr q2 \<Rightarrow> M2.\<delta>\<^sub>m q2 hds i
  \<rparr>"

lemma M_valid: "is_valid_TM comp_rec" unfolding comp_rec_def
proof (unfold_locales, unfold TM.simps)
  show "(if M1.q\<^sub>0 \<in> M1.F then Inr M2.q\<^sub>0 else Inl M1.q\<^sub>0) \<in> Inl ` M1.Q \<union> Inr ` M2.Q"
    by (rule if_cases) blast+

  fix q hds
  assume "q \<in> Inl ` M1.Q \<union> Inr ` M2.Q"
  then show "(case q of Inl q1 \<Rightarrow> let q1' = M1.\<delta>\<^sub>q q1 hds in if q1' \<in> M1.F then Inr M2.q\<^sub>0 else Inl q1'
        | Inr q2 \<Rightarrow> Inr (M2.\<delta>\<^sub>q q2 hds))
       \<in> Inl ` M1.Q \<union> Inr ` M2.Q" (is "(case q of Inl q1 \<Rightarrow> ?l q1 | Inr q2 \<Rightarrow> ?r q2) \<in> ?Q")
  proof (induction q)
    case (Inl q1)
    show ?case unfolding sum.case Let_def by (rule if_cases) (use Inl in blast)+
  next
    case (Inr q2)
    then show ?case unfolding sum.case by blast
  qed
qed (use M2.TM_axioms(4-5) in blast)+

definition "M \<equiv> Abs_TM comp_rec"

sublocale TM M .

lemma M_rec: "M_rec = comp_rec" unfolding M_def using M_valid by (intro Abs_TM_inverse CollectI)
lemmas M_fields = TM_fields_defs[unfolded M_rec comp_rec_def TM_record.simps Let_def]
lemmas [simp] = M_fields(1-6)

lemma next_state_simps[simp]:
  shows "M1.\<delta>\<^sub>q q1 hds \<in> M1.F \<Longrightarrow> \<delta>\<^sub>q (Inl q1) hds = Inr M2.q\<^sub>0"
    and "M1.\<delta>\<^sub>q q1 hds \<notin> M1.F \<Longrightarrow> \<delta>\<^sub>q (Inl q1) hds = Inl (M1.\<delta>\<^sub>q q1 hds)"
    and "\<delta>\<^sub>q (Inr q2) hds = Inr (M2.\<delta>\<^sub>q q2 hds)"
  unfolding M_fields by auto

definition cl :: "('q1, 's) TM_config \<Rightarrow> ('q1 + 'q2, 's) TM_config"
  where "cl \<equiv> map_conf_state Inl"
definition cl' :: "('q1 + 'q2, 's) TM_config \<Rightarrow> ('q1, 's) TM_config"
  where "cl' \<equiv> map_conf_state projl"

lemma cl_state[simp]: "state (cl c) = Inl (state c)" unfolding cl_def by simp
lemma cl'_tapes[simp]: "tapes (cl' c) = tapes c" unfolding cl'_def by simp

lemma cl'_cl[simp]: "cl' (cl c) = c" unfolding cl_def cl'_def TM_config.map_comp comp_def sum.sel TM_config.map_ident ..

lemma cl_cl'[simp]: "isl (state c) \<Longrightarrow> cl (cl' c) = c"
proof (induction c)
  case (TM_config q tps)
  then obtain q1 where q1: "q = Inl q1" by (induction q) auto
  show ?case unfolding cl_def cl'_def TM_config.map_comp comp_def q1
    unfolding TM_config.map sum.sel tape.map_ident by simp
qed

lemma comp_step1_not_final:
  assumes "isl (state c)" (* TODO there may be a more streamlined way to word this assumption *)
    and step_nf: "\<not> M1.is_final (M1.step (cl' c))"
  shows "step c = cl (M1.step (cl' c))"
proof -
  from step_nf have nf': "\<not> M1.is_final (cl' c)" by blast
  with \<open>isl (state c)\<close> have nf: "\<not> is_final c" by auto

  then have "step c = step_not_final c" by blast
  also have "... = cl (M1.step_not_final (cl' c))"
  proof (rule TM_config_eq)
    from \<open>isl (state c)\<close> obtain q1 where [simp]: "state c = Inl q1" unfolding isl_def ..
    then have [simp]: "state (cl' c) = q1" unfolding cl'_def by simp
    from step_nf have *: "M1.\<delta>\<^sub>q q1 (heads c) \<notin> M1.F" using nf' by simp
    from nf' have [simp]: "q1 \<notin> M1.F" by simp

    show "state (step_not_final c) = state (cl (M1.step_not_final (cl' c)))" using * by force
    show "tapes (step_not_final c) = tapes (cl (M1.step_not_final (cl' c)))"
      unfolding cl_def by (simp add: M_fields(8-9))
  qed
  also from nf' have "... = cl (M1.step (cl' c))" by simp
  finally show ?thesis .
qed

lemma comp_step1_next_final:
  assumes "isl (state c)"
    and nf': "\<not> M1.is_final (cl' c)"
    and step_final: "M1.is_final (M1.step (cl' c))"
  shows "step c = conf (Inr M2.q\<^sub>0) (tapes (M1.step (cl' c)))"
proof -
  from assms(1-2) have nf: "\<not> is_final c" by auto

  then have "step c = step_not_final c" by blast
  also have "... = conf (Inr M2.q\<^sub>0) (tapes (M1.step_not_final (cl' c)))"
  proof (rule TM_config_eq, unfold TM_config.sel)
    from \<open>isl (state c)\<close> obtain q1 where [simp]: "state c = Inl q1" unfolding isl_def ..
    then have [simp]: "state (cl' c) = q1" unfolding cl'_def by simp
    from step_final have *: "M1.\<delta>\<^sub>q q1 (heads c) \<in> M1.F" using nf' by simp
    from nf' have [simp]: "q1 \<notin> M1.F" by simp

    show "state (step_not_final c) = Inr M2.q\<^sub>0" using * by force
    show "tapes (step_not_final c) = tapes (M1.step_not_final (cl' c))" by (simp add: M_fields(8-9))
  qed
  also from nf' have "... = conf (Inr M2.q\<^sub>0) (tapes (M1.step (cl' c)))"
    by (subst M1.step_simps(2)) blast+
  finally show ?thesis .
qed

lemma comp_steps1:
  assumes "n < M1.config_time c"
  shows "steps n (cl c) = cl (M1.steps n c)"
proof -
  have "0 \<le> n" by (rule le0)
  then show "steps n (cl c) = cl (M1.steps n c)"
  proof (induction n rule: dec_induct)
    case base
    show "steps 0 (cl c) = cl (M1.steps 0 c)" unfolding funpow_0 cl_def[symmetric] ..
  next
    case (step n')
    have "steps (Suc n') (cl c) = step (steps n' (cl c))" unfolding funpow.simps comp_def ..
    also have "... = step (cl (M1.steps n' c))" unfolding step.IH ..
    also have "... = cl (M1.step (cl' (cl (M1.steps n' c))))"
    proof (rule comp_step1_not_final)
      show "isl (state (cl (M1.steps n' c)))" by simp
      from \<open>n' < n\<close> and assms have "Suc n' < M1.config_time c" by (rule less_trans_Suc)
      then have "\<not> M1.is_final (M1.steps (Suc n') c)" unfolding M1.config_time_def by (rule not_less_Least)
      then show "\<not> M1.is_final (M1.step (cl' (cl (M1.steps n' c))))"
        unfolding cl'_cl funpow.simps comp_def .
    qed
    also have "... = cl (M1.steps (Suc n') c)" by simp
    finally show *: "steps (Suc n') (cl c) = cl (M1.steps (Suc n') c)" .
  qed
qed

lemma comp_step2: "step (map_conf_state Inr c) = map_conf_state Inr (M2.step c)"
  (is "step (?cr c) = ?cr (M2.step c)")
proof (cases "M2.is_final c")
  assume nf: "\<not> M2.is_final c"
  then have "\<not> is_final (?cr c)" by force

  then have "step (?cr c) = step_not_final (?cr c)" by blast
  also have "... = ?cr (M2.step_not_final c)"
  proof (rule TM_config_eq)
    show "state (step_not_final (?cr c)) = state (?cr (M2.step_not_final c))" by simp
    show "tapes (step_not_final (?cr c)) = tapes (?cr (M2.step_not_final c))" by (simp add: M_fields(8-9))
  qed
  also from nf have "... = ?cr (M2.step c)" by simp
  finally show ?thesis .
qed \<comment> \<open>case \<^term>\<open>M2.is_final c\<close> by\<close> simp

lemma comp_steps2: "steps n2 (map_conf_state Inr c_init2) = map_conf_state Inr (M2.steps n2 c_init2)"
  using le0
proof (induction n2 rule: dec_induct)
  case (step n2)
  show ?case unfolding funpow.simps comp_def unfolding step.IH comp_step2 ..
qed simp

lemma comp_steps_final:
  fixes c_init1 n1 n2
  defines "c_fin1 \<equiv> M1.steps n1 c_init1"
  defines "c_init2 \<equiv> conf M2.q\<^sub>0 (tapes c_fin1)"
  defines "c_fin2 \<equiv> M2.steps n2 c_init2"
  assumes ci1_nf: "\<not> M1.is_final c_init1"
    and cf1: "M1.is_final c_fin1"
    and cf2: "M2.is_final c_fin2"
  shows "steps (n1+n2) (map_conf_state Inl c_init1) = map_conf_state Inr c_fin2"
    (is "steps ?n ?c0 = ?c_fin")
proof -
  let ?cl = "map_conf_state Inl" and ?cr = "map_conf_state Inr"
  let ?fs1 = "\<lambda>n. M1.is_final (M1.steps n c_init1)"

  from ci1_nf cf1 have "\<exists>n1'<n1. (\<forall>i\<le>n1'. \<not> ?fs1 i) \<and> ?fs1 (Suc n1')"
    unfolding c_fin1_def by (intro ex_least_nat_less) auto
  then obtain n1' where "n1' < n1" and nfs1: "\<And>i. i \<le> n1' \<Longrightarrow> \<not>?fs1 i" and "?fs1 (Suc n1')" by blast
  then have "\<not>?fs1 n1'" by blast

  (* TODO use comp_steps1 here instead*)
  have "0 \<le> n1'" by (rule le0)
  then have steps_n1': "steps n1' ?c0 = cl (M1.steps n1' c_init1)"
    and isl_n1': "isl (state (steps n1' ?c0))"
  proof (induction n1' rule: dec_induct)
    case base
    show "steps 0 ?c0 = cl (M1.steps 0 c_init1)" and "isl (state (steps 0 ?c0))"
      unfolding funpow_0 cl_def[symmetric] by auto
  next
    case (step n)
    have "steps (Suc n) ?c0 = step (steps n ?c0)" unfolding funpow.simps comp_def ..
    also have "... = step (cl (M1.steps n c_init1))" unfolding step.IH ..
    also have "... = cl (M1.step (cl' (cl (M1.steps n c_init1))))"
    proof (rule comp_step1_not_final)
      show "isl (state (cl (M1.steps n c_init1)))" by simp
      from \<open>n < n1'\<close> have "\<not>?fs1 (Suc n)" by (intro nfs1 Suc_leI)
      then show "\<not> M1.is_final (M1.step (cl' (cl (M1.steps n c_init1))))"
        unfolding cl'_cl funpow.simps comp_def .
    qed
    also have "... = cl (M1.steps (Suc n) c_init1)" by simp
    finally show *: "steps (Suc n) ?c0 = cl (M1.steps (Suc n) c_init1)" .

    show "isl (state (steps (Suc n) ?c0))" unfolding * by simp
  qed

  from \<open>?fs1 (Suc n1')\<close> and \<open>n1' < n1\<close> have c_fin1_alt: "c_fin1 = M1.steps (Suc n1') c_init1"
    unfolding c_fin1_def by (intro M1.final_le_steps Suc_leI)

  from isl_n1' have "steps (Suc n1') ?c0 = conf (Inr M2.q\<^sub>0) (tapes (M1.step (cl' (cl (M1.steps n1' c_init1)))))"
    using \<open>\<not>?fs1 n1'\<close> and \<open>?fs1 (Suc n1')\<close> unfolding funpow.simps comp_def steps_n1'
    by (intro comp_step1_next_final; (unfold cl'_cl)?) blast+ (* TODO Isar-ify this proof *)

  also have "... = conf (Inr M2.q\<^sub>0) (tapes c_fin1)" unfolding c_fin1_alt cl'_cl funpow.simps comp_def ..
  also have "... = ?cr c_init2" unfolding c_init2_def by simp
  finally have steps_Sn1': "steps (Suc n1') ?c0 = ?cr c_init2" .

  from cf2 have "is_final (steps (n2 + Suc n1') ?c0)"
    unfolding funpow_add comp_def steps_Sn1' comp_steps2 c_fin2_def by simp
  moreover from \<open>n1' < n1\<close> have "n2 + Suc n1' \<le> ?n" by auto
  ultimately have "steps ?n ?c0 = steps (n2 + Suc n1') ?c0" by (rule final_le_steps)

  also have "... = steps n2 (?cr c_init2)" unfolding funpow_add comp_def steps_Sn1' ..
  also have "... = ?c_fin" unfolding c_fin2_def comp_steps2 ..
  finally show ?thesis .
qed


lemma comp_run:
  fixes w n1 n2
  defines "c_fin1 \<equiv> M1.run n1 w"
  defines "c_init2 \<equiv> conf M2.q\<^sub>0 (tapes c_fin1)"
  defines "c_fin2 \<equiv> M2.steps n2 c_init2"
  assumes cf1: "M1.is_final c_fin1"
    and cf2: "M2.is_final c_fin2"
  shows "run (n1+n2) w = map_conf_state Inr c_fin2"
    (is "run ?n w = ?cr c_fin2")
proof (cases "M1.q\<^sub>0 \<in> M1.F")
  assume q0f: "M1.q\<^sub>0 \<in> M1.F"
  then have "initial_config w = ?cr (M2.initial_config w)" unfolding TM.initial_config_def by simp
  then have "run ?n w = steps ?n (?cr (M2.initial_config w))" unfolding run_def by presburger
  also have "... = ?cr (M2.steps ?n (M2.initial_config w))" unfolding comp_steps2 ..
  also have "... = ?cr (M2.steps ?n c_init2)"
  proof -
    from q0f have [simp]: "c_fin1 = M1.initial_config w" unfolding c_fin1_def M1.run_def by simp
    have "M2.initial_config w = c_init2" unfolding c_init2_def by (simp add: TM.initial_config_def)
    then show ?thesis by (rule arg_cong)
  qed
  also from cf2 have "... = ?cr c_fin2" unfolding c_fin2_def
    by (intro arg_cong[where f="?cr"], elim M2.final_le_steps) simp
  finally show ?thesis .
next
  assume "M1.q\<^sub>0 \<notin> M1.F"
  then have *: "run n w = steps n (cl (M1.initial_config w))" for n w
    unfolding cl_def run_def by (simp add: TM.initial_config_def)
  from \<open>M1.q\<^sub>0 \<notin> M1.F\<close> have "\<not> M1.is_final (M1.initial_config w)" by simp
  with cf1 cf2 show ?thesis unfolding assms * cl_def M1.run_def by (intro comp_steps_final)
qed

end


definition TM_comp :: "('q1, 's::finite) TM \<Rightarrow> ('q2, 's) TM \<Rightarrow> ('q1 + 'q2, 's) TM"
  where "TM_comp M1 M2 \<equiv> simple_TM_comp.M M1 M2"

theorem TM_comp_steps_final:
  fixes M1 :: "('q1, 's::finite) TM" and M2 :: "('q2, 's) TM"
    and c_init1 :: "('q1, 's) TM_config"
    and n1 n2 :: nat
  assumes k: "TM.tape_count M1 = TM.tape_count M2"
  defines "c_fin1 \<equiv> TM.steps M1 n1 c_init1"
  assumes c_init2_def: "c_init2 \<equiv> TM_config (TM.q\<^sub>0 M2) (tapes c_fin1)" \<comment> \<open>Assumed, not defined, to reduce the term size of the overall lemma.\<close>
  defines "c_fin2 \<equiv> TM.steps M2 n2 c_init2"
  assumes ci1_nf: "\<not> TM.is_final M1 c_init1"
    and cf1: "TM.is_final M1 c_fin1"
    and cf2: "TM.is_final M2 c_fin2"
  shows "TM.steps (TM_comp M1 M2) (n1+n2) (map_TM_config Inl (\<lambda>x. x) c_init1) = map_TM_config Inr (\<lambda>x. x) c_fin2"
    (is "TM.steps ?M ?n ?c0 = ?c_fin")
  using k ci1_nf cf1 cf2
  unfolding c_fin1_def c_init2_def c_fin2_def TM_comp_def simple_TM_comp_def[symmetric]
  by (rule simple_TM_comp.comp_steps_final)


(* here be dragons *)

subsubsection\<open>Composition of Arbitrary TMs\<close>

text\<open>This is designed to allow composition of TMs that we do not know anything about.
  As it is common practise in complexity theoretic proofs to obtain TMs from existence
  (``from \<open>L \<in> DTIME(T)\<close> we obtain \<open>M\<close> where ...'').\<close>


locale arb_TM_comp =
  fixes M1 :: "('q1, 's1::finite) TM"
    and M2 :: "('q2, 's2::finite) TM"
    and f1 :: "('s1 \<Rightarrow> 's::finite)"
    and f2 :: "('s2 \<Rightarrow> 's)"
  assumes inj_f1: "inj f1"
    and inj_f2: "inj f2"
begin
sublocale M1: TM_map_alphabet M1 f1 using inj_f1 by (unfold_locales)
sublocale M2: TM_map_alphabet M2 f2 using inj_f2 by (unfold_locales)

abbreviation "M1' \<equiv> M1.M'"
abbreviation "M2' \<equiv> M2.M'"
sublocale M1': TM_tape_offset M1' 0 "M2.k - 1" .
sublocale M2': TM_tape_offset M2' "M1.k - 1" 0 .

sublocale simple_TM_comp M1'.M' M2'.M'
proof unfold_locales
  show "M1'.M'.k = M2'.M'.k" unfolding M1'.M'_fields(1) M2'.M'_fields(1)
    using M1.at_least_one_tape M2.at_least_one_tape by simp
qed

end \<comment> \<open>\<^locale>\<open>arb_TM_comp\<close>\<close>

end
