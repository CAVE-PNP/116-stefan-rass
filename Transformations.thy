subsection\<open>TM Transformations\<close>

theory Transformations
  imports TM Complexity SpaceComplexity
begin

subsubsection\<open>Reordering Tapes\<close>

(* TODO document this section *)

(* TODO consider renaming \<open>is\<close>. it stands for indices, but is a somewhat bad name since it is also an Isabelle keyword *)
(* TODO consider extracting the function and general lemmas *)
definition reorder :: "(nat option list) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "reorder is xs ys = map2 (\<lambda>i x. case is ! i of None \<Rightarrow> x | Some j \<Rightarrow> nth_default x ys j) [0..<length xs] xs"

value "reorder [Some 0, Some 2, Some 1, None] [w,x,y,z] [a,b,c]"

lemma reorder_length[simp]: "length (reorder is xs ys) = length xs" unfolding reorder_def by simp

lemma reorder_Nil[simp]: "reorder is xs [] = xs"
  unfolding reorder_def nth_default_Nil case_option_same prod.snd_def[symmetric] by simp

lemma reorder_nth[simp]:
  assumes "i < length xs"
  shows "reorder is xs ys ! i = (case is ! i of None \<Rightarrow> xs ! i | Some j \<Rightarrow> nth_default (xs ! i) ys j)"
  using assms unfolding reorder_def by (subst nth_map2) auto

lemma reorder_in_set:
  assumes [simp]: "i < length xs"
  obtains "reorder is xs ys ! i \<in> set xs" | "reorder is xs ys ! i \<in> set ys"
proof -
  have "reorder is xs ys ! i \<in> set xs \<union> set ys"
  proof (induction "is ! i")
    case None
    then show ?case by simp
  next
    case (Some j)
    note [simp] = \<open>Some j = is ! i\<close>[symmetric]

    have "nth_default (xs ! i) ys j \<in> set xs \<union> set ys" by (simp split: nth_default_split)
    then show ?case by simp
  qed
  with that show ?thesis by blast
qed

lemma reorder_in_set':
  assumes "x \<in> set (reorder is xs ys)"
  obtains "x \<in> set xs" | "x \<in> set ys"
proof -
  from assms obtain i where l: "i < length xs" and x: "reorder is xs ys ! i = x"
    unfolding in_set_conv_nth reorder_length by blast
  show ?thesis
  proof (rule reorder_in_set)
    from l show "i < length xs" .
    show  "reorder is xs ys ! i \<in> set xs \<Longrightarrow> thesis"
      and "reorder is xs ys ! i \<in> set ys \<Longrightarrow> thesis" unfolding x by (fact that)+
  qed
qed

lemma reorder_map[simp]: "map f (reorder is xs ys) = reorder is (map f xs) (map f ys)"
proof -
  let ?m = "\<lambda>d i x. case is ! i of None \<Rightarrow> d x | Some j \<Rightarrow> nth_default (d x) (map f ys) j"
  let ?m' = "\<lambda>d (i, x). ?m d i x" and ?id = "\<lambda>x. x"
  have "map f (reorder is xs ys) =
    map (\<lambda>(i, x). f (case is ! i of None \<Rightarrow> x | Some j \<Rightarrow> nth_default x ys j)) (zip [0..<length xs] xs)"
    unfolding reorder_def map_map comp_def by force
  also have "... = map2 (?m f) [0..<length xs] xs" unfolding option.case_distrib nth_default_map ..
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
    [0..<if set is \<subseteq> {None} then 0 else Suc (Max (someset is))]"


lemma set_reorder_inv:
  assumes ls: "length ys = length is"
    and items_match: "someset is = {0..<N}"
  shows "set (reorder_inv is ys) \<subseteq> set ys" (is "set ?r \<subseteq> set ys")
proof cases
  assume "set is \<subseteq> {None}"
  then have "set (reorder_inv is ys) = {}" unfolding reorder_inv_def by simp
  also have "... \<subseteq> set ys" ..
  finally show ?thesis .
next
  assume "\<not> set is \<subseteq> {None}"
  then have "N > 0" unfolding these_empty_eq_subset[symmetric] items_match by simp

  show "set (reorder_inv is ys) \<subseteq> set ys"
  proof (rule subsetI)
    define n where "n \<equiv> if set is \<subseteq> {None} then 0 else Suc (Max (someset is))"
    with \<open>\<not> set is \<subseteq> {None}\<close> have n_simp: "n = Suc (Max (Option.these (set is)))" by simp

    define f where "f \<equiv> \<lambda>i. ys ! (LEAST i'. i' < length is \<and> is ! i' = Some i)"
    have lr: "length (map f [0..<n]) = n" by simp

    fix x
    assume "x \<in> set ?r"
    then have "x \<in> set (map f [0..<n])" unfolding reorder_inv_def by (fold n_def f_def)
    then obtain i where "i < n" and "map f [0..<n] ! i = x" unfolding in_set_conv_nth lr by blast
    then have "x = f i" by simp
    show "x \<in> set ys" unfolding \<open>x = f i\<close> f_def
    proof (intro nth_mem)
      from \<open>i < n\<close> have "i \<le> Max (Option.these (set is))" unfolding n_simp by simp
      then have "i \<in> someset is" unfolding items_match
        using \<open>N > 0\<close> by (subst (asm) Max_ge_iff) force+
      then have "\<exists>i'. i' < length is \<and> is ! i' = Some i" unfolding in_set_conv_nth in_these_eq .
      then show "(LEAST i'. i' < length is \<and> is ! i' = Some i) < length ys"
        unfolding ls by (blast dest!: LeastI_ex)
    qed
  qed
qed


lemma reorder_inv:
  assumes [simp]: "length xs = length is"
    and items_match: "someset is = {0..<length ys}"
  shows "reorder_inv is (reorder is xs ys) = ys"
proof -
  define zs where "zs \<equiv> reorder is xs ys"
  have lz: "length zs = length xs" unfolding zs_def reorder_length ..

  have *: "(if set is \<subseteq> {None} then 0 else Suc (Max (someset is))) = length ys"
  proof (rule ifI)
    assume "set is \<subseteq> {None}"
    then have "Option.these (set is) = {}" unfolding these_empty_eq subset_singleton_iff .
    then have "{0..<length ys} = {}" unfolding items_match .
    then show "0 = length ys" by simp
  next
    assume "\<not> set is \<subseteq> {None}"
    then have "Option.these (set is) \<noteq> {}" unfolding these_empty_eq subset_singleton_iff .
    then have "0 < length ys" unfolding items_match by simp
    then show "Suc (Max (someset is)) = length ys"
      unfolding items_match Max_atLeastLessThan_nat[OF \<open>length ys > 0\<close>] by simp
  qed

  have "length ys = card (someset is)" unfolding items_match by simp
  also have "... \<le> length is" by (rule card_these_length)
  finally have ls: "length is \<ge> length ys" .

  have "reorder_inv is (reorder is xs ys) = map ((!) ys) [0..<length ys]"
    unfolding reorder_inv_def zs_def[symmetric] lz *
  proof (intro list.map_cong0)
    fix n assume "n \<in> set [0..<length ys]"
    then have [simp]: "n < length ys" by simp
    then have *: "[0..<length ys] ! n = n" by simp

    define i where "i = (LEAST i. i < length is \<and> is ! i = Some n)"

    from \<open>n < length ys\<close> have "n \<in> someset is" unfolding items_match by simp
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

lemma reorder_config_length[simp]: "length (tapes (reorder_config is tps c)) = length tps"
  unfolding reorder_config_def by simp

lemma reorder_config_simps[simp]:
  shows reorder_config_state: "state (reorder_config is tps c) = state c"
    and reorder_config_tapes: "tapes (reorder_config is tps c) = reorder is tps (tapes c)"
  unfolding reorder_config_def by simp_all


locale TM_reorder_tapes = TM M for M :: "('q, 's, 'l) TM" +
  fixes "is" :: "nat option list"
  assumes items_match: "someset is = {0..<k}"
begin

abbreviation "k' \<equiv> length is"

abbreviation "r \<equiv> reorder is"
abbreviation "rc \<equiv> reorder_config is"
abbreviation r_inv ("r\<inverse>") where "r_inv \<equiv> reorder_inv is"

lemma is_not_only_None: "\<not> (set is \<subseteq> {None})"
proof
  assume "set is \<subseteq> {None}"
  then have "Option.these (set is) = {}" unfolding these_empty_eq by (fact subset_singletonD)
  with items_match show False by simp
qed
lemma is_not_empty: "is \<noteq> []" using items_match these_not_empty_eq by fastforce

lemma h1[simp]: "Suc (Max (someset is)) = k"
  unfolding items_match by (simp add: Max_atLeastLessThan_nat)

lemma r_inv_len[simp]: "length (reorder_inv is ys) = k"
  unfolding reorder_inv_def using is_not_only_None by simp

lemma r_inv_set:
  assumes "length ys = k'"
  shows "set (reorder_inv is ys) \<subseteq> set ys"
  using assms items_match by (fact set_reorder_inv)

lemma k_k': "k \<le> k'"
proof -
  have "k = card (someset is)" unfolding items_match by simp
  also have "... \<le> card (set is)" by (rule card_these) blast
  also have "... \<le> k'" by (rule card_length)
  finally show "k \<le> k'" .
qed

definition reorder_tapes_rec :: "('q, 's, 'l) TM_record"
  where "reorder_tapes_rec \<equiv> M_rec \<lparr>
      tape_count := k',
      next_state := \<lambda>q hds. \<delta>\<^sub>q q (r\<inverse> hds),
      next_write := \<lambda>q hds i. case nth_default None is i of Some i \<Rightarrow> (\<delta>\<^sub>w q (r\<inverse> hds) i) | None \<Rightarrow> nth_default None hds i,
      next_move  := \<lambda>q hds i. case nth_default None is i of Some i \<Rightarrow> (\<delta>\<^sub>m q (r\<inverse> hds) i) | None \<Rightarrow> No_Shift
    \<rparr>"

lemma reorder_tapes_rec_simps: "reorder_tapes_rec = \<lparr>
  TM_record.tape_count = k', symbols = \<Sigma>,
  states = Q, initial_state = q\<^sub>0, final_states = F, label = lab,
  next_state = \<lambda>q hds. \<delta>\<^sub>q q (r\<inverse> hds),
  next_write = \<lambda>q hds i. case nth_default None is i of Some i \<Rightarrow> (\<delta>\<^sub>w q (r\<inverse> hds) i) | None \<Rightarrow> nth_default None hds i,
  next_move  = \<lambda>q hds i. case nth_default None is i of Some i \<Rightarrow> (\<delta>\<^sub>m q (r\<inverse> hds) i) | None \<Rightarrow> No_Shift
\<rparr>" unfolding reorder_tapes_rec_def M_rec by simp

definition "M' \<equiv> Abs_TM reorder_tapes_rec"

lemma M'_valid: "valid_TM reorder_tapes_rec" unfolding reorder_tapes_rec_simps
proof (rule valid_TM_I)
  from at_least_one_tape and k_k' show "k' > 0" by linarith

  fix q hds assume "q \<in> Q" and "length hds = k'" and "set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p"
  from \<open>length hds = k'\<close> have "set (r\<inverse> hds) \<subseteq> set hds" by (fact r_inv_set)
  also note \<open>set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p\<close>
  finally have "set (r\<inverse> hds) \<subseteq> \<Sigma>\<^sub>t\<^sub>p" .
  with \<open>q \<in> Q\<close> show "\<delta>\<^sub>q q (r\<inverse> hds) \<in> Q" by simp

  fix i
  assume "i < k'"
  show "(case nth_default None is i of Some x \<Rightarrow> \<delta>\<^sub>w q (r\<inverse> hds) x | None \<Rightarrow> nth_default None hds i) \<in> \<Sigma>\<^sub>t\<^sub>p"
  proof (rule case_option_cases)
    show "nth_default None hds i \<in> \<Sigma>\<^sub>t\<^sub>p" by (rule nth_default_cases) (use \<open>set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p\<close> in auto)

    fix y
    assume "nth_default None is i = Some y"

    with \<open>i < k'\<close> have "is ! i = Some y" by simp
    from \<open>i < k'\<close> have "Some y \<in> set is" by (fold \<open>is ! i = Some y\<close>) (fact nth_mem)
    with items_match have "y < k" unfolding in_these_eq[symmetric] by simp
    then show "\<delta>\<^sub>w q (r\<inverse> hds) y \<in> \<Sigma>\<^sub>t\<^sub>p" using \<open>set (r\<inverse> hds) \<subseteq> \<Sigma>\<^sub>t\<^sub>p\<close> and \<open>q \<in> Q\<close> by simp
  qed
qed (fact TM_axioms)+

sublocale M': TM M' .

lemma M'_rec: "M'.M_rec = reorder_tapes_rec" using Abs_TM_inverse M'_valid by (auto simp add: M'_def)
lemmas M'_fields = M'.TM_fields_defs[unfolded M'_rec reorder_tapes_rec_simps TM_record.simps]
lemmas [simp] = M'_fields(1-6)

lemma M'_wf_config[intro?]:
  assumes "wf_config c"
    and "length tps' = k'"
    and "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "M'.wf_config (rc tps' c)"
proof (intro M'.wf_configI, unfold M'_fields)
  from \<open>wf_config c\<close> show "state (rc tps' c) \<in> Q" by auto
  from \<open>length tps' = k'\<close> show "length (tapes (rc tps' c)) = k'" by simp
  show "\<forall>tp\<in>set (tapes (rc tps' c)). set_tape tp \<subseteq> \<Sigma>"
    unfolding reorder_config_simps all_set_conv_all_nth reorder_length
  proof (intro allI impI)
    fix n
    assume "n < length tps'"
    then show "set_tape (r tps' (tapes c) ! n) \<subseteq> \<Sigma>"
    proof (rule reorder_in_set)
      assume "r tps' (tapes c) ! n \<in> set tps'"
      with \<open>\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>\<close> show "set_tape (r tps' (tapes c) ! n) \<subseteq> \<Sigma>"
        unfolding list_all_iff by blast
    next
      assume "r tps' (tapes c) ! n \<in> set (tapes c)"
      with \<open>wf_config c\<close> show "set_tape (r tps' (tapes c) ! n) \<subseteq> \<Sigma>"
        using list_all_iff[iff] by blast
    qed
  qed
qed

lemma reorder_step:
  assumes "wf_config c"
    and l_tps'[simp]: "length tps' = k'"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "M'.step (rc tps' c) = rc tps' (step c)"
    (is "M'.step (?rc c) = ?rc (step c)")
proof (cases "is_final c")
  assume "is_final c"
  then show ?thesis by simp
next
  define c' where "c' \<equiv> ?rc c"

  let ?q  = "state c"  and ?tps  = "tapes c"  and ?hds  = "heads c"
  let ?q' = "state c'" and ?tps' = "tapes c'" and ?hds' = "heads c'"

  have q': "?q' = ?q" unfolding c'_def by simp

  let ?rt = "r tps'" and ?rh = "r (map head tps')"
  have  tps': "?tps' = ?rt ?tps"
    and hds': "?hds' = ?rh ?hds" unfolding c'_def by simp_all

  from l_tps' have l_tps''[simp]: "length ?tps' = k'" unfolding c'_def by simp

  from \<open>wf_config c\<close> have l_tps: "length (tapes c) = k" by blast
  then have l_hds: "length (heads c) = k" by simp
  have l_hds': "length (map head tps') = k'" by simp

  moreover have "someset is = {0..<length ?hds}" unfolding l_hds items_match ..
  ultimately have r_inv_hds[simp]: "reorder_inv is ?hds' = ?hds" unfolding hds' by (rule reorder_inv)

  from \<open>wf_config c\<close> and l_tps' wf_tps' have [simp]: "M'.wf_config c'"
    unfolding c'_def by (fact M'_wf_config)

  assume "\<not> is_final c"
  then have "M'.step c' = M'.step_not_final c'" by (simp add: q')
  also have "... = ?rc (step_not_final c)"
  proof (intro TM_config.expand conjI)
    have "state (M'.step_not_final c') = M'.\<delta>\<^sub>q ?q' ?hds'" by simp
    also from \<open>M'.wf_config c'\<close> have "... = \<delta>\<^sub>q ?q' ?hds" unfolding M'_fields(7) by simp
    also have "... = state (?rc (step_not_final c))" unfolding q' by simp
    finally show "state (M'.step_not_final c') = state (?rc (step_not_final c))" .

    from k_k' have min_k_k': "min k M'.k = k" by simp
    have lr: "length (r tps' x) = M'.k" for x by simp

    have "tapes (M'.step_not_final c') = map2 tape_action (M'.\<delta>\<^sub>a ?q' ?hds') ?tps'" by simp
    also have "... = r tps' (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps)"
    proof (rule M'.step_not_final_eqI)
      fix i assume "i < M'.k"
      then have [simp]: "i < k'" by simp

      show "tape_action (M'.\<delta>\<^sub>w ?q' ?hds' i, M'.\<delta>\<^sub>m ?q' ?hds' i) (?tps' ! i) =
        ?rt (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps) ! i"
      proof (induction "is ! i")
        case None
        then have [simp]: "is ! i = None" ..
        have [simp]: "reorder is xs ys ! i = xs ! i" if "length xs = k'" for xs ys :: "'x list"
          using that by simp
        have [simp]: "?tps' ! i = tps' ! i" unfolding c'_def by simp

        from \<open>i < k'\<close> show ?case unfolding M'_fields using l_tps' by simp
      next
        case (Some i')
        then have [simp]: "is ! i = Some i'" ..

        from \<open>i < k'\<close> have "i \<in> {0..<k'}" by simp
        then have "Some i' \<in> set is" unfolding \<open>Some i' = is ! i\<close> using \<open>i < k'\<close> nth_mem by blast
        then have "i' \<in> {0..<k}" unfolding items_match[symmetric] in_these_eq .
        then have [simp]: "i' < k" by simp

        then have nth_i': "nth_default x xs i' = xs ! i'" if "length xs = k" for x :: 'x and xs using that by simp
        from \<open>i < k'\<close> have "i < length tps'" by simp
        then have r_nth_or: "?rt tps ! i = nth_default (tps' ! i) tps i'" for tps by simp

        have \<delta>\<^sub>w': "M'.\<delta>\<^sub>w ?q' ?hds' i = \<delta>\<^sub>w (state c) (heads c) i'"
         and \<delta>\<^sub>m': "M'.\<delta>\<^sub>m ?q' ?hds' i = \<delta>\<^sub>m (state c) (heads c) i'"
          unfolding M'_fields q'[symmetric] by simp_all

        have "tape_action (M'.\<delta>\<^sub>w ?q' ?hds' i, M'.\<delta>\<^sub>m ?q' ?hds' i) (?tps' ! i) =
              tape_action (   \<delta>\<^sub>w ?q  ?hds i',    \<delta>\<^sub>m ?q  ?hds i') (?tps ! i')"
          unfolding \<delta>\<^sub>w' \<delta>\<^sub>m' unfolding tps' r_nth_or nth_i'[OF l_tps] ..
        also have "... = tape_action (\<delta>\<^sub>a ?q ?hds ! i') (?tps ! i')" by simp
        also have "... = map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps ! i'" by (auto simp add: l_tps)
        also have "... = ?rt (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps) ! i"
          unfolding r_nth_or by (rule nth_i'[symmetric]) (simp add: l_tps)
        finally show ?case .
      qed
    qed ((unfold tps')?, fact lr)+
    also have "... = tapes (?rc (step_not_final c))" by (simp add: Let_def)
    finally show "tapes (M'.step_not_final c') = tapes (?rc (step_not_final c))" .
  qed
  also from \<open>\<not> is_final c\<close> have "... = ?rc (step c)" by simp
  finally show ?thesis unfolding c'_def .
qed

corollary reorder_steps:
  assumes wfc: "wf_config c"
    and l_tps': "length tps' = k'"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "M'.steps n (rc tps' c) = rc tps' (steps n c)"
proof (induction n)
  case (Suc n)
  from \<open>wf_config c\<close> have wfcs: "wf_config (steps n c)" by blast
  show ?case unfolding funpow.simps comp_def Suc.IH unfolding reorder_step[OF wfcs l_tps' wf_tps'] ..
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

corollary reorder_final_iff:
  assumes wfc: "wf_config c"
    and l_tps': "length tps' = k'"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "M'.is_final (M'.steps n (rc tps' c)) = is_final (steps n c)"
  unfolding reorder_steps[OF assms] by simp

corollary reorder_halts:
  assumes wfc: "wf_config c"
    and l_tps': "length tps' = k'"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "M'.halts_config (rc tps' c) \<longleftrightarrow> halts_config c"
  unfolding TM.halts_config_def reorder_final_iff[OF assms] ..

corollary reorder_config_time:
  fixes c :: "('q, 's) TM_config"
  assumes wfc: "wf_config c"
    and l_tps': "length tps' = k'"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "M'.config_time (rc tps' c) = config_time c"
  unfolding TM.config_time_def reorder_final_iff[OF assms] ..

corollary reorder_run':
  assumes wwf: "wf_input w"
    and l_tps': "length tps' = k'"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "M'.steps n (rc tps' (c\<^sub>0 w)) = rc tps' (run n w)"
  unfolding run_def using assms by (blast intro: reorder_steps)

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
        unfolding M'_fields(1) by simp
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
  assumes "wf_input w"
    and tape0_id: "\<forall>i<k'. i = 0 \<longleftrightarrow> is ! i = Some 0" \<comment> \<open>the first tape is only mapped to the first tape\<close>
  shows "M'.run n w = rc (\<langle>\<rangle> \<up> k') (run n w)"
proof -
  let ?rc = "rc (tapes (TM_config q\<^sub>0 (\<langle>\<rangle> \<up> k')))"
  have "M'.run n w = M'.steps n (?rc (initial_config w))"
    unfolding M'.run_def init_conf_eq[OF tape0_id] by simp
  also from \<open>wf_input w\<close> have "... = ?rc (run n w)" by (subst reorder_run') auto
  finally show ?thesis by simp
qed

corollary reorder_time:
  assumes "wf_input w"
    and tape0_id: "\<forall>i<k'. i = 0 \<longleftrightarrow> is ! i = Some 0"
  shows "M'.time w = time w"
  unfolding TM.time_altdef reorder_run[OF assms] by simp

end \<comment> \<open>\<^locale>\<open>TM_reorder_tapes\<close>\<close>


context TM
begin

definition reorder_tapes :: "nat option list \<Rightarrow> ('q, 's, 'l) TM"
  where "reorder_tapes is \<equiv> TM_reorder_tapes.M' M is"

corollary reorder_tapes_steps:
  fixes c :: "('q, 's) TM_config"
  assumes "wf_config c"
    and "length tps' = length is"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
    and "someset is = {0..<k}"
  shows "TM.steps (reorder_tapes is) n (reorder_config is tps' c) = reorder_config is tps' (steps n c)"
  unfolding reorder_tapes_def using assms
  by (intro TM_reorder_tapes.reorder_steps) (unfold_locales)

definition tape_offset :: "nat \<Rightarrow> nat \<Rightarrow> nat option list"
  where "tape_offset a b \<equiv> None\<up>a @ (map Some [0..<k]) @ None\<up>b"

lemma tape_offset_length[simp]: "length (tape_offset a b) = a + k + b"
  unfolding tape_offset_def by simp

lemma tape_offset_nth:
  assumes "i < a + k + b"
  shows "tape_offset a b ! i = (if a \<le> i \<and> i < a + k then Some (i - a) else None)"
  (is "?lhs = ?rhs")
proof (cases "a \<le> i", cases "i < a + k")
  assume "a \<le> i" and "i < a + k"
  then have "i - a < k" by (subst less_diff_conv2) presburger+

  from \<open>a \<le> i\<close> have "?lhs = (map Some [0..<k] @ None \<up> b) ! (i - a)"
    unfolding tape_offset_def by (subst nth_append) force
  also from \<open>i - a < k\<close> have "... = Some (i - a)" by (subst nth_append) simp
  also from \<open>a \<le> i\<close> and \<open>i < a + k\<close> have "... = ?rhs" by argo
  finally show ?thesis .
next
  assume "\<not> i < a + k"
  then have "i \<ge> a + k" by (rule leI)
  then have "i - a \<ge> k" by (subst le_diff_conv2) presburger+

  have "?lhs = ((None \<up> a @ map Some [0..<k]) @ None \<up> b) ! i" unfolding tape_offset_def by simp
  also from \<open>\<not> i < a + k\<close> have "... = (None \<up> b) ! (i - (a + k))" by (subst nth_append) simp
  also from \<open>i < a + k + b\<close> and \<open>a + k \<le> i\<close> have "... = None"
    using less_diff_conv2 by (subst nth_replicate) presburger+
  also from \<open>\<not> i < a + k\<close> have "... = ?rhs" by presburger
  finally show ?thesis .
next
  assume "\<not> a \<le> i"
  then show ?thesis unfolding tape_offset_def by (subst nth_append) simp
qed

lemma tape_offset_simps:
  assumes [simp]: "length xs = a + k + b"
    and [simp]: "length ys = k"
  shows "reorder (tape_offset a b) xs ys = take a xs @ ys @ take b (drop (a + length ys) xs)"
  (is "?lhs = ?rhs")
proof (rule nth_equalityI, unfold reorder_length tape_offset_length)
  from assms show "length xs = length ?rhs" by simp

  fix i assume "i < length xs"
  with assms have "i < a + k + b" by simp

  note * = reorder_nth[OF \<open>i < length xs\<close>] tape_offset_nth[OF \<open>i < a + k + b\<close>]

  show "?lhs ! i = ?rhs ! i"
  proof (cases "a \<le> i", cases "i < a + k")
    assume "a \<le> i" and "i < a + k"
    then have "i - a < k" by (subst less_diff_conv2) presburger+
    from \<open>a \<le> i\<close> have "\<not> i < a" by simp

    from \<open>a \<le> i\<close> and \<open>i < a + k\<close> have "a \<le> i \<and> i < a + k" by blast
    then have "?lhs ! i = nth_default (xs ! i) ys (i - a)" unfolding * by simp
    also from \<open>i - a < k\<close> have "... = ys ! (i - a)" unfolding nth_default_def \<open>length ys = k\<close> by simp
    also from \<open>i - a < k\<close> have "... = (ys @ take b (drop (a + k) xs)) ! (i - a)" by (subst nth_append) simp
    also from \<open>\<not> i < a\<close> have "... = ?rhs ! i" by (subst (2) nth_append) simp
    finally show ?thesis .
  next
    assume "\<not> i < a + k"
    then have "\<not> i - a < k" by force
    from \<open>\<not> i < a + k\<close> have "\<not> i < a" by linarith

    from \<open>\<not> i < a + k\<close> have "?lhs ! i = xs ! i" unfolding * by simp
    also from \<open>\<not> i < a + k\<close> have "... = (drop (a + k) xs) ! (i - a - length ys)" by (subst nth_drop) auto
    also have "... = (take b (drop (a + k) xs)) ! (i - a - length ys)" by simp
    also from \<open>\<not> i - a < k\<close> have "... = (ys @ take b (drop (a + k) xs)) ! (i - a)"
      by (subst nth_append, subst if_not_P) force+
    also from \<open>\<not> i < a\<close> have "... = ?rhs ! i" by (subst (2) nth_append, subst if_not_P) auto
    finally show ?thesis .
  next
    assume "\<not> a \<le> i"
    then show ?thesis unfolding * by (subst nth_append) simp
  qed
qed


lemma tape_offset_simps1:
  assumes "length xs = k + b"
    and "length ys = k"
  shows "reorder (tape_offset 0 b) xs ys = ys @ take b (drop (length ys) xs)"
  using assms by (subst tape_offset_simps) auto

lemma tape_offset_simps2:
  assumes "length xs = k + a"
    and "length ys = k"
  shows "reorder (tape_offset a 0) xs ys = take a xs @ ys"
  using assms by (subst tape_offset_simps) auto


lemma tape_offset_valid: "someset (tape_offset a b) = {0..<k}"
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
    and "length tps' = length is"
    and wf_tps': "\<forall>tp\<in>set tps'. set_tape tp \<subseteq> \<Sigma>"
  shows "TM.steps (reorder_tapes is) n (reorder_config is tps' c) = reorder_config is tps' (steps n c)"
  using assms tape_offset_valid unfolding reorder_tapes_def is_def
  by (intro TM_reorder_tapes.reorder_steps) (unfold_locales)

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


locale TM_tape_offset = TM M for M :: "('q, 's, 'l) TM" +
  fixes a b :: nat
begin

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
    moreover from \<open>\<not> i < k\<close> and at_least_one_tape have "i \<noteq> 0" by meson
    ultimately show ?thesis by blast
  qed
qed

corollary init_conf_offset_eq: "a = 0 \<Longrightarrow> M'.c\<^sub>0 w = rc (\<langle>\<rangle> \<up> length is) (c\<^sub>0 w)"
  by (intro init_conf_eq tape_offset_helper)

corollary offset_time: "a = 0 \<Longrightarrow> wf_input w \<Longrightarrow> M'.time w = time w"
  by (intro reorder_time tape_offset_helper)

end \<comment> \<open>\<^locale>\<open>TM_tape_offset\<close>\<close>


subsubsection\<open>Change Alphabet\<close>

locale TM_map_alphabet = TM M for M :: "('q, 's1, 'l) TM" +
  fixes f :: "'s1 \<Rightarrow> 's2"
    and \<Sigma>' :: "'s2 set" \<comment> \<open>this is not necessarily \<^term>\<open>f ` \<Sigma>\<close>.\<close>
  assumes inj_f: "inj_on f \<Sigma>"
    and range_f: "f ` \<Sigma> \<subseteq> \<Sigma>'"
    and finite_symbols: "finite \<Sigma>'"
begin

abbreviation f' where "f' \<equiv> map_option f"
definition f_inv ("f\<inverse>") where "f_inv \<equiv> inv_into \<Sigma> f"
abbreviation f'_inv ("f''\<inverse>") where "f'_inv \<equiv> map_option f_inv"

lemma inv_f_f[simp]: "x \<in> \<Sigma> \<Longrightarrow> f_inv (f x) = x"
  unfolding f_inv_def using inj_f by (rule inv_into_f_f)
lemma inv_f'_f'[simp]: "x \<in> \<Sigma>\<^sub>t\<^sub>p \<Longrightarrow> f'_inv (f' x) = x" by (induction x) auto

lemma map_f_inv[simp]: "xs \<in> \<Sigma>* \<Longrightarrow> map f_inv (map f xs) = xs"
  unfolding f_inv_def lists_member using inj_f by (rule map_inv_into_map_id)
lemma map_f'_inv[simp]: "xs \<in> \<Sigma>\<^sub>t\<^sub>p* \<Longrightarrow> map f'_inv (map f' xs) = xs"
  unfolding map_map comp_def using inv_f'_f' by (blast intro: map_idI)


definition fc where "fc \<equiv> map_conf_tapes f"

lemma fc_simps[simp]:
  shows "state (fc c) = state c"
    and "tapes (fc c) = map (map_tape f) (tapes c)"
  unfolding fc_def TM_config.map_sel by (rule refl)+

definition map_alph_rec :: "('q, 's2, 'l) TM_record"
  where "map_alph_rec \<equiv> \<lparr>
    TM_record.tape_count = k, symbols = \<Sigma>',
    states = Q, initial_state = q\<^sub>0, final_states = F, label = lab,
    next_state = \<lambda>q hds. if set hds \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p then \<delta>\<^sub>q q (map f'_inv hds) else q,
    next_write = \<lambda>q hds i. if set hds \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p then f' (\<delta>\<^sub>w q (map f'_inv hds) i) else hds ! i,
    next_move  = \<lambda>q hds i. if set hds \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p then \<delta>\<^sub>m q (map f'_inv hds) i else No_Shift
  \<rparr>"

lemma valid_tape_symbol_helper[intro]: "x \<in> \<Sigma>\<^sub>t\<^sub>p \<Longrightarrow> f' x \<in> options \<Sigma>'"
  unfolding set_options_eq using range_f by blast

lemma M'_valid: "valid_TM map_alph_rec" unfolding map_alph_rec_def
proof (rule valid_TM_I)
  from finite_symbols show "finite \<Sigma>'" .
  from range_f show "\<Sigma>' \<noteq> {}" using symbol_axioms(2) by blast

  fix q hds i
  let ?\<Sigma>\<^sub>t\<^sub>p' = "options \<Sigma>'" and ?hds' = "map f'\<inverse> hds"
  assume "q \<in> Q" and "length hds = k" and "set hds \<subseteq> ?\<Sigma>\<^sub>t\<^sub>p'"
  then have *[dest]: "wf_hds ?hds'" if "set hds \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p"
  proof (intro conjI)
    from \<open>set hds \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p\<close> have "set ?hds' \<subseteq> f'_inv ` f' ` \<Sigma>\<^sub>t\<^sub>p" ..
    also have "... \<subseteq> \<Sigma>\<^sub>t\<^sub>p" by force
    finally show "set ?hds' \<subseteq> \<Sigma>\<^sub>t\<^sub>p" .
  qed simp

  from \<open>q \<in> Q\<close> and \<open>length hds = k\<close> and \<open>set hds \<subseteq> ?\<Sigma>\<^sub>t\<^sub>p'\<close>
  show "(if set hds \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p then \<delta>\<^sub>q q (map f'\<inverse> hds) else q) \<in> Q" by (cases rule: ifI) blast

  assume "i < k"
  with \<open>length hds = k\<close> and \<open>set hds \<subseteq> ?\<Sigma>\<^sub>t\<^sub>p'\<close> have "hds ! i \<in> ?\<Sigma>\<^sub>t\<^sub>p'" by force
  with * show "(if set hds \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p then f' (\<delta>\<^sub>w q ?hds' i) else hds ! i) \<in> ?\<Sigma>\<^sub>t\<^sub>p'"
    using \<open>q \<in> Q\<close> and \<open>i < k\<close> by (cases rule: ifI) blast+
qed (fact TM_axioms)+

definition "M' \<equiv> Abs_TM map_alph_rec"
sublocale M': TM M' .

lemma M'_rec: "M'.M_rec = map_alph_rec" using Abs_TM_inverse M'_valid by (auto simp add: M'_def)
lemmas M'_fields = M'.TM_fields_defs[unfolded M'_rec map_alph_rec_def TM_record.simps]
lemmas [simp] = M'_fields(1-6)

lemma M'_tape_symbols: "f' ` \<Sigma>\<^sub>t\<^sub>p \<subseteq> M'.\<Sigma>\<^sub>t\<^sub>p" by force

lemma map_wf_config[intro,dest]: "wf_config c \<Longrightarrow> M'.wf_config (fc c)"
proof (elim wf_config_transferI)
  from range_f have "set_tape tp \<subseteq> \<Sigma> \<Longrightarrow> set_tape (map_tape f tp) \<subseteq> \<Sigma>'" for tp
    unfolding tape.set_map by blast
  then show "\<forall>tp\<in>set (tapes c). set_tape tp \<subseteq> \<Sigma> \<Longrightarrow> \<forall>tp\<in>set (tapes (fc c)). set_tape tp \<subseteq> M'.\<Sigma>"
    by simp
qed simp_all

lemma map_step:
  assumes [intro]: "wf_config c"
  defines "c' \<equiv> fc c"
  shows "M'.step c' = fc (step c)"
proof (cases "is_final c") (* TODO extract this pattern as lemma *)
  let ?q  = "state c"  and ?tps  = "tapes c"  and ?hds  = "heads c"
  let ?q' = "state c'" and ?tps' = "tapes c'" and ?hds' = "heads c'"

  let ?ft = "map (map_tape f)"
  have  tps': "?tps' = ?ft ?tps"
    and hds': "?hds' = map f' ?hds" unfolding c'_def by simp_all

  from \<open>wf_config c\<close> have [simp]: "length ?tps = k" ..
  from \<open>wf_config c\<close> have [simp]: "M'.wf_config c'" unfolding c'_def ..

  have c'_simps[simp]: "?q' = ?q" "length ?tps' = k" unfolding c'_def by simp_all

  assume "\<not> is_final c"
  then have "M'.step c' = M'.step_not_final c'" by simp
  also have "... = fc (step_not_final c)"
  proof (rule TM_config_eq)
    from \<open>wf_config c\<close> have "set ?hds' \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p" unfolding hds' by (intro map_image) blast
    then have \<delta>_If: "\<And>x y. (if set ?hds' \<subseteq> f' ` \<Sigma>\<^sub>t\<^sub>p then x else y) = x" by (fact if_P)
    from \<open>wf_config c\<close> have f_inv_f[simp]: "map f'\<inverse> ?hds' = ?hds"
      unfolding hds' by (blast intro: map_f'_inv)
    note * = M'_fields(7-9) \<delta>_If f_inv_f

    have "state (M'.step_not_final c') = M'.\<delta>\<^sub>q ?q' ?hds'" by simp
    also have "... = \<delta>\<^sub>q ?q' ?hds" unfolding M'_fields(7-9) by (simp only: *)
    also have "... = state (fc (step_not_final c))" by simp
    finally show "state (M'.step_not_final c') = state (fc (step_not_final c))" .

    show "tapes (M'.step_not_final c') = tapes (fc (step_not_final c))"
      unfolding TM.step_not_final_simps
    proof (intro TM.step_not_final_eqI, unfold fc_simps map_head_tapes)
      fix i assume "i < M'.k"
      then have [simp]: "i < k" by simp

      have "tape_action (M'.\<delta>\<^sub>w ?q' ?hds' i, M'.\<delta>\<^sub>m ?q' ?hds' i) (?tps' ! i)
          = tape_action (f' (\<delta>\<^sub>w ?q' ?hds i), \<delta>\<^sub>m ?q' ?hds i) (?tps' ! i)" by (simp only: * \<open>i < k\<close>)
      also have "... = tape_action (f' (\<delta>\<^sub>w ?q ?hds i), \<delta>\<^sub>m ?q ?hds i) (map_tape f (?tps ! i))" by (simp add: c'_def)
      also have "... = map_tape f (tape_action (\<delta>\<^sub>w ?q ?hds i, \<delta>\<^sub>m ?q ?hds i) (?tps ! i))" by simp
      also have "... = ?ft (tapes (step_not_final c)) ! i" by simp
      finally show "tape_action (M'.\<delta>\<^sub>w ?q' ?hds' i, M'.\<delta>\<^sub>m ?q' ?hds' i) (?tps' ! i) =
         ?ft (tapes (step_not_final c)) ! i" .
    qed simp_all
  qed
  also from \<open>\<not> is_final c\<close> have "... = fc (step c)" by simp
  finally show ?thesis .
qed \<comment> \<open>case \<open>is_final c\<close> by\<close> (simp add: c'_def)

corollary map_steps[simp]:
  assumes "wf_config c"
  shows "M'.steps n (fc c) = fc (steps n c)"
proof (induction n)
  case (Suc n)
  from \<open>wf_config c\<close> have wf: "wf_config (steps n c)" by (fact wf_steps)
  show ?case unfolding funpow.simps comp_def Suc.IH map_step[OF wf] ..
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

corollary map_config_time[simp]: "wf_config c \<Longrightarrow> M'.config_time (fc c) = config_time c"
  unfolding TM.config_time_def by simp

lemma map_init_conf[simp]: "M'.c\<^sub>0 (map f w) = fc (c\<^sub>0 w)"
  unfolding TM.initial_config_def by (rule TM_config_eq) auto

corollary map_run[simp]: "wf_input w \<Longrightarrow> M'.run n (map f w) = fc (run n w)" by simp
corollary map_time[simp]: "wf_input w \<Longrightarrow> M'.time (map f w) = time w" by simp
corollary map_compute[simp]: "wf_input w \<Longrightarrow> M'.compute (map f w) = fc (compute w)" by simp
corollary map_halts_conf: "wf_config c \<Longrightarrow> M'.halts_config (fc c) = halts_config c" by simp
corollary map_halts[iff]: "wf_input w \<Longrightarrow> M'.halts (map f w) \<longleftrightarrow> halts w" by (simp add: TM.halts_def)

lemma map_computes_word:
  assumes wf: "wf_input w" and wf': \<open>wf_input w'\<close>
  shows "M'.computes_word (map f w) (map f w') \<longleftrightarrow> computes_word w w'"
  \<comment> \<open>Note that the equivalence does not extend to \<^const>\<open>TM.computes\<close>,
      as \<^term>\<open>f\<close> is not required to be \<^const>\<open>bij\<close>.\<close>
  unfolding TM.computes_word_def TM.has_output_altdef
proof (intro conj_cong)
  from wf show "M'.halts (map f w) = halts w" by blast

  from wf have "last (tapes (M'.compute (map f w))) = last (map (map_tape f) (tapes (compute w)))"
    by simp
  also from wf have "... = map_tape f (last (tapes (compute w)))"
    by (subst last_map, intro wf_config_tapes_nonempty) blast+
  finally have *: "last (tapes (M'.compute (map f w))) = map_tape f (last (tapes (compute w)))" .

  have "last (tapes (M'.compute (map f w))) = <map f w'>\<^sub>t\<^sub>p
       \<longleftrightarrow> map_tape f (last (tapes (compute w))) = map_tape f <w'>\<^sub>t\<^sub>p" unfolding * by simp
  also have "... \<longleftrightarrow> last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p"
  proof (rule iffI, rule tape.inj_map_strong)
    fix z za
    assume "f z = f za"

    assume "z \<in> set_tape (last (tapes (compute w)))"
    moreover from wf have "set_tape (last (tapes (compute w))) \<subseteq> \<Sigma>" by (intro wf_config_last) blast
    ultimately have "z \<in> \<Sigma>" ..

    assume "za \<in> set_tape <w'>\<^sub>t\<^sub>p"
    with wf' have "za \<in> \<Sigma>" by auto

    with inj_f and \<open>f z = f za\<close> and \<open>z \<in> \<Sigma>\<close> show "z = za" by (rule inj_onD)
  qed force+

  finally show "last (tapes (M'.compute (map f w))) = <map f w'>\<^sub>t\<^sub>p
            \<longleftrightarrow> last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p" .
qed

end \<comment> \<open>\<^locale>\<open>TM_map_alphabet\<close>\<close>

context TM
begin


abbreviation map_alphabet :: "('s \<Rightarrow> 's2) \<Rightarrow> 's2 set \<Rightarrow> ('q, 's2, 'l) TM"
  where "map_alphabet \<equiv> TM_map_alphabet.M' M"

theorem map_alphabet_steps:
  fixes f :: "'s \<Rightarrow> 's2::finite"
  assumes "wf_config c"
    and inj_f: "inj_on f \<Sigma>"
    and range_f: "f ` \<Sigma> \<subseteq> \<Sigma>'"
    and finite_symbols: "finite \<Sigma>'"
  shows "TM.steps (map_alphabet f \<Sigma>') n (map_conf_tapes f c) = map_conf_tapes f (steps n c)"
proof -
  interpret TM_map_alphabet M f using inj_f range_f finite_symbols by (unfold_locales)
  from \<open>wf_config c\<close> have "M'.steps n (fc c) = fc (steps n c)" by (rule map_steps)
  then show ?thesis unfolding fc_def .
qed

end


subsubsection\<open>Simple Composition\<close>

locale simple_TM_comp = TM_abbrevs + M1: TM M1 + M2: TM M2
  for M1 :: "('q1, 's, 'l1) TM"
    and M2 :: "('q2, 's, 'l2) TM" +
  assumes k[simp]: "M1.k = M2.k"
    and symbols_eq[simp]: "M1.\<Sigma> = M2.\<Sigma>"
begin

text\<open>Note: as the \<^const>\<open>tape_count\<close> and \<^const>\<open>symbols\<close> of \<^term>\<open>M1\<close> and \<^term>\<open>M2\<close> are interchangeable,
  we opt to simplify properties of \<^term>\<open>M1\<close> to those of \<^term>\<open>M2\<close> where applicable.
  For this reason, we use the properties of \<^term>\<open>M2\<close> in definitions and on the left-hand-side of \<^emph>\<open>simp\<close>-rules.\<close>

lemma wf_hds_eq[simp]: "M1.wf_hds hds \<longleftrightarrow> M2.wf_hds hds" by simp


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

definition comp_rec :: "('q1 + 'q2, 's, 'l2) TM_record"
  where "comp_rec \<equiv> \<lparr>
    TM_record.tape_count = M2.k, symbols = M2.\<Sigma>,
    states = Inl ` M1.Q \<union> Inr ` M2.Q,
    initial_state = if M1.q\<^sub>0 \<in> M1.F then Inr M2.q\<^sub>0 else Inl M1.q\<^sub>0,
    final_states = Inr ` M2.F,
    label = \<lambda>q. case q of Inr q2 \<Rightarrow> M2.lab q2,
    next_state = \<lambda>q hds. case q of Inl q1 \<Rightarrow> let q1' = M1.\<delta>\<^sub>q q1 hds in
                                             if q1' \<in> M1.F then Inr M2.q\<^sub>0 else Inl q1'
                                 | Inr q2 \<Rightarrow> Inr (M2.\<delta>\<^sub>q q2 hds),
    next_write = \<lambda>q hds i. case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>w q1 hds i | Inr q2 \<Rightarrow> M2.\<delta>\<^sub>w q2 hds i,
    next_move  = \<lambda>q hds i. case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>m q1 hds i | Inr q2 \<Rightarrow> M2.\<delta>\<^sub>m q2 hds i
  \<rparr>"


lemma M_valid: "valid_TM comp_rec" unfolding comp_rec_def
proof (rule valid_TM_I)
  show "(if M1.q\<^sub>0 \<in> M1.F then Inr M2.q\<^sub>0 else Inl M1.q\<^sub>0) \<in> Inl ` M1.Q \<union> Inr ` M2.Q"
    by (rule ifI) blast+

  fix q hds
  assume "length hds = M2.k" and "set hds \<subseteq> M2.\<Sigma>\<^sub>t\<^sub>p"
  then have wf_hds: "M2.wf_hds hds" by auto
  assume q_valid: "q \<in> Inl ` M1.Q \<union> Inr ` M2.Q"
  then show "(case q of Inl q1 \<Rightarrow> let q1' = M1.\<delta>\<^sub>q q1 hds in if q1' \<in> M1.F then Inr M2.q\<^sub>0 else Inl q1'
        | Inr q2 \<Rightarrow> Inr (M2.\<delta>\<^sub>q q2 hds))
       \<in> Inl ` M1.Q \<union> Inr ` M2.Q"
  proof (induction q rule: case_sum_cases)
    case (Inl q1)
    then have "q1 \<in> M1.Q" by blast
    with wf_hds have "M1.\<delta>\<^sub>q q1 hds \<in> M1.Q" by simp
    then show ?case unfolding Let_def by (induction rule: ifI) blast+
  next
    case (Inr q2)
    then have "q2 \<in> M2.Q" by blast
    with wf_hds have "M2.\<delta>\<^sub>q q2 hds \<in> M2.Q" by blast
    then show ?case unfolding Let_def by (induction rule: ifI) blast+
  qed

  fix i
  assume "i < M2.k"
  then show "(case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>w q1 hds i | Inr q2 \<Rightarrow> M2.\<delta>\<^sub>w q2 hds i) \<in> M2.\<Sigma>\<^sub>t\<^sub>p"
    using wf_hds q_valid unfolding wf_hds_eq[symmetric]
  proof (induction q rule: case_sum_cases)
    case (Inl q1)
    then show ?case by (fold symbols_eq k) blast
  next
    case (Inr q2)
    then show ?case by fastforce
  qed
qed (use M2.symbol_axioms(2) M2.state_axioms(3) in blast)+

definition "M \<equiv> Abs_TM comp_rec"

sublocale TM M .

lemma M_rec: "M_rec = comp_rec" unfolding M_def using M_valid by (intro Abs_TM_inverse CollectI)
lemmas M_fields = TM_fields_defs[unfolded M_rec comp_rec_def TM_record.simps Let_def]
lemmas [simp] = M_fields(1-6)

definition cl :: "('q1, 's) TM_config \<Rightarrow> ('q1 + 'q2, 's) TM_config" where "cl \<equiv> map_conf_state Inl"
definition cr :: "('q2, 's) TM_config \<Rightarrow> ('q1 + 'q2, 's) TM_config" where "cr \<equiv> map_conf_state Inr"
lemma cl_simps[simp]: "state (cl c) = Inl (state c)" "tapes (cl c) = tapes c" "cl (TM_config q tps) = TM_config (Inl q) tps" unfolding cl_def by auto
lemma cr_simps[simp]: "state (cr c) = Inr (state c)" "tapes (cr c) = tapes c" "cr (TM_config q tps) = TM_config (Inr q) tps" unfolding cr_def by auto

lemma is_final_cl[simp]: "is_final (cl c) \<longleftrightarrow> False" by (auto simp: is_final_def)
lemma is_final_cr[simp]: "is_final (cr c) \<longleftrightarrow> M2.is_final c" by (auto simp: is_final_def)

lemma wf_config_simps[simp]:
  shows wf_config_cl: "wf_config (cl c1) \<longleftrightarrow> M1.wf_config c1"
    and wf_config_cr: "wf_config (cr c2) \<longleftrightarrow> M2.wf_config c2"
  by (fastforce elim!: TM.wf_config_transferI)+

lemma wf_config_transfer[intro,simp]: "M1.wf_config c \<Longrightarrow> M2.wf_config (TM_config M2.q\<^sub>0 (tapes c))"
  by (force simp: TM.wf_config_def)


lemma next_fun_cl_simps[simplified,simp]:
  assumes [simp]: "M1.wf_config c"
  defines "q \<equiv> state c" and "hds \<equiv> heads c"
  defines "q' \<equiv> state (cl c)" and "hds' \<equiv> heads (cl c)"
  shows "M1.\<delta>\<^sub>q q hds \<in> M1.F \<Longrightarrow> \<delta>\<^sub>q q' hds' = Inr M2.q\<^sub>0"
    and "M1.\<delta>\<^sub>q q hds \<notin> M1.F \<Longrightarrow> \<delta>\<^sub>q q' hds' = Inl (M1.\<delta>\<^sub>q q hds)"
    and "i < k \<Longrightarrow> \<delta>\<^sub>m q' hds' i = M1.\<delta>\<^sub>m q hds i"
    and "i < k \<Longrightarrow> \<delta>\<^sub>w q' hds' i = M1.\<delta>\<^sub>w q hds i"
  unfolding M_fields assms by auto

lemma next_fun_cr_simps[simplified,simp]:
  assumes [simp]: "M2.wf_config c"
  defines "q \<equiv> state c" and "hds \<equiv> heads c"
  defines "q' \<equiv> state (cr c)" and "hds' \<equiv> heads (cr c)"
  shows "\<delta>\<^sub>q q' hds' = Inr (M2.\<delta>\<^sub>q q hds)"
    and "i < k \<Longrightarrow> \<delta>\<^sub>m q' hds' i = M2.\<delta>\<^sub>m q hds i"
    and "i < k \<Longrightarrow> \<delta>\<^sub>w q' hds' i = M2.\<delta>\<^sub>w q hds i"
  unfolding M_fields assms by auto

lemma next_actions_simps[simp]:
  shows "M1.wf_config c1 \<Longrightarrow> \<delta>\<^sub>a (Inl (state c1)) (heads c1) = M1.\<delta>\<^sub>a (state c1) (heads c1)"
    and "M2.wf_config c2 \<Longrightarrow> \<delta>\<^sub>a (Inr (state c2)) (heads c2) = M2.\<delta>\<^sub>a (state c2) (heads c2)"
  unfolding TM.next_actions_altdef by auto

lemma comp_step1_not_final:
  assumes step_nf: "\<not> M1.is_final (M1.step c)"
    and [simp]: "M1.wf_config c"
  shows "step (cl c) = cl (M1.step c)" (is "step ?c = cl (M1.step c)")
proof -
  from step_nf have nf': "\<not> M1.is_final c" by blast
  then have "\<not> is_final ?c" by auto

  then have "step ?c = step_not_final ?c" by blast
  also have "... = cl (M1.step_not_final c)"
  proof (rule TM_config_eq)
    from step_nf have "M1.\<delta>\<^sub>q (state c) (heads c) \<notin> M1.F" using nf' by auto
    then show "state (step_not_final ?c) = state (cl (M1.step_not_final c))" by simp
    show "tapes (step_not_final ?c) = tapes (cl (M1.step_not_final c))" by simp
  qed
  also from nf' have "... = cl (M1.step c)" by simp
  finally show ?thesis .
qed

lemma comp_steps1_non_final:
  assumes "\<not> M1.is_final (M1.steps n c)"
    and [simp]: "M1.wf_config c"
  shows "steps n (cl c) = cl (M1.steps n c)"
proof -
  have "0 \<le> n" by (rule le0)
  then show "steps n (cl c) = cl (M1.steps n c)"
  proof (induction n rule: dec_induct)
    case (step n')
    have "steps (Suc n') (cl c) = step (steps n' (cl c))" unfolding funpow.simps comp_def ..
    also have "... = step (cl (M1.steps n' c))" unfolding step.IH ..
    also have "... = cl (M1.step (M1.steps n' c))"
    proof (rule comp_step1_not_final)
      from \<open>n' < n\<close> have "Suc n' \<le> n" by (rule Suc_leI)
      with assms have "\<not> M1.is_final (M1.steps (Suc n') c)" using M1.final_mono by blast
      then show "\<not> M1.is_final (M1.step (M1.steps n' c))" unfolding funpow.simps comp_def .
    qed fastforce
    also have "... = cl (M1.steps (Suc n') c)" by simp
    finally show *: "steps (Suc n') (cl c) = cl (M1.steps (Suc n') c)" .
  qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp
qed

corollary comp_steps1_non_final':
  assumes "n < M1.config_time c"
    and [simp]: "M1.wf_config c"
  shows "steps n (cl c) = cl (M1.steps n c)"
  using assms by (blast intro!: comp_steps1_non_final)

lemma comp_step1_next_final:
  assumes nf': "\<not> M1.is_final c"
    and step_final: "M1.is_final (M1.step c)"
    and [simp]: "M1.wf_config c"
  shows "step (cl c) = TM_config (Inr M2.q\<^sub>0) (tapes (M1.step c))"
  (is "step ?c = ?c\<^sub>0 (M1.step c)")
proof -
  from assms(1-2) have "\<not> is_final ?c" by auto

  then have "step ?c = step_not_final ?c" by blast
  also have "... = ?c\<^sub>0 (M1.step_not_final c)"
  proof (rule TM_config_eq, unfold TM_config.sel)
    from step_final have "M1.\<delta>\<^sub>q (state c) (heads c) \<in> M1.F" using nf' by force
    then show "state (step_not_final ?c) = Inr M2.q\<^sub>0" by simp
    show "tapes (step_not_final ?c) = tapes (M1.step_not_final c)" by simp
  qed
  also from nf' have "... = ?c\<^sub>0 (M1.step c)" by simp
  finally show ?thesis .
qed

lemma comp_steps1_final:
  assumes "\<not> M1.is_final c"
    and "M1.halts_config c"
    and wfc[simp]: "M1.wf_config c"
  defines "n \<equiv> M1.config_time c"
  shows "steps n (cl c) = TM_config (Inr M2.q\<^sub>0) (tapes (M1.steps n c))"
proof -
  from \<open>\<not> M1.is_final c\<close> have "\<not> M1.is_final (M1.steps 0 c)" by simp
  with \<open>M1.halts_config c\<close> have "n > 0" unfolding n_def by blast
  then obtain n' where "n = Suc n'" by (rule lessE)
  then have "n' < n" by blast

  have *: "TM.steps M n c = TM.step M (TM.steps M n' c)" for M :: "('x, 'y, 'z) TM" and c
    unfolding \<open>n = Suc n'\<close> funpow.simps comp_def ..
  from \<open>n' < n\<close> and wfc have **: "steps n' (cl c) = cl (M1.steps n' c)"
    unfolding n_def by (rule comp_steps1_non_final')

  show ?thesis unfolding * **
  proof (rule comp_step1_next_final)
    from \<open>n' < n\<close> show "\<not> M1.is_final (M1.steps n' c)" unfolding n_def by blast
    from \<open>M1.halts_config c\<close> show "M1.is_final (M1.step (M1.steps n' c))"
      unfolding *[symmetric] n_def by blast
  qed fastforce
qed

lemma comp_step2:
  assumes [simp]: "M2.wf_config c"
  shows "step (cr c) = cr (M2.step c)"
proof (cases "M2.is_final c")
  assume nf: "\<not> M2.is_final c"
  then have "\<not> is_final (cr c)" by fastforce

  then have "step (cr c) = step_not_final (cr c)" ..
  also have "... = cr (M2.step_not_final c)" by (rule TM_config_eq) simp_all
  also from nf have "... = cr (M2.step c)" by simp
  finally show ?thesis .
qed \<comment> \<open>case \<^term>\<open>M2.is_final c\<close> by\<close> simp

lemma comp_steps2:
  assumes wfc[simp]: "M2.wf_config c_init2"
  shows "steps n2 (cr c_init2) = cr (M2.steps n2 c_init2)" using le0
proof (induction n2 rule: dec_induct)
  case (step n2)
  show ?case unfolding funpow.simps comp_def step.IH
    using wfc by (blast intro: comp_step2)
qed \<comment> \<open>case \<open>n2 = 0\<close> by\<close> simp

lemma comp_steps_final:
  fixes c_init1 n1 n2
  defines "c_fin1 \<equiv> M1.steps n1 c_init1"
  defines "c_init2 \<equiv> TM_config M2.q\<^sub>0 (tapes c_fin1)"
  defines "c_fin2 \<equiv> M2.steps n2 c_init2"
  assumes ci1_nf: "\<not> M1.is_final c_init1"
    and cf1: "M1.is_final c_fin1"
    and cf2: "M2.is_final c_fin2"
    and wfc1[simp]: "M1.wf_config c_init1"
  shows "steps (n1+n2) (cl c_init1) = cr c_fin2" (is "steps ?n ?c0 = _")
proof -
  let ?n1' = "M1.config_time c_init1"
  from cf1 have "?n1' \<le> n1" unfolding c_fin1_def by blast

  from ci1_nf cf1 wfc1 have "steps ?n1' ?c0 = TM_config (Inr M2.q\<^sub>0) (tapes (M1.steps ?n1' c_init1))"
    unfolding c_fin1_def by (intro comp_steps1_final) blast+
  also from cf1 have "... = cr c_init2" unfolding c_init2_def c_fin1_def cr_def by auto
  finally have steps_n1': "steps ?n1' ?c0 = cr c_init2" .

  from wfc1 have wfc2[simp]: "M2.wf_config c_init2" unfolding c_init2_def c_fin1_def by blast

  from cf2 have "is_final (steps (n2 + ?n1') ?c0)"
    unfolding funpow_add comp_def unfolding steps_n1' c_fin2_def by (subst comp_steps2) auto
  moreover from \<open>?n1' \<le> n1\<close> have "n2 + ?n1' \<le> ?n" by simp
  ultimately have "steps ?n ?c0 = steps (n2 + ?n1') ?c0" by (rule final_le_steps)

  also have "... = steps n2 (cr c_init2)" unfolding funpow_add comp_def steps_n1' ..
  also have "... = cr c_fin2" unfolding c_fin2_def by (force simp: comp_steps2)
  finally show ?thesis .
qed


lemma comp_run:
  fixes w n1 n2
  defines "c_fin1 \<equiv> M1.run n1 w"
  defines "c_init2 \<equiv> TM_config M2.q\<^sub>0 (tapes c_fin1)"
  defines "c_fin2 \<equiv> M2.steps n2 c_init2"
  assumes cf1: "M1.is_final c_fin1"
    and cf2: "M2.is_final c_fin2"
    and wfw: "M1.wf_input w"
  shows "run (n1+n2) w = cr c_fin2"
    (is "run ?n w = _")
proof (cases "M1.q\<^sub>0 \<in> M1.F")
  assume q0f: "M1.q\<^sub>0 \<in> M1.F"
  then have "c\<^sub>0 w = cr (M2.c\<^sub>0 w)" unfolding TM.initial_config_def cr_def by simp
  then have "run ?n w = steps ?n (cr (M2.c\<^sub>0 w))" unfolding run_def by presburger
  also have "... = cr (M2.steps ?n (M2.c\<^sub>0 w))" using wfw by (simp add: comp_steps2)
  also have "... = cr (M2.steps ?n c_init2)"
  proof -
    from q0f have [simp]: "c_fin1 = M1.initial_config w" unfolding c_fin1_def M1.run_def by (simp add: TM.is_final_def)
    have "M2.initial_config w = c_init2" unfolding c_init2_def by (simp add: TM.initial_config_def)
    then show ?thesis by (rule arg_cong)
  qed
  also from cf2 have "... = cr c_fin2" unfolding c_fin2_def
    by (intro arg_cong[where f=cr], elim M2.final_le_steps) simp
  finally show ?thesis .
next
  assume "M1.q\<^sub>0 \<notin> M1.F"
  then have *: "run n w = steps n (cl (M1.initial_config w))" for n w
    unfolding cl_def run_def by (simp add: TM.initial_config_def)
  from \<open>M1.q\<^sub>0 \<notin> M1.F\<close> have "\<not> M1.is_final (M1.initial_config w)" by (simp add: TM.is_final_def)
  with cf1 cf2 wfw show ?thesis unfolding assms * M1.run_def
    by (intro comp_steps_final M1.wf_initial_config)
qed

lemma final_is_Inr:
  assumes "q \<in> F"
  obtains q' :: 'q2 where "q = Inr q'"
  using assms by auto
end

definition TM_comp :: "('q1, 's, 'l1) TM \<Rightarrow> ('q2, 's, 'l2) TM \<Rightarrow> ('q1 + 'q2, 's, 'l2) TM"
  where "TM_comp M1 M2 \<equiv> simple_TM_comp.M M1 M2"

theorem TM_comp_steps_final:
  fixes M1 :: "('q1, 's, 'l1) TM" and M2 :: "('q2, 's, 'l2) TM"
    and c_init1 :: "('q1, 's) TM_config"
    and n1 n2 :: nat
  assumes k: "TM.tape_count M1 = TM.tape_count M2"
    and symbols_eq: "TM.TM.symbols M1 = TM.TM.symbols M2"
  defines "c_fin1 \<equiv> TM.steps M1 n1 c_init1"
  assumes c_init2_def: "c_init2 = TM_config (TM.q\<^sub>0 M2) (tapes c_fin1)" \<comment> \<open>Assumed, not defined, to reduce the term size of the overall lemma.\<close>
  defines "c_fin2 \<equiv> TM.steps M2 n2 c_init2"
  assumes ci1_nf: "\<not> TM.is_final M1 c_init1"
    and cf1: "TM.is_final M1 c_fin1"
    and cf2: "TM.is_final M2 c_fin2"
    and wfc1: "TM.wf_config M1 c_init1"
  shows "TM.steps (TM_comp M1 M2) (n1+n2) (simple_TM_comp.cl c_init1) = simple_TM_comp.cr c_fin2"
  using k symbols_eq ci1_nf cf1 cf2 wfc1
  unfolding c_fin1_def c_init2_def c_fin2_def TM_comp_def
  by (intro simple_TM_comp.comp_steps_final simple_TM_comp.intro)


subsubsection\<open>Composition with Tape-Offset/Separate Tape Ranges\<close>

text\<open>Combine \<^locale>\<open>simple_TM_comp\<close> and \<^locale>\<open>TM_tape_offset\<close> to define a composition
  where the output of the first TM becomes the input for the second one.\<close>

locale IO_TM_comp = TM_abbrevs + M1: TM M1 + M2: TM M2
  for M1 :: "('q1, 's, 'l1) TM" and M2 :: "('q2, 's, 'l2) TM" +
  assumes symbols_eq: "M1.\<Sigma> = M2.\<Sigma>"
begin

definition "k1 \<equiv> M1.k"
definition "k2 \<equiv> M2.k"
lemmas Mx_k_simps[simp] = k1_def[symmetric] k2_def[symmetric]

sublocale M1: TM_tape_offset M1 0 "k2 - (Suc 0)" .
sublocale M2: TM_tape_offset M2 "k1 - (Suc 0)" 0 .

abbreviation "M1' \<equiv> M1.M'"
abbreviation "M2' \<equiv> M2.M'"

lemma M1'_M2'_k: "M1.M'.k = M2.M'.k" unfolding M1.M'_fields(1) M2.M'_fields(1)
  using M1.at_least_one_tape' M2.at_least_one_tape' by simp
lemma symbols_eq': "M1.M'.\<Sigma> = M2.M'.\<Sigma>"
  unfolding M1.M'_fields(2) M2.M'_fields(2) symbols_eq ..

sublocale simple_TM_comp M1' M2' using M1'_M2'_k symbols_eq' by unfold_locales

declare M_fields(1)[simp del]

lemma k_def: "k = k1 + k2 - (Suc 0)" using M1.at_least_one_tape' by (simp add: M_fields(1))

lemma M1'_k[simp]: "M1.M'.k = k" using M2.at_least_one_tape' by (simp add: k_def)
lemma M2'_k[simp]: "M2.M'.k = k" using M1'_k unfolding M1'_M2'_k .

lemma M1_is_len[simp]: "length M1.is = k" using M1'_k unfolding M1.M'_fields .
lemma M2_is_len[simp]: "length M2.is = k" using M2'_k unfolding M2.M'_fields .

lemma k_simps[simp]:
  shows "k1 + (k2 - Suc 0) = k1 + k2 - Suc 0"
    and "k - k1 = k2 - Suc 0"
    and "k1 - Suc 0 + k2 = k"
    and "k2 + (k1 - Suc 0) = k"
  unfolding k_def using M1.at_least_one_tape' M2.at_least_one_tape' by auto

lemma init_conf1:
  assumes "M1.q\<^sub>0 \<notin> M1.F"
  shows "c\<^sub>0 w = cl (M1.M'.c\<^sub>0 w)"
proof -
  from \<open>M1.q\<^sub>0 \<notin> M1.F\<close> have q0: "q\<^sub>0 = Inl M1.q\<^sub>0" unfolding M_fields M1.M'_fields by (rule if_not_P)

  have "c\<^sub>0 w = TM_config (Inl M1.q\<^sub>0) (<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1))" unfolding initial_config_def q0 ..
  also have "... = cl (TM_config M1.q\<^sub>0 (<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1)))" unfolding cl_simps ..
  also have "... = cl (M1.M'.c\<^sub>0 w)" unfolding reorder_config_def
  proof (rule TM_config_eq, unfold cl_simps TM_config.sel)
    show "Inl M1.q\<^sub>0 = Inl (state (M1.M'.c\<^sub>0 w))" unfolding M1.M'.init_conf_state M1.M'_fields(4) ..

    have "tapes (M1.M'.c\<^sub>0 w) = tapes (M1.rc (\<langle>\<rangle> \<up> k) (M1.c\<^sub>0 w))"
      by (subst M1.init_conf_offset_eq, unfold M1_is_len) blast+
    also have "... = M1.r (\<langle>\<rangle> \<up> k) (tapes (M1.c\<^sub>0 w))" by simp
    also have "M1.r (\<langle>\<rangle> \<up> k) (tapes (M1.c\<^sub>0 w)) = tapes (M1.c\<^sub>0 w) @ take (M2.k - 1) (drop M1.k (\<langle>\<rangle> \<up> k))"
      using M2.at_least_one_tape unfolding k_def by (subst M1.tape_offset_simps1) auto
    also have "... = tapes (M1.c\<^sub>0 w) @ (\<langle>\<rangle> \<up> (M2.k - 1))" unfolding k_def by simp
    also have "... = (<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (M1.k - 1)) @ (\<langle>\<rangle> \<up> (M2.k - 1))"
      unfolding append_same_eq M1.initial_config_def by simp
    also have "... = <w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1)" unfolding append_Cons replicate_add[symmetric]
      using M1.at_least_one_tape' M2.at_least_one_tape' by simp
    finally show "<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1) = tapes (M1.M'.c\<^sub>0 w)" ..
  qed
  finally show ?thesis .
qed

corollary init_conf1': "M1.M'.c\<^sub>0 w = M1.rc (\<langle>\<rangle> \<up> k) (M1.c\<^sub>0 w)"
  by (subst M1.init_conf_offset_eq, unfold M1_is_len) blast+

lemma take_reorder_le:
  "take (k1 - 1) (M1.r (\<langle>\<rangle> \<up> k) (tapes (M1.run n w))) = butlast (tapes (M1.run n w))"
  (is "take (k1 - 1) ?r1 = butlast (tapes ?c1)")
proof -
  have "take (k1 - 1) ?r1 = take (k1 - 1) (tapes ?c1 @ take (k2 - 1) (drop k1 (\<langle>\<rangle> \<up> k)))"
    unfolding k_def by (subst M1.tape_offset_simps1) auto
  also have "... = take (k1 - 1) (tapes ?c1)" unfolding drop_replicate k_simps by simp
  also have "... = butlast (tapes ?c1)" unfolding butlast_conv_take by simp
  finally show ?thesis .
qed

corollary take_reorder_le'[simp]:
  "take (k1 - 1) (M1.r (\<langle>\<rangle> \<up> k) (tapes (M1.compute w))) = butlast (tapes (M1.compute w))"
  unfolding M1.compute_altdef by (fact take_reorder_le)


lemma io_comp_run1:
  assumes comp_w: "M1.computes_word w w'"
    and wfw[simp]: "M1.wf_input w"
  shows "run (M1.time w) w = cr (M2.rc (tapes (M1.rc (\<langle>\<rangle> \<up> k) (M1.compute w))) (M2.c\<^sub>0 w'))"
proof (cases "M1.q\<^sub>0 \<in> M1.F")
  assume q0_f: "M1.q\<^sub>0 \<in> M1.F"
  then have q0_f': "M1.is_final (M1.c\<^sub>0 w)" by auto
  then have "M1.time w = 0" and "M1.halts w" by (auto simp: TM.halts_def)
  then have *[simp]: "TM.run M (M1.time w) w = TM.c\<^sub>0 M w" for M :: "('x, 's, 'y) TM"
    unfolding TM.run_def by simp
  with q0_f' have **[simp]: "M1.compute w = M1.c\<^sub>0 w" by simp

  from q0_f have q0: "q\<^sub>0 = Inr M2.q\<^sub>0" unfolding M_fields(4) M1.M'_fields(4-5) M2.M'_fields(4) by simp

  show ?thesis unfolding * ** init_conf1'[symmetric]
  proof (cases "k1 = 1")
    assume "k1 = 1"
    then have "<w>\<^sub>t\<^sub>p = last (tapes (M1.compute w))" unfolding ** by simp
    also from comp_w have "... = <w'>\<^sub>t\<^sub>p" by blast
    finally have "w' = w" by simp

    have "cr (M2.rc (tapes (M1.M'.c\<^sub>0 w)) (M2.c\<^sub>0 w')) =
            TM_config (Inr M2.q\<^sub>0) (M2.r (tapes (M1.M'.c\<^sub>0 w)) (tapes (M2.c\<^sub>0 w')))"
      unfolding reorder_config_def by simp
    also have "... = TM_config (Inr M2.q\<^sub>0) (tapes (M2.c\<^sub>0 w'))"
      by (subst M2.tape_offset_simps2) (unfold TM.init_conf_len M1'_k k_def, unfold \<open>k1 = 1\<close>, auto)
    also have "... = c\<^sub>0 w" unfolding \<open>w' = w\<close> TM.initial_config_def TM_config.sel TM_config.inject Mx_k_simps
    proof (intro conjI)
      from q0_f show "Inr M2.q\<^sub>0 = q\<^sub>0" unfolding M_fields M1.M'_fields M2.M'_fields by simp

      have "k2 = k" unfolding k_def unfolding \<open>k1 = 1\<close> using M2.at_least_one_tape by simp
      then show "<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k2 - 1) = <w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1)" by (rule arg_cong)
    qed
    finally show "c\<^sub>0 w = cr (M2.rc (tapes (M1.M'.c\<^sub>0 w)) (M2.c\<^sub>0 w'))" ..
  next
    assume "k1 \<noteq> 1"
    with M1.at_least_one_tape' have "k1 > 1" by simp
    then have "k1 - Suc 0 \<noteq> 0" by simp

    note input_tape.simps(1)
    also from \<open>k1 > 1\<close> have "\<langle>\<rangle> = last (tapes (M1.compute w))" unfolding ** by simp
    also from comp_w have "... = <w'>\<^sub>t\<^sub>p" by blast
    finally have "w' = []" by fastforce
    have *: "tapes (M2.c\<^sub>0 w') = \<langle>\<rangle> \<up> k2" unfolding TM.initial_config_def TM_config.sel \<open>w' = []\<close>
      unfolding input_tape.simps replicate_Suc[symmetric] using M2.at_least_one_tape by simp

    have "min (k1 - Suc 0 - 1) (M1.M'.k - 1) = k1 - Suc 0 - 1"
      unfolding M1'_k k_def by (intro min_absorb1) simp
    then have **: "take (k1 - Suc 0) (tapes (M1.M'.c\<^sub>0 w)) = <w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k1 - Suc 0 - 1)"
      unfolding TM.initial_config_def TM_config.sel take_Cons' if_not_P[OF \<open>k1 - (Suc 0) \<noteq> 0\<close>]
      unfolding take_replicate by simp

    have ***: "k1 - 1 - 1 + k2 = k - 1" unfolding k_def using \<open>1 < k1\<close> by simp

    have "cr (M2.rc (tapes (M1.M'.c\<^sub>0 w)) (M2.c\<^sub>0 w')) =
            TM_config (Inr M2.q\<^sub>0) (M2.r (tapes (M1.M'.c\<^sub>0 w)) (tapes (M2.c\<^sub>0 w')))"
      unfolding reorder_config_def by simp
    also have "... = TM_config (Inr M2.q\<^sub>0) (<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k1 - 1 - 1) @ \<langle>\<rangle> \<up> k2)"
      by (subst M2.tape_offset_simps2, unfold TM.init_conf_len M1'_k * **) auto
    also have "... = TM_config (Inr M2.q\<^sub>0) (<w>\<^sub>t\<^sub>p # \<langle>\<rangle> \<up> (k - 1))" unfolding replicate_add[symmetric] *** ..
    also have "... = c\<^sub>0 w" unfolding initial_config_def q0 ..
    finally show "c\<^sub>0 w = cr (M2.rc (tapes (M1.M'.c\<^sub>0 w)) (M2.c\<^sub>0 w'))" ..
  qed
next
  assume q0_nf: "M1.q\<^sub>0 \<notin> M1.F"
  then have q0: "q\<^sub>0 = Inl M1.q\<^sub>0" unfolding M_fields(4) M1.M'_fields(4-5) M2.M'_fields(4) by simp
  from \<open>M1.wf_input w\<close> have time1: "M1.time w = M1.M'.time w" using M1.offset_time by presburger

  from comp_w have [simp]: "M1.compute w = M1.run (M1.time w) w" by blast

  let ?c1 = "M1.compute w" let ?r1 = "M1.r (\<langle>\<rangle> \<up> k) (tapes ?c1)"

  have "run (M1.time w) w = run (M1.M'.time w) w" unfolding time1 ..
  also have "... = steps (M1.M'.config_time (M1.M'.c\<^sub>0 w)) (c\<^sub>0 w)" unfolding run_def by simp
  also have "... = TM_config (Inr M2.M'.q\<^sub>0) (tapes (M1.M'.run (M1.time w) w))"
    unfolding init_conf1[OF q0_nf]
  proof (subst comp_steps1_final, fold M1.M'.time_def time1 TM.run_def)
    from q0_nf show "\<not> M1.M'.is_final (M1.M'.c\<^sub>0 w)"
      unfolding M1.M'.initial_config_def M1.M'_fields by (simp add: TM.is_final_def)

    from \<open>M1.computes_word w w'\<close> have "M1.halts w" by blast
    then have "M1.halts_config (M1.c\<^sub>0 w)" by (simp add: M1.halts_def)
    with \<open>M1.wf_input w\<close> have "M1.M'.halts_config (M1.rc (\<langle>\<rangle> \<up> k) (M1.c\<^sub>0 w))"
      by (subst M1.reorder_halts, unfold M1_is_len) auto
    then show "M1.M'.halts_config (M1.M'.c\<^sub>0 w)"
      by (subst M1.init_conf_offset_eq, unfold M1_is_len) blast+
  qed (use wfw in force)+
  also have "... = TM_config (Inr M2.M'.q\<^sub>0) (tapes (M1.rc (\<langle>\<rangle> \<up> k) ?c1))"
    unfolding init_conf1' TM.run_def unfolding M2.M'_fields(3)
  proof (subst M1.reorder_steps)
    from \<open>M1.wf_input w\<close> show "M1.wf_config (M1.c\<^sub>0 w)" by blast
    show "length (\<langle>\<rangle> \<up> k) = length M1.is" unfolding M1_is_len by simp
  qed simp_all
  also have "... = cr (M2.rc (tapes (M1.rc (\<langle>\<rangle> \<up> k) ?c1)) (M2.c\<^sub>0 w'))"
  proof (rule TM_config_eq, unfold TM_config.sel cr_simps reorder_config_simps)
    show "Inr M2.M'.q\<^sub>0 = Inr (state (M2.c\<^sub>0 w'))" unfolding TM.init_conf_simps M2.M'_fields(4) ..

    have "k - k1 = M2.k - 1" unfolding k_def by simp

    have "?r1 = tapes ?c1 @ (\<langle>\<rangle> \<up> (k2 - 1))" using M2.at_least_one_tape unfolding k_def
      by (subst M1.tape_offset_simps1) auto
    also have "... = (butlast (tapes ?c1)) @ [last (tapes ?c1)] @ (\<langle>\<rangle> \<up> (k2 - 1))"
      unfolding append_assoc[symmetric]
    proof (subst append_butlast_last_id)
      from M1.at_least_one_tape show "tapes (M1.compute w) \<noteq> []"
        unfolding length_greater_0_conv[symmetric] by simp
    qed blast
    also have "... = (take (k1 - 1) ?r1) @ [last (tapes ?c1)] @ (\<langle>\<rangle> \<up> (k2 - 1))"
      unfolding append_same_eq M1.compute_altdef take_reorder_le ..
    also have "... = (take (k1 - 1) ?r1) @ tapes (M2.c\<^sub>0 w')"
    proof -
      from \<open>M1.computes_word w w'\<close> have l_tp: "last (tapes (M1.compute w)) = <w'>\<^sub>t\<^sub>p" by blast
      show ?thesis unfolding same_append_eq M2.initial_config_def TM_config.sel unfolding l_tp by simp
    qed
    also have "... = M2.r ?r1 (tapes (M2.c\<^sub>0 w'))" unfolding One_nat_def
      by (subst M2.tape_offset_simps2) (simp, simp, blast)
    finally show "?r1 = ..." .
  qed
  finally show ?thesis .
qed

lemma io_comp_steps2:
  assumes "M2.halts w"
    and wfw[simp]: "M2.wf_input w"
    and l_tps: "length tps = k"
    and wf_tps: "\<forall>tp\<in>set tps. set_tape tp \<subseteq> M2.\<Sigma>"
  shows "steps t2 (cr (M2.rc tps (M2.c\<^sub>0 w))) = cr (M2.rc tps (M2.run t2 w))"
  (is "steps t2 (cr ?c\<^sub>0') = cr (M2.rc tps ?c)")
proof -
  from l_tps have l_tps': "length tps = length M2.is" unfolding TM.tape_offset_length Mx_k_simps k_simps add_0_right .
  with wfw wf_tps have "M2.M'.wf_config (M2.rc tps (M2.c\<^sub>0 w))" by (intro M2.M'_wf_config) blast+
  then have "steps t2 (cr ?c\<^sub>0') = cr (M2.M'.steps t2 ?c\<^sub>0')" by (subst comp_steps2) blast+
  also have "... = cr (M2.rc tps ?c)" unfolding M2.run_def using wfw l_tps' wf_tps
    by (subst M2.reorder_steps, unfold M2_is_len) blast+
  finally show ?thesis .
qed

theorem io_comp_run:
  assumes "M1.computes_word w w'"
    and "M1.wf_input w"
    and "M2.wf_input w'"
    and "M2.halts w'"
  shows "run (M1.time w + t2) w =
    cr (M2.rc (tapes (M1.rc (\<langle>\<rangle> \<up> k) (M1.compute w))) (M2.run t2 w'))"
    (is "run (?t1 + t2) w = cr (M2.rc ?tps ?c2)")
proof -
  have "run (?t1 + t2) w = steps t2 (run ?t1 w)" unfolding run_def using steps_plus ..
  also from assms(1-2) have "... = steps t2 (cr (M2.rc ?tps (M2.c\<^sub>0 w')))"
    by (subst io_comp_run1) blast+
  also from assms(3-4) have "... = cr (M2.rc ?tps ?c2)"
  proof (subst io_comp_steps2)
    show "\<forall>tp\<in>set ?tps. set_tape tp \<subseteq> M2.\<Sigma>"
    proof (intro ballI)
      fix tp
      assume "tp \<in> set ?tps"
      then show "set_tape tp \<subseteq> M2.\<Sigma>" unfolding reorder_config_tapes
      proof (cases rule: reorder_in_set')
        assume "tp \<in> set (tapes (M1.compute w))"
        moreover from \<open>M1.wf_input w\<close> have "M1.wf_config (M1.compute w)" by blast
        ultimately have "set_tape tp \<subseteq> M1.\<Sigma>" by fast
        then show "set_tape tp \<subseteq> M2.\<Sigma>" using symbols_eq by simp
      qed simp
    qed
  qed auto
  finally show ?thesis .
qed

corollary io_comp_run':
  fixes t2 :: nat
  assumes "M1.computes_word w w'"
    and "M1.wf_input w"
    and "M2.wf_input w'"
    and "M2.halts w'"
  defines "c1 \<equiv> M1.compute w"
  defines "c2 \<equiv> M2.run t2 w'"
  shows "run (M1.time w + t2) w = TM_config (Inr (state c2)) (butlast (tapes c1) @ (tapes c2))"
    (is "run (?t1 + t2) w = TM_config ?q2 (butlast ?tps1 @ ?tps2)")
proof -
  let ?tps = "tapes (M1.rc (\<langle>\<rangle> \<up> k) (M1.compute w))"
  have "run (?t1 + t2) w = cr (M2.rc ?tps (M2.run t2 w'))" unfolding io_comp_run[OF assms(1-4)] ..
  also have "... = TM_config ?q2 ((take (M1.k - 1) ?tps) @ ?tps2)"
    unfolding reorder_config_def cr_simps TM_config.sel c2_def Mx_k_simps One_nat_def
    by (subst M2.tape_offset_simps2) (simp, simp, blast+)
  also have "... = TM_config ?q2 (butlast ?tps1 @ ?tps2)"
    unfolding reorder_config_tapes take_reorder_le' c1_def Mx_k_simps ..
  finally show ?thesis .
qed

end \<comment> \<open>\<^locale>\<open>IO_TM_comp\<close>\<close>


subsubsection\<open>Composition of Arbitrary TMs\<close>

text\<open>This is designed to allow composition of TMs that we do not know anything about.
  As it is common practise in complexity theoretic proofs to obtain TMs from existence
  (``from \<open>L \<in> DTIME(T)\<close> we obtain \<open>M\<close> where ...'').\<close>


locale arb_TM_comp = M1a: TM_map_alphabet M1 f1 + M2a: TM_map_alphabet M2 f2
  for M1 :: "('q1, 's1, 'l1) TM"
    and M2 :: "('q2, 's2, 'l2) TM"
    and f1 :: "('s1 \<Rightarrow> 's)"
    and f2 :: "('s2 \<Rightarrow> 's)" +
  assumes symbols_eq_a: "f1 ` M1a.\<Sigma> = f2 ` M2a.\<Sigma>"
begin

abbreviation "M1a \<equiv> M1a.M'"
abbreviation "M2a \<equiv> M2a.M'"
sublocale IO_TM_comp M1a M2a using symbols_eq_a by unfold_locales simp

lemma arb_comp_run:
  fixes t2 :: nat
  assumes wf_w_in: "w_in \<in> M1a.\<Sigma>*"
    and wf_w_out1: "w_out1 \<in> M1a.\<Sigma>*"
    and wf_w_out2: "w_out2 \<in> M2a.\<Sigma>*"
    and M1: "M1a.computes_word w_in w_out1"
    and w_out_eq: "map f1 w_out1 = map f2 w_out2"
    and M2: "M2a.halts w_out2"
  defines "c1 \<equiv> M1a.compute w_in"
  defines "c2 \<equiv> M2a.run t2 w_out2"
  shows "run (M1a.time w_in + t2) (map f1 w_in) = TM_config (Inr (state c2)) (butlast (tapes (M1a.fc c1)) @ (tapes (M2a.fc c2)))"
    (is "run (?t1 + t2) ?w_in = TM_config ?q2 (butlast ?tps1 @ ?tps2)")
proof -
  let ?w_out = "map f1 w_out1"

  from M1 have M1': "M1a.M'.computes_word (map f1 w_in) ?w_out"
    using wf_w_in wf_w_out1 by (subst M1a.map_computes_word) blast+
  from M2 have M2': "M2a.M'.halts ?w_out" unfolding w_out_eq using wf_w_out2 by blast

  note M2a_map_run = M2a.map_run[OF wf_w_out2]

  have "run (?t1 + t2) (map f1 w_in) = run (M1a.M'.time (map f1 w_in) + t2) (map f1 w_in)"
    using wf_w_in M1a.map_time by auto
  also from M1' M2' have "... = TM_config (Inr (state (M2a.M'.run t2 ?w_out)))
     (butlast (tapes (M1a.M'.compute (map f1 w_in))) @ tapes (M2a.M'.run t2 ?w_out))"
  proof (subst io_comp_run')
    from M1a.range_f wf_w_in show "map f1 w_in \<in> M1a.M'.\<Sigma>*" by auto
    from M2a.range_f wf_w_out1 show "map f1 w_out1 \<in> M2a.M'.\<Sigma>*" by (fold symbols_eq symbols_eq_a) auto
  qed blast+
  also have "... = TM_config ?q2 (butlast ?tps1 @ ?tps2)"
  proof (rule TM_config_eq; unfold TM_config.sel)
    show "Inr (state (M2a.M'.run t2 ?w_out)) = Inr (state c2)"
      unfolding w_out_eq M2a_map_run M2a.fc_simps c2_def ..
    show "butlast (tapes (M1a.M'.compute (map f1 w_in))) @ tapes (M2a.M'.run t2 ?w_out) =
          butlast ?tps1 @ ?tps2"
      unfolding w_out_eq M1a.map_compute[OF wf_w_in] M2a_map_run unfolding c1_def c2_def ..
  qed
  finally show ?thesis .
qed

end \<comment> \<open>\<^locale>\<open>arb_TM_comp\<close>\<close>

lemma computable_in_time_compI: "typed_computable_in_time TYPE('q1) TYPE('l1) T1 f \<Longrightarrow>
                                 typed_computable_in_time TYPE('q2) TYPE('l2) T2 g \<Longrightarrow>
                                 computable_in_time (\<lambda>n. max_Tf T2 f n + T1 n) (g \<circ> f)"
proof (erule computableE)+
  fix M1 :: "('q1, 'a, 'l1) TM" and M2 :: "('q2, 'a, 'l2) TM"
  assume a1: "TM.computes M1 f" and a2: "\<forall>w. TM.time_bounded_word M1 T1 w" and
         a3: "TM.symbols M1 = UNIV" and a4: "TM.computes M2 g" and
         a5: "\<forall>w. TM.time_bounded_word M2 T2 w" and a6: "TM.symbols M2 = UNIV"
  interpret M1M2_comp: IO_TM_comp M1 M2
  proof
    show "TM.TM.symbols M1 = TM.TM.symbols M2" by (simp only: a3 a6)
  qed
  have 1: "M1M2_comp.M1.computes_word w (f w)" for w :: "'a list"
    apply standard
     apply auto
    using a1 apply blast
    using M1M2_comp.M1.computes_wordD(2) a1 by auto
  have 2: "M1M2_comp.M1.wf_input w" for w :: "'a list"
    using a3 by blast
  have 3: "M1M2_comp.M2.wf_input w" for w :: "'a list"
    using a6 by blast
  have 4: "M1M2_comp.M2.halts w" for w :: "'a list"
    using a5 by blast
  note 5 = IO_TM_comp.io_comp_run' [OF M1M2_comp.IO_TM_comp_axioms 1 2 3 4]
  have 6: "M1M2_comp.\<Sigma> = UNIV"
    using M1M2_comp.M2.M'_fields(2) M1M2_comp.M_fields(2) a6 by argo
  have 7: "M1M2_comp.M1.time w \<le> T1 (length w)" for w :: "'a list"
    using a2 by fast
  have 8: "M1M2_comp.is_final (M1M2_comp.run (M1M2_comp.M1.time w +
           T2 (length (f w))) w)"
    for w :: "'a list" unfolding 5 using a5
    by (metis M1M2_comp.M2.M'_fields(5) M1M2_comp.is_final_cr
        M1M2_comp.simple_TM_comp_axioms TM.time_bounded_wordD TM_config.sel(1) is_finalD
        is_finalI simple_TM_comp.cr_simps(1))
  have 9: "M1M2_comp.is_final (M1M2_comp.run (T1 (length w) +
            max_Tf T2 f (length w)) w)" for w :: "'a list"
    using 7
    by (meson 8 M1M2_comp.final_mono_run add_mono_thms_linordered_semiring(1) max_Tf_ge)
  have 10: "M1M2_comp.time_bounded (\<lambda>n. T1 n + max_Tf T2 f n)" using 9 by fast
  have 11: "M1M2_comp.computes (g \<circ> f)"
    using a1 a4 unfolding TM.computes_def TM.computes_word_def
    using 9 apply auto
     apply blast
  proof
    fix w :: "'a list"
    assume a1: "\<forall>w. M1M2_comp.M1.halts w \<and> M1M2_comp.M1.M'.has_output
                (M1M2_comp.M1.steps (M1M2_comp.M1.config_time (M1M2_comp.M1.c\<^sub>0 w))
                (M1M2_comp.M1.c\<^sub>0 w)) (f w)" and
           a2: "\<forall>w. M1M2_comp.M2.halts w \<and> M1M2_comp.M2.M'.has_output
                (M1M2_comp.M2.steps (M1M2_comp.M2.config_time (M1M2_comp.M2.c\<^sub>0 w))
                (M1M2_comp.M2.c\<^sub>0 w)) (g w)"
    have 1: "M1M2_comp.config_time (M1M2_comp.c\<^sub>0 w) \<le> M1M2_comp.M1.time w +
             T2 (length (f w))"
      using 8 M1M2_comp.time_def M1M2_comp.time_leI by presburger
    have 2: "M1M2_comp.steps (M1M2_comp.config_time (M1M2_comp.c\<^sub>0 w)) (M1M2_comp.c\<^sub>0 w) =
             M1M2_comp.steps (M1M2_comp.M1.time w +
             T2 (length (f w))) (M1M2_comp.c\<^sub>0 w)" using 1
      by (metis 8 M1M2_comp.final_run_compute TM.compute_altdef TM.run_def TM.time_def)
    show "last (tapes (M1M2_comp.steps (M1M2_comp.config_time (M1M2_comp.c\<^sub>0 w))
          (M1M2_comp.c\<^sub>0 w))) = <g (f w)>\<^sub>t\<^sub>p" unfolding 2 5 [unfolded TM.run_def] apply simp
      by (metis M1M2_comp.M2.at_least_one_tape M1M2_comp.M2.has_outputD
          M1M2_comp.M2.time_bounded_wordD TM.run_def TM.run_tapes_len TM.steps_conf_time
          a2 a5 last_appendR list.size(3) neq0_conv)
  qed
  have "typed_computable_in_time TYPE('q1+'q2) TYPE('l2)
        (\<lambda>n. max_Tf T2 f n + T1 n) (g \<circ> f)"
    unfolding typed_computable_in_time_def
    apply (rule exI [where x="M1M2_comp.M"])
    using 6 10 11 apply auto
    apply (subst add.commute)
    by simp
  thus "computable_in_time (\<lambda>n. max_Tf T2 f n + T1 n) (g \<circ> f)"
    by (rule typed_comp_in_time_natI)
qed

lemma append_computable: "typed_computable_in_time TYPE('q1) TYPE('l1) T1 f \<Longrightarrow>
                          typed_computable_in_time TYPE('q2) TYPE('l2) T2 g \<Longrightarrow>
                          computable_in_time (\<lambda>n. T1 n + T2 n + 2 * n + 3 + 2 * max_Tf id f n +
                          max_Tf id g n) (\<lambda>w. f w @ g w)"
proof (rule typed_comp_in_time_natI, unfold typed_computable_in_time_def, auto)
  fix Mf :: "('q1, 'a, 'l1) TM" and Mg :: "('q2, 'a, 'l2) TM"
  assume a1: "TM.computes Mf f" and a2: "TM.computes Mg g" and a3: "TM.time_bounded Mf T1" and
         a4 [simp]: "TM.TM.symbols Mf = UNIV" and a5: "TM.time_bounded Mg T2" and
         a6 [simp]: "TM.TM.symbols Mg = UNIV"
  define tc :: nat where "tc \<equiv> TM.tape_count Mf + TM.tape_count Mg + 1"
  have UNIV_finite: "finite (UNIV :: 'a set)" by (simp flip: a4)
  have *: "Suc 0 \<le> tc - Suc 0 \<and> Suc (TM.TM.tape_count Mf) \<le> tc - Suc 0" unfolding tc_def
    using less_eq_Suc_le by auto
  have **: "0 < tc" unfolding tc_def by simp
  obtain Mr :: "(nat, 'a, unit) TM" where Mr_syms [simp]: "TM.symbols Mr = UNIV" and
    Mr_tc [simp]: "TM.tape_count Mr = tc" and
    Mr_t1: "\<And>w. tapes (TM.compute Mr w) ! 1 = TM_abbrevs.input_tape w" and
    Mr_t2: "\<And>w. tapes (TM.compute Mr w) ! (Suc (TM.tape_count Mf)) = TM_abbrevs.input_tape w" and
    Mr_tr: "\<And>w i. i < TM.tape_count Mr \<Longrightarrow> i > 1 \<Longrightarrow> i \<noteq> Suc (TM.tape_count Mf) \<Longrightarrow>
            tapes (TM.compute Mr w) ! i = Tape [] None []"
    using replicate_input_on_tapes [of UNIV "{1, Suc (TM.tape_count Mf)}" tc,
        OF UNIV_finite, simplified, OF * **] by fastforce
  define M :: "(nat \<times> 'a option \<times> nat \<times> 'q1 \<times> 'q2, 'a, unit) TM_record" where
    "M \<equiv> TM tc UNIV ({0..10} \<times> UNIV \<times> (TM.states Mr) \<times> (TM.states Mf) \<times> (TM.states Mg))
     (0, None, TM.initial_state Mr, TM.initial_state Mf, TM.initial_state Mg)
     ({10} \<times> UNIV \<times> (TM.final_states Mr) \<times> (TM.final_states Mf) \<times> (TM.final_states Mg))
     (\<lambda>_. ()) undefined undefined undefined"
  show "\<exists>M::(nat \<times> 'a option \<times> nat \<times> 'q1 \<times> 'q2, 'a, unit) TM. TM.computes M (\<lambda>w. f w @ g w) \<and>
        (\<forall>w. TM.time_bounded_word M
        (\<lambda>n. T1 n + T2 n + 2 * n + 3 + 2 * max_Tf id f n + max_Tf id g n) w) \<and>
        TM.TM.symbols M = UNIV"
  proof (rule exI [where x="Abs_TM M"], unfold TM.computes_def, auto)
    fix w :: "'a list"
    show syms: "\<And>s. s \<in> TM.TM.symbols (Abs_TM M)" sorry
    show tb: "TM.time_bounded_word (Abs_TM M)
              (\<lambda>n. T1 n + T2 n + 2 * n + 3 + 2 * max_Tf id f n + max_Tf id g n) w" sorry
    show "TM.computes_word (Abs_TM M) w (f w @ g w)" sorry
  qed
qed

(* The theoretical optimum would probably be around 2 * n + 2 * length suff (if suff \<noteq> []),
   so this is very good and usable considering that conceptually it is quite inefficient
   (via rev twice and prefix). *)
lemma append_suffix_computable:
  "computable_in_time (\<lambda>n. 2 * n + 2 * length suff + 3) (\<lambda>w. w @ (suff::('a::finite) list))"
proof -
  have 1: "\<And>w. w @ suff = rev ((rev suff) @ (rev w))" by simp
  have 2: "(\<lambda>w. w @ suff) = rev \<circ> (((@) (rev suff)) \<circ> rev)" unfolding 1 comp_def ..
  note 3 = rev_computable
  note 4 = add_const_prefix_computable [of "rev suff"]
  note 5 = computable_in_time_compI [OF 3 4]
  note 6 = computable_in_time_compI [OF 5 3, folded 2]
  have 7: "\<And>n. {t. \<exists>w::'a list. length w = n \<and> Suc (length suff + length w) = t} = {Suc (length suff + n)}"
    using Ex_list_of_length by auto
  have 8: "\<And>n. {t. Suc (length suff) = t \<and> (\<exists>w. length w = n)} = {Suc (length suff)}"
    using Ex_list_of_length by auto
  note 6 [unfolded max_Tf_def, simplified, unfolded 7 8, simplified]
  thus "computable_in_time (\<lambda>n. 2 * n + 2 * length suff + 3) (\<lambda>w. w @ (suff::('a::finite) list))"
    by (metis (no_types, lifting) ext add.commute add_2_eq_Suc' add_Suc_right distrib_left
        mult.commute mult_2_right numeral_2_eq_2 numeral_3_eq_3)
qed

lemma rev_take_computable: "computable_in_time (\<lambda>_. n + 1) (rev \<circ> (take n)::('s::finite) list \<Rightarrow> 's list)"
proof (rule typed_comp_in_time_natI)
  define M :: "(nat \<times> 's option, 's, unit) TM_record" where
    "M \<equiv> TM 2 (UNIV::'s set) ({0..Suc n} \<times> UNIV) (0, None) ({Suc n} \<times> UNIV) (\<lambda>_. ())
         (\<lambda>st hds. if hds ! 0 = None \<or> fst st = Suc n then (Suc n, snd st) else (Suc (fst st), hds ! 0))
         (\<lambda>st hds k. if fst st = 0 then hds ! k else snd st)
         (\<lambda>st hds k. if k = 0 then Shift_Right else if fst st = 0 \<or> fst st \<ge> n \<or> hds ! 0 = None then No_Shift else
           Shift_Left)"
  have valid_M [simp, intro]: "valid_TM M"
    apply standard
    unfolding M_def by auto
  have "typed_computable_in_time TYPE(nat \<times> 's option) TYPE(unit) (\<lambda>_. n + 1)
        (rev \<circ> (take n)::('s::finite) list \<Rightarrow> 's list)" if n_gt_0: "n > 0"
  proof (unfold typed_computable_in_time_def, rule exI [where x="Abs_TM M"], auto)
    show "\<And>s. s \<in> TM.TM.symbols (Abs_TM M)" unfolding valid_tm_symbols [OF valid_M] unfolding M_def by simp
    have f11: "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (1, Some (hd w))" and
         f12: "tl w = [] \<Longrightarrow> heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = None" and
         f13: "tl w \<noteq> [] \<Longrightarrow> heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! 1)" and
         f14: "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) = map Some (drop 2 w)" and
         f15: "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
         if "w \<noteq> []" for w :: "'s list"
    proof -
      have [simp]: "state (TM.initial_config (Abs_TM M) w) \<notin> TM.TM.final_states (Abs_TM M)"
        unfolding TM.initial_config_def valid_tm_final_states [OF valid_M] apply simp
        unfolding valid_tm_initial_state [OF valid_M] unfolding M_def by simp
      show "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (1, Some (hd w))"
        unfolding TM.step_def apply auto
        unfolding valid_tm_next_state [OF valid_M] TM.initial_config_def TM_abbrevs.input_tape_def
        using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M] unfolding M_def by simp
      show "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = None" if "tl w = []"
        unfolding TM.step_def apply auto
        apply (subst nth_map)
         apply auto
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
          apply (metis TM.at_least_one_tape less_numeral_extra(3))
         apply (metis TM.at_least_one_tape TM.init_conf_len less_not_refl list.size(3))
        apply (subst nth_zip)
          apply auto
         apply (metis TM.init_conf_len less_numeral_extra(3) list.size(3) valid_M valid_TM_def valid_tm_tape_count)
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] TM.initial_config_def apply simp
        unfolding valid_tm_tape_count [OF valid_M] valid_tm_initial_state [OF valid_M] TM_abbrevs.input_tape_def
        using that apply (auto simp add: M_def)
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def by simp_all
      show "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! 1)"
        if "tl w \<noteq> []"
        unfolding TM.step_def apply auto
        apply (subst nth_map)
         apply auto
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
          apply (metis TM.at_least_one_tape less_numeral_extra(3))
         apply (metis TM.at_least_one_tape TM.init_conf_len less_not_refl list.size(3))
        apply (subst nth_zip)
          apply auto
         apply (metis TM.init_conf_len less_numeral_extra(3) list.size(3) valid_M valid_TM_def valid_tm_tape_count)
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] TM.initial_config_def apply simp
        unfolding valid_tm_tape_count [OF valid_M] valid_tm_initial_state [OF valid_M] TM_abbrevs.input_tape_def
        using that apply (auto simp add: M_def)
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply simp
        apply (subst Shift_Right_is_right_not_empty)
         apply auto
        by (metis zeroth_is_head length_greater_0_conv hd_map nth_tl)
      show "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) = map Some (drop 2 w)"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
          apply auto
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
          apply (metis TM.at_least_one_tape less_numeral_extra(3))
         apply (metis TM.at_least_one_tape TM.init_conf_len linorder_not_less list.size(3) zero_le)
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] TM.initial_config_def
          TM_abbrevs.input_tape_def using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply simp
        by (simp add: drop_Suc map_tl numeral_2_eq_2)
      show "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (metis (no_types, lifting) M_def TM.init_conf_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply (subst nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] TM.initial_config_def apply simp
        unfolding TM_abbrevs.input_tape_def valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M]
        using that apply auto
        unfolding M_def apply simp
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply simp
        unfolding TM_abbrevs.tape_shift.simps ..
    qed
    have f11': "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (Suc n, None)" and
         f12': "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1 = Tape [] None []"
    proof -
      have [simp]: "state (TM.initial_config (Abs_TM M) []) \<notin> TM.TM.final_states (Abs_TM M)"
        unfolding TM.initial_config_def valid_tm_final_states [OF valid_M] apply simp
        unfolding valid_tm_initial_state [OF valid_M] unfolding M_def by simp
      show "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (Suc n, None)"
        unfolding TM.step_def apply auto
        unfolding valid_tm_next_state [OF valid_M] TM.initial_config_def TM_abbrevs.input_tape_def apply simp
        unfolding valid_tm_tape_count [OF valid_M] valid_tm_initial_state [OF valid_M] unfolding M_def by simp
      show "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1 = Tape [] None []"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (metis (no_types, lifting) M_def TM.init_conf_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] TM.initial_config_def
          TM_abbrevs.input_tape_def apply auto
        unfolding valid_tm_tape_count [OF valid_M] valid_tm_initial_state [OF valid_M] unfolding M_def apply simp
        unfolding TM_abbrevs.tape_write_def TM_abbrevs.tape_shift.simps by simp
    qed
    have f21: "state (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) = (k, Some (w ! (k - 1)))" and
         f22: "k < length w \<Longrightarrow> heads (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0 =
               Some (w ! k)" and
         f23: "k = length w \<Longrightarrow> heads (TM.steps (Abs_TM M) (length w) (TM.initial_config (Abs_TM M) w)) ! 0 =
               None" and
         f24: "right (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop (Suc k) w)" and
         f25: "tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None (map Some (rev (take (k - 1) w)))"
         if "k \<ge> 1" and "k \<le> length w" and "k \<le> n" for k :: nat and w :: "'s list" using that
    proof (induction k rule: nat_induct_at_least)
      case base
      {
        case 1
        then show ?case using f11 [of w] apply simp
          by (metis zeroth_is_head)
      next
        case 2
        then show ?case apply simp
          apply (subst f13 [of w])
            apply auto
          by (metis less_Suc0 Nitpick.size_list_simp(2) bot_nat_0.not_eq_extremum)
      next
        case 3
        then show ?case apply simp
          apply (erule subst)
          apply simp
          apply (rule f12 [of w])
          using 3 apply auto
          by (metis Nitpick.size_list_simp(2) length_greater_0_conv less_Suc0 old.nat.inject)
      next
        case 4
        then show ?case using f14 [of w] by (simp add: numeral_2_eq_2)
      next
        case 5
        then show ?case using f15 [of w] by simp
      }
    next
      case (Suc k)
      {
        case 1
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M] unfolding M_def apply simp
          using ** by simp
          show ?case apply simp
            apply (subst TM.step_def)
            apply auto
            unfolding Suc(2) [OF * **] valid_tm_next_state [OF valid_M] apply (subst M_def)
            apply auto
            using ** apply auto
            unfolding Suc(3) [OF *** * **] by simp_all
      next
        case 2
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M] unfolding M_def apply simp
          using ** by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply auto
            apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
           apply (metis TM.run_tapes_len less_numeral_extra(3) list.size(3) valid_M valid_TM_def
              valid_tm_tape_count)
          apply (subst nth_zip)
            apply auto
            apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
           apply (metis One_nat_def Suc_diff_Suc TM.at_least_one_tape TM.run_tapes_len length_tl
              list.sel(2) minus_nat.diff_0 n_not_Suc_n)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding Suc(2) [OF * **] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          apply (subst M_def)
          apply auto
          apply (subst M_def)
          using Suc(1) apply auto
          unfolding TM_abbrevs.tape_write_def apply (subst Shift_Right_is_right_not_empty)
          apply auto
          using ** "2.prems"(1) Suc.IH(4) apply force
          unfolding Suc(5) [OF * **]
          by (metis "2.prems"(1) Cons_nth_drop_Suc hd_drop_conv_nth list.distinct(1) list.map_sel(1))
      next
        case 3
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have 0: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                 TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M] unfolding M_def apply simp
          using ** by simp
        have 1: "length w = Suc (length w - 1)" using *** by simp
        have 2: "k = length w - 1" using 3(1) by simp
        show ?case apply (subst 1)
          apply simp
          apply (subst TM.step_def)
          apply auto
          using 0 *** apply (metis "3.prems"(1) diff_Suc_1')
          apply (subst nth_map)
           apply auto
            apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
           apply (metis Suc_diff_1 TM.at_least_one_tape TM.run_tapes_len length_tl list.sel(2) n_not_Suc_n)
          apply (subst nth_zip)
            apply auto
            apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
           apply (metis Suc_diff_1 TM.at_least_one_tape TM.run_tapes_len length_tl list.sel(2) n_not_Suc_n)
          unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding Suc(2) [OF * **, unfolded 2, simplified] valid_tm_next_move [OF valid_M]
            valid_tm_next_write [OF valid_M] apply (subst M_def)
          apply simp
          apply (subst M_def)
          apply auto
           apply (subst TM.initial_config_def)
          unfolding TM_abbrevs.input_tape_def using 3(1) apply auto
           apply (subst TM.initial_config_def)
          unfolding TM_abbrevs.input_tape_def apply auto
           apply (cases "map Some (tl w)")
            apply auto
          using Suc.hyps apply linarith
          unfolding TM_abbrevs.tape_write_def apply (subst Suc(5) [unfolded 2, simplified])
          using 3 apply linarith
          by simp
      next
        case 4
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M] unfolding M_def apply simp
          using ** by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply auto
            apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
           apply (metis TM.run_tapes_len less_numeral_extra(3) list.size(3) valid_M valid_TM_def
              valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply auto
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF * **]
          apply (subst M_def)
          apply simp
          unfolding Suc(5) [OF * **] by (metis drop_Suc tl_drop drop_map)
      next
        case 5
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M] unfolding M_def apply simp
          using ** by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
          apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
              valid_tm_tape_count)
           apply (metis (lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
            Suc(2) [OF * **] valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] apply simp
          apply (subst (1 2) nth_zip)
            apply auto
          using M_def valid_tm_tape_count apply fastforce
          using M_def valid_tm_tape_count apply fastforce
          apply (subst (1 2) nth_map)
           apply auto
          using M_def valid_tm_tape_count apply fastforce
          apply (subst M_def)
          using Suc(1) 5 apply auto
           apply (metis (no_types, lifting) M_def Suc_diff_Suc Suc_pred TM.at_least_one_tape
              length_upt lessI n_not_Suc_n nth_map nth_map_upto numeral_2_eq_2 simps(1)
              valid_M valid_tm_tape_count)
          apply (subst M_def)
          apply simp
          unfolding TM_abbrevs.tape_write_def Suc(6) [OF * **, simplified] apply simp
          unfolding TM_abbrevs.tape_shift.simps apply simp
          using Suc.IH(2) apply force
           apply (metis (lifting) M_def One_nat_def add.commute lessI n_not_Suc_n nth_upt
              numeral_2_eq_2 plus_1_eq_Suc simps(1) valid_M valid_tm_tape_count)
          apply (simp add: TM_abbrevs.tape_shift.simps)
          apply (subst M_def)
          apply simp
          by (metis * Suc_pred less_eq_Suc_le list.simps(9) list_take_rev_Cons)
      }
    qed
    have f31: "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
              (Suc n, Some (w ! (length w - 1)))" and
         f32: "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] (Some (last w)) (map Some (rev (butlast w)))"
         if "length w \<le> n" and "w \<noteq> []" for w :: "'s list"
    proof -
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" apply (subst f21)
        using that apply auto
        unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
            (Suc n, Some (w ! (length w - 1)))" apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding valid_tm_next_state [OF valid_M] apply (subst f21)
        using that apply auto
        apply (subst M_def)
        apply auto
         apply (subst (asm) f23 [where k="length w"])
        using that apply auto
        apply (subst (asm) f23 [where k="length w"])
        by simp_all
      show "tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
            Tape [] (Some (last w)) (map Some (rev (butlast w)))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2
            simps(1) valid_M valid_tm_tape_count)
        apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (subst f21)
        using that apply auto
        apply (subst f25 [simplified])
           apply auto
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply force
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count apply fastforce
        apply (subst M_def)
        apply auto
        using M_def valid_tm_tape_count apply force
        unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
          apply simp
        unfolding TM_abbrevs.tape_write_def apply auto
           apply (simp add: last_conv_nth)
          apply (simp add: drop_Suc rev_butlast_is_tl_rev)
        using M_def valid_tm_tape_count apply force
           apply (subst M_def)
           apply simp
           apply (metis One_nat_def last_conv_nth)
          apply (metis One_nat_def drop_rev butlast_conv_take)
         apply (metis One_nat_def f23 le_refl length_Suc0_not_empty option.distinct(1))
        apply (subst (asm) f23 [where k="length w"])
        by simp_all
    qed
    have f31': "state (TM.steps (Abs_TM M) (Suc n) (TM.initial_config (Abs_TM M) w)) =
                (Suc n, Some (w ! n))" and
         f32': "tapes (TM.steps (Abs_TM M) (Suc n) (TM.initial_config (Abs_TM M) w)) ! 1 =
                Tape [] (Some (w ! (n - 1))) (map Some (rev (take (n - 1) w)))"
         if "length w > n" and "w \<noteq> []" for w :: "'s list"
    proof -
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" apply (subst f21)
        using that \<open>n > 0\<close> apply auto
        unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show "state ((TM.step (Abs_TM M) ^^ Suc n) (TM.initial_config (Abs_TM M) w)) =
            (Suc n, Some (w ! n))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding valid_tm_next_state [OF valid_M] apply (subst f21)
        using \<open>n > 0\<close> that apply auto
        apply (subst M_def)
        apply auto
         apply (subst (asm) f22)
             apply auto
        apply (subst (asm) f22)
        by auto
      show "tapes ((TM.step (Abs_TM M) ^^ Suc n) (TM.initial_config (Abs_TM M) w)) ! 1 =
            Tape [] (Some (w ! (n - 1))) (map Some (rev (take (n - 1) w)))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2
            simps(1) valid_M valid_tm_tape_count)
        apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f21)
        using that \<open>n > 0\<close> apply auto
        apply (subst M_def)
        apply auto
        using M_def valid_tm_tape_count apply force
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
         apply (subst f25 [simplified])
            apply auto
        apply (subst f25 [simplified])
        by simp_all
    qed
    show tb: "TM.time_bounded_word (Abs_TM M) (\<lambda>_. Suc n) w" for w :: "'s list"
    proof (cases "w = []")
      have 1: "TM.is_final (Abs_TM M) (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) []))"
        unfolding TM.is_final_def f11' valid_tm_final_states [OF valid_M] unfolding M_def by simp
      case True
      then show ?thesis apply simp
        apply (rule TM.time_bounded_word_mono [where t="\<lambda>_. 1"])
         apply auto
        unfolding TM.time_bounded_word_def TM.run_def using 1 by simp
    next
      case False
      show ?thesis
      proof (cases "length w \<le> n")
        case True
        show ?thesis apply (rule TM.time_bounded_word_mono [where t="\<lambda>n. Suc n"])
           using True apply auto
           unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def apply (subst f31)
           using False apply auto
           unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      next
        case False
        hence 1: "n < length w" by simp
        show ?thesis unfolding TM.time_bounded_word_def TM.run_def TM.is_final_def apply (subst f31')
            apply fact+
          unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      qed
    qed
    show "TM.computes (Abs_TM M) (rev \<circ> (take n)::('s::finite) list \<Rightarrow> 's list)"
      unfolding TM.computes_def
    proof
      fix w :: "'s list"
      show "TM.computes_word (Abs_TM M) w ((rev \<circ> take n) w)"
      proof (cases "w = []")
        have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                 (TM.initial_config (Abs_TM M) []))) = 1"
          apply (rule Least_natI)
           apply auto
          unfolding TM.is_final_def f11' valid_tm_final_states [OF valid_M] apply (subst M_def)
           apply simp
          unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M] unfolding M_def by simp
        case True
        then show ?thesis apply simp
          unfolding TM.computes_word_def apply auto
          using tb [of "[]"] TM.time_bounded_altdef2 tb apply blast
          unfolding TM.has_output_def TM.clean_output_of_def TM.compute_def TM.compute_config_def apply auto
          unfolding 1 apply auto
          unfolding TM.clean_output_def TM.output_of_def Let_def apply auto
        proof -
          have "length (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) []))) = 2"
            by (metis (lifting) M_def TM.init_conf_len TM.step_l_tps simps(1) valid_M valid_tm_tape_count)
          hence 2: "last (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) []))) =
                    tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1"
            by (metis One_nat_def Suc_pred Zero_not_Suc last_conv_nth list.size(3) nat.inject numeral_2_eq_2
                zero_less_Suc)
          show "\<exists>w. last (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) []))) =
                TM_abbrevs.input_tape w"
            unfolding 2 f12' TM_abbrevs.input_tape_def apply (rule exI [where x="[]"])
            by simp
          fix w' :: "'s list"
          assume a1: "last (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) []))) =
                      TM_abbrevs.input_tape w'"
          note a1 [unfolded 2 f12' TM_abbrevs.input_tape_def]
          hence 3: "w' = []" using TM_abbrevs.input_tape_cong by fastforce
          show "(case head (TM_abbrevs.input_tape w') of None \<Rightarrow> [] | Some h \<Rightarrow> h # the (those
                (takeWhile (\<lambda>s. s \<noteq> None) (right (last (tapes (TM.step (Abs_TM M)
                (TM.initial_config (Abs_TM M) [])))))))) = []" unfolding 3 TM_abbrevs.input_tape_def
            by simp
        qed
      next
        case False
        have "length (tapes (TM.compute (Abs_TM M) w)) = 2"
          by (metis (no_types, lifting) M_def TM.compute_altdef TM.run_def TM.run_tapes_len simps(1) valid_M
              valid_tm_tape_count)
        hence *: "last (tapes (TM.compute (Abs_TM M) w)) = tapes (TM.compute (Abs_TM M) w) ! 1"
          by (metis One_nat_def Zero_not_Suc diff_Suc_Suc last_conv_nth list.size(3)
              minus_nat.diff_0 numeral_2_eq_2)
        have **: "length w \<le> n \<Longrightarrow> (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                  (TM.initial_config (Abs_TM M) w))) = Suc (length w)"
          apply (rule Least_nat_monoI)
          unfolding TM.is_final_def apply (subst f31)
              apply assumption
             apply (rule False)
            apply (subst valid_tm_final_states)
             apply auto
            apply (subst M_def)
            apply simp
           apply (subst (asm) f21 [OF _ Nat.le_refl, of w])
          using False apply simp
            apply assumption
          apply (subst (asm) valid_tm_final_states [OF valid_M])
           apply (subst (asm) M_def)
           apply simp
          by (simp add: TM.step_def)
        have ***: "\<not>length w \<le> n \<Longrightarrow> (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                   (TM.initial_config (Abs_TM M) w))) = Suc n"
          apply (rule Least_nat_monoI)
            apply (subst TM.is_final_def)
            apply (subst f31')
          using False apply auto
          unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
           apply simp
          unfolding TM.is_final_def apply (subst (asm) f21)
          using \<open>n > 0\<close> apply auto
          unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
        have 1: "length w \<le> n \<Longrightarrow> head (last (tapes (TM.compute (Abs_TM M) w))) = Some (last w)"
          unfolding * unfolding TM.compute_def TM.compute_config_def ** apply (subst f32)
          using False by simp_all
        have 2: "\<not>length w \<le> n \<Longrightarrow> head (last (tapes (TM.compute (Abs_TM M) w))) = Some (w ! (n - 1))"
          unfolding * unfolding TM.compute_def TM.compute_config_def *** apply (subst f32')
          using False by simp_all
        have 3: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some w) = map Some w" for w :: "'s list" by simp
        show ?thesis unfolding TM.computes_word_def apply auto
          using tb [of w] unfolding TM.halts_def TM.halts_config_def TM.time_bounded_word_def TM.run_def
           apply (rule exI)
          unfolding TM.has_output_def TM.clean_output_of_def apply auto
          unfolding TM.clean_output_def TM.output_of_def Let_def apply (cases "length w \<le> n")
          unfolding 1 apply auto
            apply (subst TM_abbrevs.input_tape_def)
          apply auto
             apply (metis 1 TM_abbrevs.input_tape_empty_hd_iff option.distinct(1))
          unfolding 3 apply simp
          unfolding * unfolding TM.compute_def TM.compute_config_def ** apply (subst (asm) f32)
          using False apply auto
            apply (metis TM_abbrevs.input_tape.simps(2) TM_abbrevs.input_tape_inj hd_rev list.collapse
              rev_butlast_is_tl_rev rev_is_Nil_conv)
          unfolding *** apply (subst (asm) f32' [unfolded One_nat_def])
             apply auto
          unfolding TM_abbrevs.input_tape_def apply simp
        proof (rule conjI, rule impI)
          fix w' :: "'s list"
          assume a1: "Tape [] (Some (w ! (n - Suc 0))) (map Some (rev (take (n - Suc 0) w))) =
                     (if w' = [] then Tape [] None [] else Tape [] (Some (hd w')) (map Some (tl w')))" and
                 a2: "w' = []"
          thus "n = 0" using a1 a2 by simp
        next
          fix w' :: "'s list"
          assume a1: "\<not> length w \<le> n" and
                 a2: "Tape [] (Some (w ! (n - Suc 0))) (map Some (rev (take (n - Suc 0) w))) =
                     (if w' = [] then Tape [] None [] else Tape [] (Some (hd w')) (map Some (tl w')))"
          have 1: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some (rev (take (n - Suc 0) w))) =
                   map Some (rev (take (n - Suc 0) w))" by simp
          have 2: "hd w' = w ! (n - Suc 0)" using a2 by (metis option.distinct(1) option.inject tape.inject)
          show "w' \<noteq> [] \<longrightarrow> hd w' # the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y)
                (right (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                (TM.initial_config (Abs_TM M) w))) ! Suc 0)))) = rev (take n w)" apply auto
            apply (subst f32' [simplified])
            using a1 apply auto
            unfolding 1 apply simp
            using \<open>n > 0\<close> unfolding 2 by (simp add: list_take_rev_Cons)
        next
          assume a1: "w \<noteq> []"
          show "\<exists>wa. tapes ((TM.step (Abs_TM M) ^^ (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                (TM.initial_config (Abs_TM M) w)))) (TM.initial_config (Abs_TM M) w)) ! Suc 0 =
                (if wa = [] then Tape [] None [] else Tape [] (Some (hd wa)) (map Some (tl wa)))"
          proof (cases "length w \<le> n")
            case True
            show ?thesis unfolding ** [OF True] f32 [OF True a1, unfolded One_nat_def]
              apply (rule exI [where x="rev w"])
              apply auto
              using a1 apply simp
               apply (metis hd_rev)
              using rev_butlast_is_tl_rev by blast
          next
            case False
            show ?thesis unfolding *** [OF False] apply (subst f32' [unfolded One_nat_def])
              using False apply simp
               apply (rule a1)
              apply (rule exI [where x="rev (take n w)"])
              apply auto
                 apply fact
              using a1 apply simp
               apply (metis False Suc_pred less_eq_Suc_le list.sel(1) list_take_rev_Cons nat_le_linear)
              by (metis False One_nat_def butlast_take nat_le_linear rev_butlast_is_tl_rev)
          qed
        qed
      qed
    qed
  qed
  moreover have "typed_computable_in_time TYPE(nat \<times> 's option) TYPE(unit) (\<lambda>_. 1)
                 (rev \<circ> (take 0)::('s::finite) list \<Rightarrow> 's list)"
    apply (simp add: comp_def)
    apply (rule computable_mono [where t="\<lambda>_. 0"])
     apply auto
  proof (unfold typed_computable_in_time_def)
    define M :: "(nat \<times> 's option, 's, unit) TM_record" where
      "M \<equiv> TM 2 UNIV {(undefined, undefined)} (undefined, undefined) {(undefined, undefined)} (\<lambda>_. ())
           (\<lambda>st _. st)
           (\<lambda>_ hds _. hds ! 1)
           (\<lambda>_ _ _. No_Shift)"
    have valid_M: "valid_TM M"
      apply standard
      unfolding M_def by auto
    have syms: "TM.TM.symbols (Abs_TM M) = UNIV" unfolding valid_tm_symbols [OF valid_M]
      unfolding M_def by simp
    have tb: "TM.time_bounded_word (Abs_TM M) (\<lambda>_. 0) w" for w :: "'s list"
      unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def valid_tm_final_states [OF valid_M]
      apply simp
      unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M] apply simp
      unfolding M_def by simp
    have 1: "\<And>w. (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
             (TM.initial_config (Abs_TM M) w))) = 0"
      apply (rule Least_natI)
       apply auto
      using tb unfolding TM.time_bounded_word_def TM.run_def by simp
    have comp: "TM.computes (Abs_TM M) (\<lambda>_. [])"
      unfolding TM.computes_def TM.computes_word_def apply auto
      using tb TM.time_bounded_altdef2 apply blast
      unfolding TM.compute_def TM.compute_config_def 1 apply simp
      unfolding TM.initial_config_def TM_abbrevs.input_tape_def valid_tm_tape_count [OF valid_M]
        TM.has_output_def apply auto
      unfolding TM.clean_output_of_def apply auto
      unfolding TM.clean_output_def TM.output_of_def Let_def apply auto
      unfolding TM_abbrevs.input_tape_def apply auto
      unfolding M_def by simp
    show "\<exists>M::(nat \<times> 's option, 's, unit) TM. TM.computes M (\<lambda>_. []) \<and>
          (\<forall>w. TM.time_bounded_word M (\<lambda>_. 0) w) \<and> TM.TM.symbols M = UNIV" using syms tb comp by blast
  qed
  ultimately show "typed_computable_in_time TYPE(nat \<times> 's option) TYPE(unit) (\<lambda>_. n + 1)
                   (rev \<circ> take n::('s::finite) list \<Rightarrow> 's list)" by fastforce
qed

lemma take_computable: "computable_in_time (\<lambda>_. 2 * n + 2) ((take n)::('s::finite) list \<Rightarrow> 's list)"
proof -
  have 1: "((take n)::('s::finite) list \<Rightarrow> 's list) = rev \<circ> (rev \<circ> (take n))" unfolding comp_def by simp
  note 2 = rev_take_computable [of n, where 's='s]
  note 3 = rev_computable [where 'a='s]
  have 4: "\<And>m n. {t. \<exists>w::'s list. length w = m \<and> Suc (min (length w) n) = t} = {Suc (min n m)}" apply auto
    by (metis Ex_list_of_length min.commute)
  note 5 = computable_in_time_compI [OF 2 3, folded 1, unfolded max_Tf_def, simplified, unfolded 4, simplified]
  note computable_mono [OF 5, of "(\<lambda>_. 2 * n + 2)", simplified]
  thus "computable_in_time (\<lambda>_. 2 * n + 2) ((take n)::('s::finite) list \<Rightarrow> 's list)" by simp
qed

lemma rev_drop_computable: "computable_in_time (\<lambda>n. n + 1) (rev \<circ> (drop n)::('s::finite) list \<Rightarrow> 's list)"
proof -
  define M :: "(nat \<times> 's option, 's, unit) TM_record" where
    "M \<equiv> TM 2 UNIV ({0..Suc (Suc n)} \<times> UNIV) (0, None) ({Suc (Suc n)} \<times> UNIV) (\<lambda>_. ())
         (\<lambda>st hds. if hds ! 0 = None then (Suc (Suc n), snd st) else
          if fst st < n then (Suc (fst st), None) else if fst st = n then (Suc n, hds ! 0) else (Suc n, hds ! 0))
         (\<lambda>st _ _. snd st)
         (\<lambda>st hds k. if k = 0 then Shift_Right else if fst st \<le> n \<or> hds ! 0 = None then No_Shift else
          Shift_Left)"
  have valid_M [simp, intro]: "valid_TM M"
    apply standard
    unfolding M_def by auto
  show "computable_in_time (\<lambda>n. n + 1) (rev \<circ> (drop n)::('s::finite) list \<Rightarrow> 's list)"
    apply (cases "n > 0")
     apply (rule typed_comp_in_time_natI)
    apply (subst typed_computable_in_time_def)
  proof (rule exI, auto)
    assume a1: "n > 0"
    show syms: "\<And>s. s \<in> TM.TM.symbols (Abs_TM M)"
      unfolding valid_tm_symbols [OF valid_M] unfolding M_def by simp
    have f11: "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (1, None)" and
         f12: "tl w \<noteq> [] \<Longrightarrow> heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) =
               [Some (w ! 1), None]" and
         f13: "tl w = [] \<Longrightarrow> heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) =
               [None, None]" and
         f14: "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop 2 w)" and
         f15: "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
         if "w \<noteq> []" for w :: "'s list"
    proof -
      have [simp]: "state (TM.initial_config (Abs_TM M) w) \<notin> TM.TM.final_states (Abs_TM M)"
        unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M]
          valid_tm_final_states [OF valid_M] apply simp
        unfolding M_def by simp
      show "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (1, None)"
        unfolding TM.step_def apply auto
        unfolding valid_tm_next_state [OF valid_M] TM.initial_config_def TM_abbrevs.input_tape_def
        using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M]
        unfolding M_def by (simp add: a1)
      show "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = [Some (w ! 1), None]"
        if "tl w \<noteq> []"
        unfolding TM.step_def apply auto
        apply (rule nth_equalityI)
         apply auto
         apply (metis (no_types, lifting) M_def TM.init_conf_len TM.next_actions_simps(2) min.idem
            numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply simp
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] TM.initial_config_def
          TM_abbrevs.input_tape_def using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M] unfolding M_def
        apply auto
        unfolding TM_abbrevs.tape_write_def apply auto
         apply (subst Shift_Right_is_right_not_empty)
          apply auto
         apply (metis list.map_sel(1) length_greater_0_conv hd_conv_nth nth_tl)
        unfolding TM_abbrevs.tape_shift.simps using a1 by simp_all
      show "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = [None, None]" if "tl w = []"
        unfolding TM.step_def apply auto
        apply (rule nth_equalityI)
         apply auto
         apply (metis (no_types, lifting) M_def TM.init_conf_len TM.next_actions_simps(2) min.idem
            numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
        apply simp
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          TM.initial_config_def TM_abbrevs.input_tape_def valid_tm_initial_state [OF valid_M]
        using \<open>w \<noteq> []\<close> apply auto
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def using a1 apply auto
        unfolding TM_abbrevs.tape_write_def that by (auto simp add: TM_abbrevs.tape_shift.simps)
      show "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) =
            map Some (drop 2 w)"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
          apply auto
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
         apply (metis TM.init_conf_len list.size(3) TM.at_least_one_tape less_not_refl)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply auto
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] TM.initial_config_def
          TM_abbrevs.input_tape_def using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M]
        unfolding M_def apply simp
        by (simp add: drop_Suc map_tl numeral_2_eq_2)
      show "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        using M_def valid_tm_tape_count apply force
        apply (metis (no_types, lifting) M_def TM.init_conf_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (subst nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply force
        using M_def valid_tm_tape_count apply force
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count apply force
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          valid_tm_tape_count [OF valid_M] TM.initial_config_def valid_tm_initial_state [OF valid_M] apply simp
        unfolding TM_abbrevs.input_tape_def using that apply auto
        unfolding M_def using a1 apply auto
        unfolding TM_abbrevs.tape_action_def by (simp add: TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def)
    qed
    have f11': "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (Suc (Suc n), None)" and
         f12': "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1 = Tape [] None []"
    proof -
      show "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (Suc (Suc n), None)"
        unfolding TM.step_def TM.initial_config_def valid_tm_initial_state [OF valid_M]
          valid_tm_tape_count [OF valid_M] TM.step_not_final_def valid_tm_next_state [OF valid_M] apply auto
        unfolding valid_tm_final_states [OF valid_M] apply (subst (asm) (1 2) M_def)
         apply simp
        unfolding Let_def apply simp
        unfolding M_def TM_abbrevs.input_tape_def by simp
      show "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1 = Tape [] None []"
        unfolding TM.step_def apply auto
        unfolding TM.initial_config_def valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M]
         apply auto
        unfolding valid_tm_tape_count [OF valid_M] apply (subst (asm) (1 2) M_def)
         apply simp
        apply (subst nth_map2)
        apply (metis (lifting) M_def TM.next_actions_simps(2) valid_tm_tape_count [OF valid_M] lessI
            numeral_2_eq_2 simps(1))
         apply (simp add: M_def)
        unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def TM.next_moves_def apply auto
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count [OF valid_M] apply simp
        using M_def valid_tm_tape_count [OF valid_M] apply simp
        apply (subst (1 2) nth_map)
        using M_def valid_tm_tape_count [OF valid_M] apply simp
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 5) M_def)
        apply auto
        unfolding valid_tm_tape_count [OF valid_M] apply (simp add: M_def)+
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
        by (simp_all add: M_def)
    qed
    have f21: "state (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) = (k, None)" and
         f22: "k < length w \<Longrightarrow> heads (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0 =
               Some (w ! k)" and
         f23: "k = length w \<Longrightarrow> heads (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0 =
               None" and
         f24: "right (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop (Suc k) w)" and
         f25: "tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None []"
         if "k \<ge> 1" and "k \<le> length w" and "k \<le> n" for w :: "'s list" and k :: nat using that
    proof (induction k rule: nat_induct_at_least)
      case base
      {
        case 1
        then show ?case apply simp unfolding f11 by simp
      next
        case 2
        then show ?case apply simp apply (subst f12)
            apply auto
          by (metis less_not_refl Nitpick.size_list_simp(2))
      next
        case 3
        then show ?case apply simp
          apply (erule subst)
          apply simp
          apply (subst f13)
          using 3 apply auto
          by (metis Nil_tl length_1_ex_iff)
      next
        case 4
        then show ?case apply simp
          unfolding f14 by (simp only: numeral_2_eq_2)
      next
        case 5
        then show ?case using f15 [of w] by simp
      }
    next
      case (Suc k)
      {
        case 1
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M]
          unfolding M_def using a1 ** by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          unfolding valid_tm_next_state [OF valid_M] Suc(2) [OF * **] apply (subst M_def)
          apply auto
          unfolding Suc(3) [OF *** * **] using 1 by simp_all
      next
        case 2
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M]
          unfolding M_def using a1 ** by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply auto
            apply (metis Suc_diff_1 TM.at_least_one_tape TM.next_actions_simps(2) length_1_ex_iff
              length_Cons length_upt list.distinct(1) list.sel(3))
           apply (metis TM.run_tapes_len less_numeral_extra(3) list.size(3) valid_M valid_TM_def
              valid_tm_tape_count)
          apply (subst nth_zip)
            apply auto
            apply (metis list.size(3) TM.next_actions_simps(2) less_not_refl TM.at_least_one_tape)
           apply (metis TM.run_tapes_len less_numeral_extra(3) list.size(3) valid_M valid_TM_def
              valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply simp
          unfolding Suc(2) [OF * **] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          apply (subst (1 4) M_def)
          apply simp
          unfolding TM_abbrevs.tape_write_def apply (subst Shift_Right_is_right_not_empty)
           apply auto
          using ** "2.prems"(1) Suc.IH(4) apply fastforce
          unfolding Suc(5) [OF * **]
          by (metis "2.prems"(1) drop_eq_Nil hd_drop_conv_nth le_antisym list.map_sel(1) nat_less_le)
      next
        case 3
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M]
          unfolding M_def using a1 ** by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply auto
            apply (metis list.size(3) TM.next_actions_simps(2) less_not_refl TM.at_least_one_tape)
           apply (metis list.size(3) less_not_refl TM.run_tapes_len TM.run_def TM.at_least_one_tape)
          apply (subst nth_zip)
            apply auto
            apply (metis list.size(3) TM.next_actions_simps(2) less_not_refl TM.at_least_one_tape)
           apply (metis list.size(3) TM.run_tapes_len less_not_refl TM.at_least_one_tape)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def apply (subst (1 2) nth_zip)
            apply auto
            apply (metis TM.next_writes_simps(2) lessI list.size(3) not_less_eq valid_M valid_TM_def
              valid_tm_tape_count)
           apply (metis TM.next_moves_simps(2) lessI list.size(3) not_less_eq valid_M valid_TM_def
              valid_tm_tape_count)
          unfolding TM.next_moves_def TM.next_writes_def apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF * **]
          apply (subst (1 4) M_def)
          apply simp
          unfolding TM_abbrevs.tape_write_def Suc(5) [OF * **] 3 by simp
      next
        case 4
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M]
          unfolding M_def using a1 ** by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply auto
            apply (metis One_nat_def TM.at_least_one_tape' TM.next_actions_simps(2) le_refl
              list.size(3) not_less_eq_eq)
           apply (metis TM.run_tapes_len le_refl linorder_not_less list.size(3) valid_M valid_TM_def
              valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF * **]
            Suc(3) [OF *** * **] apply (subst (1 2) M_def)
          apply simp
          unfolding Suc(5) [OF * **] by (metis drop_Suc tl_drop drop_map)
      next
        case 5
        hence *: "k \<le> length w" and **: "k \<le> n" and ***: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **] valid_tm_final_states [OF valid_M]
          unfolding M_def using a1 ** by simp
        have 1: "0 < k \<Longrightarrow> \<not> Suc 0 < k \<Longrightarrow> k = 1" by linarith
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2
              simps(1) valid_M valid_tm_tape_count)
          apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
              valid_tm_tape_count)
          unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply (subst nth_zip)
            apply auto
          using M_def valid_tm_tape_count apply fastforce
          using M_def valid_tm_tape_count apply fastforce
          apply (subst (1 2) nth_map)
          using M_def valid_tm_tape_count apply fastforce
          unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] Suc(2) [OF * **]
          apply (subst (1 5) M_def)
          using 5 apply auto
          unfolding valid_tm_tape_count [OF valid_M] apply (subst (asm) M_def)
           apply simp
          unfolding TM_abbrevs.tape_action_def apply simp
          unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
          using Suc(6) by simp_all
      }
    qed
    have f31: "state (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) = (Suc n, Some (w ! (k - 1)))" and
         f32: "k < length w \<Longrightarrow> heads (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0 =
               Some (w ! k)" and
         f33: "k = length w \<Longrightarrow> heads (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0 =
               None" and
         f34: "right (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop (Suc k) w)" and
         f35: "tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None (map Some (rev (take (k - Suc n) (drop n w))))"
         if "k \<ge> Suc n" and "k \<le> length w" for w :: "'s list" and k :: nat using that
    proof (induction k rule: nat_induct_at_least)
      case base
      {
        case 1
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          apply (subst f21)
          using a1 1 apply simp_all
          unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          unfolding valid_tm_next_state [OF valid_M] apply (subst f21)
          using a1 1 apply simp_all
          apply (subst M_def)
          apply auto
           apply (subst f22)
               apply auto
          apply (subst (asm) f22)
          by simp_all
      next
        case 2
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          apply (subst f21)
          using a1 2 apply simp_all
          unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply auto
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
           apply (metis (no_types, lifting) M_def TM.run_tapes_len list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
          apply (subst nth_zip)
            apply auto
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
           apply (metis (no_types, lifting) M_def TM.run_tapes_len list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f21)
          using a1 2 apply auto
          apply (subst (1 4) M_def)
          apply simp
          apply (subst Shift_Right_is_right_not_empty)
           apply auto
           apply (subst (asm) f24)
              apply auto
          apply (subst f24)
          apply auto
          by (metis diff_diff_cancel diff_zero hd_drop_conv_nth length_drop list.map_sel(1)
              list.size(3) nat_less_le)
      next
        case 3
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)" apply (subst f21)
          using a1 3 apply simp_all
          unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
        have 1: "\<And>i::nat. i < 2 \<Longrightarrow> i > 0 \<Longrightarrow> i = 1" by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply auto
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
           apply (metis (no_types, lifting) M_def TM.run_tapes_len list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
          apply (subst nth_zip)
            apply auto
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
           apply (metis (no_types, lifting) M_def TM.run_tapes_len list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f21)
          using a1 3 apply auto
          apply (subst (1 4) M_def)
          apply auto
          unfolding TM_abbrevs.tape_write_def apply (subst f24)
          by simp_all
      next
        case 4
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)" apply (subst f21)
          using a1 4 apply simp_all
          unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply auto
            apply (metis One_nat_def Suc_n_not_le_n TM.at_least_one_tape' TM.next_actions_simps(2) list.size(3))
           apply (metis TM.run_tapes_len bot_nat_0.not_eq_extremum list.size(3) valid_M valid_TM_def
              valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f21)
          using a1 4 apply auto
          apply (subst (1 4) M_def)
          apply auto
          apply (subst f24)
             apply auto
          by (metis drop_Suc drop_map tl_drop)
      next
        case 5
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)" apply (subst f21)
          using a1 5 apply simp_all
          unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
              valid_tm_tape_count)
          apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
              valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (subst (1 2) nth_zip)
            apply auto
          using M_def valid_tm_tape_count apply fastforce
          using M_def valid_tm_tape_count apply fastforce
          apply (subst (1 2) nth_map)
           apply auto
          using M_def valid_tm_tape_count apply fastforce
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f21)
          using a1 5 apply auto
          apply (subst (1 5) M_def)
          apply auto
           apply (metis (lifting) M_def One_nat_def add.commute lessI nat.distinct(1) nth_upt
              numeral_2_eq_2 plus_1_eq_Suc simps(1) valid_M valid_tm_tape_count)
          unfolding TM_abbrevs.tape_write_def TM_abbrevs.tape_shift.simps apply auto
           apply (subst f25 [simplified])
              apply auto
          apply (subst f25 [simplified])
          by auto
      }
    next
      case (Suc k)
      {
        case 1
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          unfolding valid_tm_next_state [OF valid_M] Suc(2) [OF *] apply (subst M_def)
          apply auto
          unfolding Suc(3) [OF ** *] by simp_all
      next
        case 2
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply auto
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
           apply (metis (no_types, lifting) M_def TM.run_tapes_len list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
          apply (subst nth_zip)
            apply auto
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
           apply (metis (no_types, lifting) M_def TM.run_tapes_len list.size(3) not_less_zero
              numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count zero_less_Suc)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
          apply (subst (1 4) M_def)
          apply simp
          apply (subst Shift_Right_is_right_not_empty)
           apply auto
          unfolding Suc(5) [OF *]
          using 2 apply auto
          by (simp add: hd_drop_conv_nth list.map_sel(1))
      next
        case 3
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply (simp add: M_def TM.next_actions_simps(2) TM.run_tapes_len)
          apply (subst nth_zip)
            apply (simp add: TM.next_actions_simps(2))
           apply (simp add: TM.run_tapes_len)
          unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding TM.next_writes_def TM.next_moves_def valid_tm_next_write [OF valid_M]
            valid_tm_next_move [OF valid_M] Suc(2) [OF *] apply (subst (1 4) M_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def apply simp
          unfolding TM_abbrevs.tape_write_def apply (subst Suc(5))
          using 3 by simp_all
      next
        case 4
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply (simp add: TM.next_actions_simps(2))
           apply (metis TM.run_tapes_len TM.at_least_one_tape)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def apply (subst (1 2) nth_zip)
            apply (simp add: TM.next_writes_simps(2))
           apply (simp add: TM.next_moves_simps(2))
          apply simp
          unfolding TM.next_moves_def TM.next_writes_def apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
          apply (subst (1 4) M_def)
          apply simp
          unfolding Suc(5) [OF *] by (metis drop_Suc tl_drop drop_map)
      next
        case 5
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2
              simps(1) valid_M valid_tm_tape_count)
          apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
              valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (subst (1 2) nth_zip)
            apply auto
          using M_def valid_tm_tape_count apply fastforce
          using M_def valid_tm_tape_count apply fastforce
          apply (subst (1 2) nth_map)
          using M_def valid_tm_tape_count apply fastforce
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
          apply (subst (1 5) M_def)
          using 5 apply (auto simp add: Suc(3) valid_tm_tape_count)
           apply (simp add: M_def)
          unfolding TM_abbrevs.tape_write_def Suc(6) [OF *, simplified] apply simp
          unfolding TM_abbrevs.tape_shift.simps apply simp
          apply (rule nth_equalityI)
           apply auto
          using Suc.hyps Suc_diff_Suc less_eq_Suc_le apply presburger
          apply (subst nth_map)
           apply auto
          using Suc.hyps apply force
          apply (subst nth_Cons)
        proof -
          fix i :: nat
          assume a1: "i < Suc (k - Suc n)"
          show "(case i of 0 \<Rightarrow> Some (w ! (k - Suc 0)) | Suc x \<Rightarrow>
                map Some (rev (take (k - Suc n) (drop n w))) ! x) =
                Some (rev (take (k - n) (drop n w)) ! i)" apply (cases i)
             apply auto
             apply (subst rev_nth)
            using * Suc.hyps apply auto
            apply (subst nth_map)
             apply auto
            using a1 apply force
            apply (subst (1 2) rev_nth)
              apply auto
              apply (metis a1 less_eq_Suc_le Suc_diff_Suc)
            using a1 apply force
            apply (subst nth_take)
             apply auto
            using a1 by auto
        qed
      }
    qed
    have f41: "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
               (Suc (Suc n), Some (w ! (length w - 1)))" and
         f42: "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] (Some (last (drop n w))) (map Some (rev (butlast (drop n w))))"
         if "n < length w" for w :: "'s list"
    proof -
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        apply (subst f31)
        using that apply auto
        unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
            (Suc (Suc n), Some (w ! (length w - 1)))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding valid_tm_next_state [OF valid_M] apply (subst f31)
        using that apply auto
        apply (subst M_def)
        apply auto
        apply (subst f33)
        by simp_all
      show "tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
            Tape [] (Some (last (drop n w))) (map Some (rev (butlast (drop n w))))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst f31)
        using that apply auto
        apply (subst nth_map2)
          apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2
            simps(1) valid_M valid_tm_tape_count)
        apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def TM.next_moves_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 5) M_def)
        apply auto
           apply (metis (no_types, lifting) M_def One_nat_def add.commute lessI nat.distinct(1)
            nth_upt numeral_2_eq_2 plus_1_eq_Suc simps(1) valid_M valid_tm_tape_count)
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
            apply (subst f35 [simplified])
              apply auto
           apply (metis One_nat_def last_conv_nth list.size(3) not_less_zero)
          apply (subst f35 [simplified])
            apply auto
          apply (simp add: butlast_conv_take)
        by (simp_all add: f33 less_eq_Suc_le)
    qed
    have f41': "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
               (Suc (Suc n), None)" and
         f42': "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None []"
         if "length w \<le> n" and "w \<noteq> []" for w :: "'s list"
    proof -
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        apply (subst f21)
        using that apply auto
        unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
            (Suc (Suc n), None)"
        apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding valid_tm_next_state [OF valid_M] apply (subst f21)
        using that apply auto
        apply (subst M_def)
        apply auto
        apply (subst f23)
             apply simp_all
        apply (subst f23)
        by simp_all
      show "tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
            Tape [] None []"
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f21)
        using that apply auto
        apply (subst (1 5) M_def)
        apply auto
         apply (metis (no_types, lifting) M_def One_nat_def add.commute lessI nat.distinct(1)
            nth_upt numeral_2_eq_2 plus_1_eq_Suc simps(1) valid_M valid_tm_tape_count)
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
         apply (subst f25 [simplified])
            apply auto
        apply (subst f25 [simplified])
        by simp_all
    qed
    show tb: "TM.time_bounded_word (Abs_TM M) Suc w" for w :: "'s list"
      unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def
    proof (cases "n < length w")
      case True
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) \<in>
            TM.TM.final_states (Abs_TM M)" unfolding f41 [OF True] valid_tm_final_states [OF valid_M]
        unfolding M_def by simp
    next
      case False
      hence 1: "length w \<le> n" by simp
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) \<in>
            TM.TM.final_states (Abs_TM M)"
      proof (cases "w = []")
        case True
        then show ?thesis apply simp
          unfolding f11' valid_tm_final_states [OF valid_M] unfolding M_def by simp
      next
        case False
        show ?thesis unfolding f41' [OF 1 False] valid_tm_final_states [OF valid_M]
          unfolding M_def by simp
      qed
    qed
    have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) =
             Suc (length w)" for w :: "'s list"
      apply (rule Least_nat_monoI)
        apply auto
       apply (cases "n < length w")
      unfolding f41 [simplified] TM.is_final_def valid_tm_final_states [OF valid_M] apply (subst M_def)
        apply simp
       apply (cases "w = []")
        apply simp
        apply (subst f11')
      apply (subst M_def)
      apply auto
       apply (subst f41' [simplified])
         apply auto
       apply (subst M_def)
       apply simp
      apply (cases "n < length w")
       apply (subst (asm) f31)
         apply auto
       apply (subst (asm) M_def)
       apply simp
      apply (subst (asm) (3) M_def)
      apply simp
      apply (cases "w = []")
       apply auto
      apply (metis (lifting) M_def TM.init_conf_state nat.distinct(1) prod.inject simps(4) valid_M
          valid_tm_initial_state)
      by (simp add: f21)
    have 2: "last (tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w))) =
             tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1"
      for w :: "'s list"
    proof -
      have "length (tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w))) = 2"
        by (metis (no_types, lifting) M_def TM.run_tapes_len simps(1) valid_M valid_tm_tape_count)
      thus "last (tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w))) =
            tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1"
        by (metis One_nat_def diff_Suc_1' last_conv_nth list.size(3) nat.distinct(1) numeral_2_eq_2)
    qed
    show "TM.computes (Abs_TM M) (rev \<circ> drop n)"
      unfolding TM.computes_def apply auto
      unfolding TM.computes_word_def apply auto
      using tb TM.time_bounded_altdef2 apply blast
      unfolding TM.has_output_def TM.compute_def TM.clean_output_of_def apply auto
      unfolding TM.output_of_def Let_def TM.compute_config_def 1 2
    proof -
      fix w :: "'s list"
      show "TM.clean_output ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w))"
        unfolding TM.clean_output_def
      proof (cases "n < length w")
        case True
        show "\<exists>w'. last (tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w))) =
              TM_abbrevs.input_tape w'" unfolding 2 apply (subst f42)
           apply fact
          unfolding TM_abbrevs.input_tape_def apply (rule exI)
          by auto
      next
        case False
        show "\<exists>w'. last (tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w))) =
              TM_abbrevs.input_tape w'" unfolding 2 apply (cases "w = []")
           apply auto
          unfolding f12' [simplified] TM_abbrevs.input_tape_def apply simp
          apply (subst f42' [simplified])
          using False by auto
      qed
      show "(case head (tapes ((TM.step (Abs_TM M) ^^ Suc (length w))
            (TM.initial_config (Abs_TM M) w)) ! 1) of None \<Rightarrow> [] | Some h \<Rightarrow> h # the (those
            (takeWhile (\<lambda>s. s \<noteq> None) (right (tapes ((TM.step (Abs_TM M) ^^ Suc (length w))
            (TM.initial_config (Abs_TM M) w)) ! 1))))) = rev (drop n w)"
      proof (cases "n < length w")
        case True
        have 1: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some (rev (butlast (drop n w)))) =
                 map Some (rev (butlast (drop n w)))" by simp
        show ?thesis apply (subst (1 2) f42)
            apply fact+
          apply auto
          unfolding 1 apply simp
          by (metis Suc_diff_Suc True append_butlast_last_id length_drop list.size(3) nat.distinct(1)
              rev_eq_Cons_iff rev_rev_ident)
      next
        case False
        show ?thesis
          apply (cases "w = []")
           apply simp
          unfolding f12' [simplified] apply simp
          apply (subst (1 2) f42')
          using False by simp_all
      qed
    qed
  next
    have 1: "rev \<circ> (\<lambda>x::'s list. x) = rev" by auto
    show "computable_in_time Suc (rev \<circ> (\<lambda>x::'s list. x))" using rev_computable unfolding 1 by simp
  qed
qed

lemma drop_computable: "computable_in_time (\<lambda>n. 2 * n + 2) ((drop n)::('s::finite) list \<Rightarrow> 's list)"
proof -
  have 1: "((drop n)::('s::finite) list \<Rightarrow> 's list) = rev \<circ> (rev \<circ> (drop n))" unfolding comp_def by simp
  note 2 = rev_drop_computable [of n, where 's='s]
  note 3 = rev_computable [where 'a='s]
  have 4: "\<And>m n. {t. \<exists>w::'s list. length w = m \<and> Suc (length w - n) = t} = {Suc (m - n)}" apply auto
    by (metis Ex_list_of_length)
  note 5 = computable_in_time_compI [OF 2 3, folded 1, unfolded max_Tf_def, simplified, unfolded 4, simplified]
  note computable_mono [OF 5, of "(\<lambda>n. 2 * n + 2)", simplified]
  thus "computable_in_time (\<lambda>n. 2 * n + 2) ((drop n)::('s::finite) list \<Rightarrow> 's list)" by simp
qed

lemma tl_computable: "computable_in_time (\<lambda>n. 2 * n + 2) (tl::('s::finite) list \<Rightarrow> 's list)"
  using drop_computable [of "Suc 0"] unfolding drop_Suc by simp

lemma takeWhile_computable: "computable_in_time (\<lambda>n. 2 * n + 2) ((takeWhile P)::('s::finite) list \<Rightarrow> 's list)"
proof -
  have 1: "((takeWhile P)::('s::finite) list \<Rightarrow> 's list) = rev \<circ> (rev \<circ> takeWhile P)" by auto
  note 2 = rev_takeWhile_computable [of P]
  note 3 = rev_computable [where 'a='s]
  have 4: "\<And>n. Max {t. \<exists>w. length w = n \<and> Suc (length (takeWhile P w)) = t} \<le> n + 1"
  proof simp
    fix n :: nat
    have "{t. \<exists>w. length w = n \<and> Suc (length (takeWhile P w)) = t} \<noteq> {}" by (rule max_Tf_not_empty)
    moreover have "\<And>w. length w = n \<Longrightarrow> Suc (length (takeWhile P w)) \<le> Suc n"
      using length_takeWhile_le by blast
    ultimately show "Max {t. \<exists>w. length w = n \<and> Suc (length (takeWhile P w)) = t} \<le> Suc n"
      by (metis (no_types, lifting) ext max_Tf_def max_Tf_w)
  qed
  note 5 = computable_in_time_compI [OF 2 3, folded 1, unfolded max_Tf_def, simplified]
  show "computable_in_time (\<lambda>n. 2 * n + 2) ((takeWhile P)::('s::finite) list \<Rightarrow> 's list)" apply simp
    apply (rule 5 [THEN computable_mono])
    using 4 by simp
qed

lemma dropWhile_computable: "computable_in_time (\<lambda>n. 2 * n + 2) ((dropWhile P)::('s::finite) list \<Rightarrow> 's list)"
proof -
  have 1: "((dropWhile P)::('s::finite) list \<Rightarrow> 's list) = rev \<circ> (rev \<circ> dropWhile P)" by auto
  note 2 = rev_dropWhile_computable [of P]
  note 3 = rev_computable [where 'a='s]
  have 4: "\<And>n. Max {t. \<exists>w. length w = n \<and> Suc (length (dropWhile P w)) = t} \<le> Suc n"
  proof -
    fix n :: nat
    have "{t. \<exists>w. length w = n \<and> Suc (length (dropWhile P w)) = t} \<noteq> {}" by (rule max_Tf_not_empty)
    moreover have "\<And>w. length w = n \<Longrightarrow> Suc (length (dropWhile P w)) \<le> Suc n"
      using length_dropWhile_le by auto
    ultimately show "Max {t. \<exists>w. length w = n \<and> Suc (length (dropWhile P w)) = t} \<le> Suc n"
      by (metis (no_types, lifting) ext max_Tf_def max_Tf_w)
  qed
  note 5 = computable_in_time_compI [OF 2 3, folded 1, unfolded max_Tf_def, simplified,
      THEN computable_mono]
  show "computable_in_time (\<lambda>n. 2 * n + 2) ((dropWhile P)::('s::finite) list \<Rightarrow> 's list)"
    apply (rule 5)
    using 4 by simp
qed

lemma rev_map_computable: "computable_in_time (\<lambda>n. n + 1) (rev \<circ> map (f::('s::finite) \<Rightarrow> 's))"
proof (rule typed_comp_in_time_natI)
  define M :: "(nat \<times> 's option, 's, unit) TM_record" where
    "M \<equiv> TM 2 UNIV ({0,1,2}\<times>UNIV) (0, None) ({2}\<times>UNIV) (\<lambda>_. ())
         (\<lambda>st hds. if hds ! 0 = None then (2, snd st) else (1, hds ! 0))
         (\<lambda>st _ _. map_option f (snd st))
         (\<lambda>st hds k. if k = 0 then Shift_Right else if hds ! 0 = None \<or> fst st = 0 then
            No_Shift else Shift_Left)"
  have valid_M [intro, simp]: "valid_TM M"
    apply standard
    unfolding M_def by auto
  show "typed_computable_in_time TYPE(nat \<times> 's option) TYPE(unit) (\<lambda>n. n + 1) (rev \<circ> map f)"
  proof (unfold typed_computable_in_time_def, rule exI, auto)
    show syms: "\<And>s. s \<in> TM.TM.symbols (Abs_TM M)" unfolding valid_tm_symbols [OF valid_M]
      unfolding M_def by simp
    have f11: "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (1, Some (w ! 0))" and
         f12: "tl w \<noteq> [] \<Longrightarrow> heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! 1)" and
         f13: "tl w = [] \<Longrightarrow> heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = None" and
         f14: "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) = map Some (drop 2 w)" and
         f15: "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
         if "w \<noteq> []" for w :: "'s list"
    proof -
      have [simp]: "state (TM.initial_config (Abs_TM M) w) \<notin> TM.TM.final_states (Abs_TM M)"
        unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M] apply simp
        unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (1, Some (w ! 0))"
        unfolding TM.step_def apply auto
        unfolding valid_tm_next_state [OF valid_M] TM.initial_config_def TM_abbrevs.input_tape_def
        using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M]
        unfolding M_def apply simp
        by (metis hd_conv_nth)
      show "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! 1)" if "tl w \<noteq> []"
        unfolding TM.step_def apply auto
        apply (subst nth_map)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        apply (metis One_nat_def TM.at_least_one_tape' TM.init_conf_len linorder_not_less list.size(3)
            zero_less_Suc)
        apply (subst nth_zip)
        apply auto
        apply (metis One_nat_def TM.at_least_one_tape' TM.init_conf_len linorder_not_less list.size(3)
            zero_less_Suc)
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] apply (subst (1 4) M_def)
        apply auto
        unfolding TM_abbrevs.tape_action_def apply simp
        unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M] apply simp
        unfolding TM_abbrevs.tape_write_def TM_abbrevs.input_tape_def using that apply auto
        apply (subst Shift_Right_is_right_not_empty)
         apply auto
        by (metis (mono_tags, lifting) hd_conv_nth length_greater_0_conv list.map_disc_iff nth_map nth_tl)
      show "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0 = None" if "tl w = []"
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
         apply (metis TM.at_least_one_tape list.size(3) TM.init_conf_len not_less_zero)
        apply (subst nth_zip)
          apply auto
        apply (metis One_nat_def TM.at_least_one_tape' TM.init_conf_len linorder_not_less list.size(3)
            zero_less_Suc)
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] TM.initial_config_def
        TM_abbrevs.input_tape_def using \<open>w \<noteq> []\<close> apply simp
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M]
        unfolding M_def apply simp
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply simp
        unfolding that by simp
      show "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) =
            map Some (drop 2 w)"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
         apply (simp add: TM.init_conf_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply auto
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] TM.initial_config_def
        TM_abbrevs.input_tape_def using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M]
        unfolding M_def apply simp
        by (metis numeral_2_eq_2 drop_Suc map_tl drop0)
      show "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (metis (no_types, lifting) M_def TM.init_conf_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] TM.initial_config_def
          TM_abbrevs.input_tape_def using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M]
        unfolding M_def apply simp
        unfolding TM_abbrevs.tape_write_def apply simp
        unfolding TM_abbrevs.tape_shift.simps ..
    qed
    have f11': "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (2, None)" and
         f12': "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1 = Tape [] None []"
    proof -
      show "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (2, None)"
        unfolding TM.step_def TM.initial_config_def apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_final_states [OF valid_M]
         apply (subst (asm) (1 2) M_def)
         apply simp
        unfolding valid_tm_next_state [OF valid_M] valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
        unfolding TM_abbrevs.input_tape_def by simp
      show "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1 = Tape [] None []"
        unfolding TM.step_def apply auto
        unfolding valid_tm_initial_state [OF valid_M] TM.initial_config_def valid_tm_final_states [OF valid_M]
         apply auto
        unfolding valid_tm_tape_count [OF valid_M] apply (subst (asm) (1 2) M_def)
         apply simp
        apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) valid_tm_tape_count [OF valid_M] lessI
            numeral_2_eq_2 simps(1))
         apply (simp add: M_def)
        unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count [OF valid_M] apply force
        using M_def valid_tm_tape_count [OF valid_M] apply force
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count [OF valid_M] apply force
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          valid_tm_tape_count [OF valid_M] unfolding M_def TM_abbrevs.input_tape_def apply auto
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def by simp
    qed
    have f21: "state (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) = (1, Some (w ! (k - 1)))" and
         f22: "k < length w \<Longrightarrow> heads (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0 =
               Some (w ! k)" and
         f23: "k = length w \<Longrightarrow> heads (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0 = None" and
         f24: "right (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop (Suc k) w)" and
         f25: "tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None (rev (map (Some \<circ> f) (take (k - 1) w)))"
         if "k \<ge> 1" and "k \<le> length w" for w :: "'s list" and k :: nat using that
    proof (induction k rule: nat_induct_at_least)
      case base
      {
        case 1
        then show ?case using f11 [of w] by simp
      next
        case 2
        then show ?case apply simp
          apply (subst f12 [of w])
            apply auto
          by (simp add: Nitpick.size_list_simp(2))
      next
        case 3
        show ?case apply simp
          apply (subst f13)
          using 3 apply auto
          by (metis Nitpick.size_list_simp(2) nat.inject nat.distinct(1))
      next
        case 4
        then show ?case apply simp
          unfolding f14 numeral_2_eq_2 ..
      next
        case 5
        then show ?case apply simp
          unfolding f15 [simplified] ..
      }
    next
      case (Suc k)
      {
        case 1
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          unfolding Suc(2) [OF *] valid_tm_next_state [OF valid_M] apply (subst M_def)
          apply auto
          unfolding Suc(3) [OF ** *] by simp_all
      next
        case 2
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
           apply (simp add: M_def TM.next_actions_simps(2) TM.run_tapes_len)
          apply (subst nth_zip)
            apply (simp add: TM.next_actions_simps(2))
           apply (simp add: TM.run_tapes_len)
          unfolding Suc(2) [OF *] TM.next_actions_def TM_abbrevs.tape_action_def apply simp
          apply (subst (1 2) nth_zip)
            apply (simp add: TM.next_writes_simps(2))
           apply (metis TM.at_least_one_tape TM.next_moves_simps(2))
          apply simp
          unfolding TM.next_moves_def TM.next_writes_def apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          apply (subst (1 4) M_def)
          apply simp
          unfolding TM_abbrevs.tape_write_def apply (subst Shift_Right_is_right_not_empty)
           apply auto
          using "2.prems"(1) Suc.IH(4) apply force
          unfolding Suc(5) [OF *]
          by (metis drop_map "2.prems"(1) length_map nth_map hd_drop_conv_nth)
      next
        case 3
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map)
          apply (simp add: M_def TM.next_actions_simps(2) TM.run_tapes_len)
          apply (subst nth_zip)
            apply (simp add: TM.next_actions_simps(2))
           apply (metis TM.at_least_one_tape TM.run_tapes_len)
          unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def TM.next_moves_def
          apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
          apply (subst (1 4) M_def)
          apply simp
          unfolding TM_abbrevs.tape_write_def Suc(5) [OF *] using 3(1) by simp
      next
        case 4
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply (simp add: TM.next_actions_simps(2))
           apply (simp add: TM.run_tapes_len)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def apply (subst (1 2) nth_zip)
            apply (simp add: TM.next_writes_simps(2))
           apply (simp add: TM.next_moves_simps(2))
          unfolding TM.next_writes_def TM.next_moves_def apply simp
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
          apply (subst (1 4) M_def)
          apply simp
          unfolding Suc(5) [OF *] by (metis drop_Suc tl_drop drop_map)
      next
        case 5
        hence *: "k \<le> length w" and **: "k < length w" by simp_all
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
          unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
          using M_def valid_tm_tape_count apply force
          apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
              valid_tm_tape_count)
          apply (subst nth_zip)
            apply auto
          using M_def valid_tm_tape_count apply force
          using M_def valid_tm_tape_count apply force
          apply (subst (1 2) nth_map)
          using M_def valid_tm_tape_count apply force
          unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] Suc(2) [OF *]
          apply (subst (1 5) M_def)
          apply auto
          unfolding Suc(3) [OF ** *] apply auto
           apply (metis (no_types, lifting) M_def One_nat_def add.commute lessI nat.distinct(1)
              nth_upt numeral_2_eq_2 plus_1_eq_Suc simps(1) valid_M valid_tm_tape_count)
          unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply simp
          unfolding Suc(6) [OF *, simplified] apply simp
          unfolding TM_abbrevs.tape_shift.simps apply simp
          apply (rule nth_equalityI)
           apply auto
          using ** Suc.hyps apply linarith
        proof -
          fix i :: nat
          assume a1: "i < Suc (min (length w) (k - Suc 0))"
          show "(Some (f (w ! (k - Suc 0))) # rev (map (\<lambda>a. Some (f a)) (take (k - Suc 0) w))) ! i =
                rev (map (\<lambda>a. Some (f a)) (take k w)) ! i" apply (subst nth_Cons)
            apply (cases i)
             apply auto
             apply (subst rev_nth)
            using 5 Suc(1) apply auto
            apply (subst (1 2) rev_nth)
              apply auto
            using a1 apply linarith+
            apply (subst nth_map)
             apply auto
            using a1 apply linarith
            by (metis Suc_pred a1 diff_less_mono2 le_eq_less_or_eq less_Suc0 less_eq_Suc_le
                min.absorb4 nth_take zero_less_Suc)
        qed
      }
    qed
    have f31: "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
               (2, Some (w ! (length w - 1)))" and
         f32: "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] (Some (f (last w))) (rev (map (Some \<circ> f) (butlast w)))"
         if "w \<noteq> []" for w :: "'s list"
    proof -
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" apply (subst f21)
        using that apply auto
        unfolding valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
            (2, Some (w ! (length w - 1)))" apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding valid_tm_next_state [OF valid_M] apply (subst f21)
        using that apply auto
        apply (subst M_def)
        apply simp
        apply (subst f23)
        by simp_all
      show "tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
            Tape [] (Some (f (last w))) (rev (map (Some \<circ> f) (butlast w)))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2
            simps(1) valid_M valid_tm_tape_count)
         apply (metis (lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM.next_actions_def TM_abbrevs.tape_action_def apply (subst (1 2) nth_zip)
        unfolding TM.next_writes_def TM.next_moves_def apply auto
        unfolding valid_tm_tape_count [OF valid_M] apply (simp add: M_def)
        apply (simp add: M_def)
        apply (subst (1 2) nth_map)
        apply (simp add: M_def)
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f21)
        using that apply auto
        apply (subst (1 4 5 8) M_def)
        apply auto
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
           apply (subst f25 [simplified])
             apply auto
          apply (simp add: last_conv_nth)
         apply (subst f25 [simplified])
           apply auto
         apply (simp add: butlast_conv_take)
        apply (subst (asm) f23)
        by simp_all
    qed
    show tb: "TM.time_bounded_word (Abs_TM M) Suc w" for w :: "'s list"
    proof (cases "w = []")
      case True
      then show ?thesis apply (simp add: TM.time_bounded_word_def)
        unfolding TM.is_final_def TM.run_def apply simp
        unfolding f11' valid_tm_final_states [OF valid_M] unfolding M_def by simp
    next
      case False
      then show ?thesis apply (simp add: TM.time_bounded_word_def)
        unfolding TM.is_final_def TM.run_def apply simp
        unfolding f31 [simplified] valid_tm_final_states [OF valid_M] unfolding M_def by simp
    qed
    show "TM.computes (Abs_TM M) (rev \<circ> map f)"
      unfolding TM.computes_def apply auto
    proof -
      fix w :: "'s list"
      have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) =
               Suc (length w)"
        apply (cases "w = []")
        apply (rule Least_nat_monoI)
          apply auto
          apply (subst TM.is_final_def)
          apply (subst f11')
        unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
          apply simp
         apply (subst (asm) TM.is_final_def)
         apply (subst (asm) TM.initial_config_def)
         apply simp
        unfolding valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M]
         apply (subst (asm) (1 2) M_def)
         apply simp
        apply (rule Least_nat_monoI)
          apply auto
        unfolding TM.is_final_def apply (subst f31 [simplified])
          apply auto
        unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
         apply simp
        apply (subst (asm) f21)
          apply auto
        unfolding M_def by simp
      have "length (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
            (TM.initial_config (Abs_TM M) w)))) = 2"
        by (metis (no_types, lifting) M_def TM.run_tapes_len TM.step_l_tps simps(1) valid_M
            valid_tm_tape_count)
      hence 2: "last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
               (TM.initial_config (Abs_TM M) w)))) =
               tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
               (TM.initial_config (Abs_TM M) w))) ! 1"
        by (metis One_nat_def diff_Suc_1 last_conv_nth list.size(3) nat.distinct(1) numeral_2_eq_2)
      show "TM.computes_word (Abs_TM M) w (rev (map f w))"
        unfolding TM.computes_word_def apply auto
        using tb [of w] TM.time_bounded_altdef2 tb apply blast
        unfolding TM.has_output_def TM.compute_def TM.compute_config_def 1 TM.clean_output_of_def
          TM.output_of_def Let_def apply auto
        unfolding 2 [simplified]
         proof (cases "w = []")
           case True
           assume a1: "TM.clean_output (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                       (TM.initial_config (Abs_TM M) w)))"
           show "(case head (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                 (TM.initial_config (Abs_TM M) w))) ! Suc 0) of None \<Rightarrow> [] | Some h \<Rightarrow>
                 h # the (those (takeWhile (\<lambda>s. s \<noteq> None) (right (last (tapes ((TM.step (Abs_TM M) ^^
                 Suc (length w)) (TM.initial_config (Abs_TM M) w)))))))) = rev (map f w)"
             apply (simp add: True)
             apply (subst f12' [simplified])
             by simp
         next
           case False
           have 1: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (rev (map (Some \<circ> f) (butlast w))) =
                    rev (map (Some \<circ> f) (butlast w))" by simp
           show "(case head (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                 (TM.initial_config (Abs_TM M) w))) ! Suc 0) of None \<Rightarrow> [] | Some h \<Rightarrow>
                 h # the (those (takeWhile (\<lambda>s. s \<noteq> None) (right (last (tapes ((TM.step (Abs_TM M) ^^
                 Suc (length w)) (TM.initial_config (Abs_TM M) w)))))))) = rev (map f w)"
             apply (subst f32 [simplified])
              apply fact
             apply auto
             unfolding 2 [simplified] apply (subst f32 [simplified])
              apply auto
             unfolding 1 apply (simp add: False)
             by (metis False append_Cons append_Nil append_butlast_last_id list.map_comp list.simps(9)
                 option.sel rev_append rev_map singleton_rev_conv those_map_Some)
         next
           show "TM.clean_output (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                 (TM.initial_config (Abs_TM M) w)))"
             apply (cases "w = []")
             unfolding TM.clean_output_def 2 [simplified] apply simp
              apply (subst f12' [simplified])
             unfolding TM_abbrevs.input_tape_def apply simp
             apply (subst f32 [simplified])
              apply simp
             apply (rule exI [where x="rev (map f w )"])
             apply auto
              apply (simp add: hd_rev last_map)
             by (simp add: map_tl rev_butlast_is_tl_rev rev_map)
         qed
    qed
  qed
qed

lemma map_computable: "computable_in_time (\<lambda>n. 2 * n + 2) (map (f::('s::finite) \<Rightarrow> 's))"
proof -
  have 1: "(map (f::('s::finite) \<Rightarrow> 's)) = rev \<circ> (rev \<circ> (map f))" unfolding comp_def by simp
  note 2 = rev_map_computable [where f=f]
  note 3 = rev_computable [where 'a='s]
  have 4: "\<And>m n. {t. \<exists>w. length w = n \<and> Suc (length w) = t} = {Suc n}" apply auto
    by (metis Ex_list_of_length)
  note computable_in_time_compI [OF 2 3, folded 1, unfolded max_Tf_def, simplified, unfolded 4, simplified]
  thus "computable_in_time (\<lambda>n. 2 * n + 2) (map (f::('s::finite) \<Rightarrow> 's))" unfolding numeral_2_eq_2 by simp
qed

lemma if_then_else_computable: "alphabet L = UNIV \<Longrightarrow> (\<And>w. w \<in>\<^sub>L L \<longleftrightarrow> P w) \<Longrightarrow>
       L \<in> typed_DTIME TYPE('q1) T1 \<Longrightarrow>
       typed_computable_in_time TYPE('q2) TYPE('l1) T2 f \<Longrightarrow>
       typed_computable_in_time TYPE('q3) TYPE('l2) T3 g \<Longrightarrow>
       computable_in_time (\<lambda>n. T1 n + max (T2 n) (T3 n) + 3 * n + 3)
       (\<lambda>w. if P w then f w else g w)"
proof (drule typed_DTIME_impl_DTIME, drule ex_readonly_input_tm,
       drule typed_comp_in_time_natI, drule typed_comp_in_time_natI,
       (erule computableE)+, auto, fold atomize_all atomize_ball atomize_imp, auto,
       rule typed_comp_in_time_natI)
  fix M\<^sub>L :: "(nat, 'a) TM_decider" and M\<^sub>f :: "(nat, 'a, 'l1) TM" and M\<^sub>g :: "(nat, 'a, 'l2) TM"
  assume a1: "\<And>w. w \<in>\<^sub>L L \<longleftrightarrow> P w" and
         a2: "\<And>w. set w \<subseteq> TM.TM.symbols M\<^sub>L \<Longrightarrow> TM.time_bounded_word M\<^sub>L (\<lambda>n. T1 n + n) w" and
         a3: "UNIV \<subseteq> TM.TM.symbols M\<^sub>L" and
         a4: "\<And>w. TM_decider.decides_word M\<^sub>L L w" and
         a5: "TM.computes M\<^sub>f f" and
         a6: "\<And>w. TM.time_bounded_word M\<^sub>f T2 w" and
         a7: "TM.TM.symbols M\<^sub>f = UNIV" and
         a8: "TM.computes M\<^sub>g g" and
         a9: "\<And>w. TM.time_bounded_word M\<^sub>g T3 w" and
         a10: "TM.TM.symbols M\<^sub>g = UNIV" and
         a11: "alphabet L = UNIV" and
         a12: "\<And>w. set w \<subseteq> TM.TM.symbols M\<^sub>L \<Longrightarrow> hd (tapes (trim_tapes
               ((TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w)))) =
               hd (tapes (TM.initial_config M\<^sub>L w))"
  have 1: "TM.symbols M\<^sub>L = UNIV" using a3 by blast
  have 2: "\<And>w. hd (tapes (trim_tapes ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
           (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))"
    using a12 1 by simp
  have 3: "\<And>w. TM.time_bounded_word M\<^sub>L (\<lambda>n. T1 n + n) w"
    using a2 1 by simp
  have 4: "finite (UNIV::'a set)" unfolding 1 [symmetric] by simp
  define ML_tapes :: "'a tape list \<Rightarrow> 'a tape list" where
    "\<And>tl. ML_tapes tl \<equiv> take (TM.tape_count M\<^sub>L) tl"
  define Mf_tapes :: "'a tape list \<Rightarrow> 'a tape list" where
    "\<And>tl. Mf_tapes tl \<equiv> rev (take (TM.tape_count M\<^sub>f) (rev tl))"
  define Mg_tapes :: "'a tape list \<Rightarrow> 'a tape list" where
    "\<And>tl. Mg_tapes tl \<equiv> rev (take (TM.tape_count M\<^sub>g) (rev tl))"
  define ML_heads :: "'a option list \<Rightarrow> 'a option list" where
    "\<And>hds. ML_heads hds \<equiv> take (TM.tape_count M\<^sub>L) hds"
  define Mf_heads :: "'a option list \<Rightarrow> 'a option list" where
    "\<And>hds. Mf_heads hds \<equiv> rev (take (TM.tape_count M\<^sub>f) (rev hds))"
  define Mg_heads :: "'a option list \<Rightarrow> 'a option list" where
    "\<And>hds. Mg_heads hds \<equiv> rev (take (TM.tape_count M\<^sub>g) (rev hds))"
  have ML_tapes_heads: "\<And>tl. map head (ML_tapes tl) = ML_heads (map head tl)"
    by (simp add: ML_heads_def ML_tapes_def take_map)
  have Mf_tapes_heads: "\<And>tl. map head (Mf_tapes tl) = Mf_heads (map head tl)"
    by (simp add: Mf_tapes_def Mf_heads_def rev_map take_map)
  have Mg_tapes_heads: "\<And>tl. map head (Mg_tapes tl) = Mg_heads (map head tl)"
    by (simp add: Mg_heads_def Mg_tapes_def rev_map take_map)
  define states :: "(nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'a) set" where
    "states \<equiv> {1..4} \<times> (TM.states M\<^sub>L) \<times> (TM.states M\<^sub>f) \<times> (TM.states M\<^sub>g) \<times> {1..5} \<times>
              UNIV \<times> UNIV"
  define final_states :: "(nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'a) set" where
    "final_states \<equiv> states \<inter> {(a, b, c, d, e, f, g). (a = 2 \<or> a = 3) \<and>
                     (a = 2 \<longrightarrow> c \<in> TM.final_states M\<^sub>f) \<and>
                     (a = 3 \<longrightarrow> d \<in> TM.final_states M\<^sub>g)}"
  define initial_state :: "nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'a" where
    "initial_state \<equiv> (1, TM.initial_state M\<^sub>L, TM.initial_state M\<^sub>f, TM.initial_state M\<^sub>g,
                      1, False, undefined)"
  have final_states_subset: "final_states \<subseteq> states" unfolding final_states_def by blast
  have init_state_in_states: "initial_state \<in> states" unfolding initial_state_def states_def
    by simp
  have states_finite: "finite states" unfolding states_def by (standard, simp)+ (rule 4)
  define tc :: nat where "tc \<equiv> TM.tape_count M\<^sub>L + max (TM.tape_count M\<^sub>f) (TM.tape_count M\<^sub>g)"
  have tc_ge_tcL: "tc > TM.tape_count M\<^sub>L" unfolding tc_def by (simp add: less_max_iff_disj)
  have tc_ge_tcf: "tc > TM.tape_count M\<^sub>f" unfolding tc_def
    by (meson TM.at_least_one_tape less_add_same_cancel2 max.strict_boundedE)
  have tc_ge_tcg: "tc > TM.tape_count M\<^sub>g" unfolding tc_def by (simp add: max_def)
  define M' :: "(nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'a, 'a, unit) TM_record" where
    "M' \<equiv> TM tc UNIV states initial_state final_states (\<lambda>_. ())
           (\<lambda>(a, b, c, d, e, f, g) hds. if a = 1 then if b \<in> TM.final_states M\<^sub>L then
           (4, b, c, d, e, TM.label M\<^sub>L b, g) else
           (a, TM.next_state M\<^sub>L b (ML_heads hds), c, d, e, f, g) else
           if a = 2 then (a, b, TM.next_state M\<^sub>f c (Mf_heads hds), d, e, f, g) else
           if a = 3 then (a, b, c, TM.next_state M\<^sub>g d (Mg_heads hds), e, f, g) else
           if e = 1 then if hds ! 0 = None then if f then (2, b, c, d, e, f, g) else
            (3, b, c, d, e, f, g) else (a, b, c, d, 2, f, the (hds ! 0)) else if e = 2 then
             if hds ! 0 = None then (a, b, c, d, 3, f, g) else
              (a, b, c, d, e, f, the (hds ! 0)) else if e = 3 then
              (a, b, c, d, 4, f, g) else
              if hds ! 0 = None then if f then (2, b, c, d, e, f, g) else
            (3, b, c, d, e, f, g) else (a, b, c, d, e, f, g))
            (\<lambda>(a, b, c, d, e, f, g) hds k. if a = 1 then if k < TM.tape_count M\<^sub>L \<and>
              b \<notin> TM.final_states M\<^sub>L then
              TM.next_write M\<^sub>L b (ML_heads hds) k else hds ! k else if a = 2 then
              if k \<ge> tc - TM.tape_count M\<^sub>f then TM.next_write M\<^sub>f c (Mf_heads hds)
              (k + TM.tape_count M\<^sub>f - tc) else hds ! k else
              if a = 3 then if k \<ge> tc - TM.tape_count M\<^sub>g then
              TM.next_write M\<^sub>g d (Mg_heads hds) (k + TM.tape_count M\<^sub>g - tc) else
              hds ! k else if e = 1 then hds ! k else if e = 2 then
              if f then if k = tc - TM.tape_count M\<^sub>f then Some g else hds ! k else
              if k = tc - TM.tape_count M\<^sub>g then Some g else hds ! k else hds ! k)
            (\<lambda>(a, b, c, d, e, f, g) hds k. if a = 1 then if k < TM.tape_count M\<^sub>L \<and>
              b \<notin> TM.final_states M\<^sub>L then
              TM.next_move M\<^sub>L b (ML_heads hds) k else No_Shift else if a = 2 then
              if k \<ge> tc - TM.tape_count M\<^sub>f then TM.next_move M\<^sub>f c (Mf_heads hds)
              (k + TM.tape_count M\<^sub>f - tc) else No_Shift else
              if a = 3 then if k \<ge> tc - TM.tape_count M\<^sub>g then
              TM.next_move M\<^sub>g d (Mg_heads hds) (k + TM.tape_count M\<^sub>g - tc) else
              No_Shift else if e = 1 then if k = 0 then if hds ! 0 = None then No_Shift else
              Shift_Right else No_Shift
              else if e = 2 then if f then if (k = tc - TM.tape_count M\<^sub>f \<or> k = 0) \<and>
              hds ! 0 \<noteq> None then
              Shift_Right else
              if k = 0 then Shift_Left else No_Shift
              else if (k = tc - TM.tape_count M\<^sub>g \<or> k = 0) \<and>
              hds ! 0 \<noteq> None then
              Shift_Right else
              if k = 0 then Shift_Left else No_Shift
              else if e = 3 then if k = 0 then Shift_Left
              else No_Shift else if f then
              if (k = tc - TM.tape_count M\<^sub>f \<or> k = 0) \<and> hds ! 0 \<noteq> None
              then Shift_Left else No_Shift else
              if (k = tc - TM.tape_count M\<^sub>g \<or> k = 0) \<and> hds ! 0 \<noteq> None
              then Shift_Left else No_Shift)"
  have valid_M' [simp, intro]: "valid_TM M'" apply standard
           apply (simp add: M'_def tc_def)
          apply (simp add: M'_def 4)
         apply (simp add: M'_def)
        apply (simp add: M'_def states_finite)
       apply (simp add: M'_def init_state_in_states)
      apply (simp add: M'_def final_states_subset)
  proof (simp_all add: M'_def)
    fix q :: "nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'a" and hds :: "'a option list"
    assume a1: "q \<in> states" and a2: "length hds = tc"
    obtain a b c d e :: nat and f :: bool and g :: 'a where
      q_def [simp]: "q = (a, b, c, d, e, f, g)" using prod_cases7 by blast
    have 1: "(if b \<in> TM.TM.final_states M\<^sub>L then (4, b, c, d, e, TM.TM.label M\<^sub>L b, g) else
             (a, TM.TM.next_state M\<^sub>L b (ML_heads hds), c, d, e, f, g)) \<in> states"
      apply auto
      using a1 [unfolded q_def] unfolding states_def apply auto
      apply (rule TM.next_state_valid)
        apply auto
      unfolding ML_heads_def using a2 tc_ge_tcL apply simp
      using 1 by force
    have 2: "(a, b, TM.TM.next_state M\<^sub>f c (Mf_heads hds), d, e, f, g) \<in> states"
      using a1 unfolding q_def states_def apply auto
      apply (rule TM.next_state_valid)
        apply auto
     unfolding Mf_heads_def using a2 tc_ge_tcf apply simp
     using a7 set_options_eq by blast
   have 3: "(a, b, c, TM.TM.next_state M\<^sub>g d (Mg_heads hds), e, f, g) \<in> states"
      using a1 unfolding q_def states_def apply auto
      apply (rule TM.next_state_valid)
        apply auto
     unfolding Mg_heads_def using a2 tc_ge_tcg apply simp
     by (simp add: a10)
   have 4: "(2, b, c, d, e, f, g) \<in> states" using a1 unfolding q_def states_def by simp
   have 5: "(3, b, c, d, e, f, g) \<in> states" using a1 unfolding q_def states_def by simp
   have 6: "(a, b, c, d, 2, f, the (hds ! 0)) \<in> states" using a1 unfolding q_def states_def
      by simp
   have 7: "(a, b, c, d, 3, f, g) \<in> states" using a1 unfolding q_def states_def by simp
   have 8: "(a, b, c, d, e, f, the (hds ! 0)) \<in> states"
     using a1 unfolding q_def states_def by simp
   have 9: "(a, b, c, d, 4, f, g) \<in> states" using a1 unfolding q_def states_def by simp
   have 10: "(a, b, c, d, 5, f, g) \<in> states" using a1 unfolding q_def states_def by simp
   have 11: "(a, b, c, d, e, f, g) \<in> states" using a1 unfolding q_def .
   have 12: "\<And>P Q x y. P x \<Longrightarrow> P y \<Longrightarrow> P (if Q then x else y)" by simp
    show "(case q of (a, b, c, d, e, f, g) \<Rightarrow> \<lambda>hds. if a = Suc 0
                 then if b \<in> TM.TM.final_states M\<^sub>L
                      then (4, b, c, d, e, TM.TM.label M\<^sub>L b, g)
                      else (a, TM.TM.next_state M\<^sub>L b (ML_heads hds), c, d, e, f, g)
                 else if a = 2 then
                    (a, b, TM.TM.next_state M\<^sub>f c (Mf_heads hds), d, e, f, g)
                      else if a = 3
                           then (a, b, c, TM.TM.next_state M\<^sub>g d (Mg_heads hds), e, f, g)
                           else if e = 1
                                then if hds ! 0 = None
                                     then if f then (2, b, c, d, e, f, g)
                                          else (3, b, c, d, e, f, g)
                                     else (a, b, c, d, 2, f, the (hds ! 0))
                                else if e = 2
                                     then if hds ! 0 = None then (a, b, c, d, 3, f, g)
                                          else (a, b, c, d, e, f, the (hds ! 0))
                                     else if e = 3 then (a, b, c, d, 4, f, g)
                                          else if hds ! 0 = None
then if f then (2, b, c, d, e, f, g) else (3, b, c, d, e, f, g) else (a, b, c, d, e, f, g))
        hds \<in> states"
      unfolding q_def prod.case apply (rule 12)
       apply fact
      apply (rule 12)
       apply fact
      apply (rule 12)
       apply fact
      apply (rule 12)
       apply (rule 12)
        apply (rule 12)
         apply fact+
      apply (rule 12)
       apply (rule 12)
        apply fact+
      apply (rule 12)
       apply fact
      apply (rule 12)
       apply (rule 12)
      by fact+
  qed
  have M'_tc [simp]: "TM.tape_count (Abs_TM M') = tc"
    unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
  have M'_states [simp]: "TM.states (Abs_TM M') = states"
    unfolding valid_tm_states [OF valid_M'] unfolding M'_def by simp
  have M'_init_state [simp]: "TM.initial_state (Abs_TM M') = initial_state"
    unfolding valid_tm_initial_state [OF valid_M'] unfolding M'_def by simp
  have M'_final_states [simp]: "TM.final_states (Abs_TM M') = final_states"
    unfolding valid_tm_final_states [OF valid_M'] unfolding M'_def by simp
  have M'_next_state_general [simp]: "TM.next_state (Abs_TM M') = next_state M'"
    by (rule valid_tm_next_state [OF valid_M'])
  have M'_next_write_general [simp]: "TM.next_write (Abs_TM M') = next_write M'"
    by (rule valid_tm_next_write [OF valid_M'])
  have M'_next_move_general [simp]: "TM.next_move (Abs_TM M') = next_move M'"
    by (rule valid_tm_next_move [OF valid_M'])
  have init_tapes_eq: "ML_tapes (tapes (TM.initial_config (Abs_TM M') w)) =
                       tapes (TM.initial_config M\<^sub>L w)" for w :: "'a list"
    unfolding TM.initial_config_def apply simp
    unfolding TM_abbrevs.input_tape_def ML_tapes_def tc_def apply auto
     apply (metis (no_types, opaque_lifting) Lists.take_replicate Suc_pred
        TM.at_least_one_tape add_diff_inverse_nat add_gr_0 max.cobounded1 max_nat
        not_add_less1 replicate_Suc)
    by (simp add: take_Cons')
  obtain T1' :: "'a list \<Rightarrow> nat" where T1'_final: "\<And>w. TM.is_final M\<^sub>L (TM.run M\<^sub>L (T1' w) w)"
    and T1'_min: "\<And>w n. n < T1' w \<Longrightarrow> \<not>TM.is_final M\<^sub>L (TM.run M\<^sub>L n w)" using a2
    by (metis 3 TM.run_time_halts TM.time_bounded_altdef2 TM.time_leI less_imp_neq
        order.strict_trans1)
  obtain T2' :: "'a list \<Rightarrow> nat" where T2'_final: "\<And>w. TM.is_final M\<^sub>f (TM.run M\<^sub>f (T2' w) w)"
    and T2'_min: "\<And>w n. n < T2' w \<Longrightarrow> \<not>TM.is_final M\<^sub>f (TM.run M\<^sub>f n w)" using a6
    by (metis TM.compute_altdef2 TM.final_run_compute TM.time_altdef TM.time_bounded_wordD
        not_less_Least)
  obtain T3' :: "'a list \<Rightarrow> nat" where T3'_final: "\<And>w. TM.is_final M\<^sub>g (TM.run M\<^sub>g (T3' w) w)"
    and T3'_min: "\<And>w n. n < T3' w \<Longrightarrow> \<not>TM.is_final M\<^sub>g (TM.run M\<^sub>g n w)" using a9
    by (metis TM.compute_altdef2 TM.final_run_compute TM.time_altdef TM.time_bounded_wordD
        not_less_Least)
  have 5: "\<And>l i. i < TM.tape_count M\<^sub>L \<Longrightarrow> i < length l \<Longrightarrow> (ML_tapes l) ! i = l ! i"
    unfolding ML_tapes_def by simp
  have f11: "state (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) =
             (1, state (TM.steps M\<^sub>L n (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 1, False, undefined)" and
       f12: "ML_tapes (tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w))) =
             tapes (TM.steps M\<^sub>L n (TM.initial_config M\<^sub>L w))" and
       f13: "\<And>k. k \<ge> TM.tape_count M\<^sub>L \<Longrightarrow> k < tc \<Longrightarrow> tapes (TM.steps (Abs_TM M') n
             (TM.initial_config (Abs_TM M') w)) ! k = Tape [] None []" if "n \<le> T1' w"
        for n :: nat and w :: "'a list" using that
  proof (induction n)
    case 0
    {
      case 1
      show ?case by (simp add: TM.initial_config_def initial_state_def)
    next
      case 2
      show ?case apply (auto simp add: TM.initial_config_def ML_tapes_def
            TM_abbrevs.input_tape_def)
        apply (metis Lists.take_replicate One_nat_def TM.at_least_one_tape' diff_le_mono
            dual_order.strict_iff_not less_one take_Cons' tc_ge_tcL)
        by (metis Lists.take_replicate One_nat_def TM.at_least_one_tape diff_le_mono nless_le
            take_Cons' tc_ge_tcL)
    next
      case 3
      then show ?case apply (auto simp add: TM.initial_config_def TM_abbrevs.input_tape_def)
        apply (metis Suc_pred gr_zeroI not_less_zero nth_replicate replicate_Suc)
        by (metis (no_types, lifting) One_nat_def Suc_diff_Suc TM.at_least_one_tape'
            diff_zero dual_order.strict_iff_not not0_implies_Suc not_less_eq nth_Cons_pos
            nth_replicate zero_less_Suc)
    }
  next
    case (Suc n)
    {
      case 1
      have 2: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) =
               (1, state ((TM.step M\<^sub>L ^^ n) (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f,
               TM.TM.initial_state M\<^sub>g, 1, False, undefined)"
        using Suc 1 by simp
      have 3: "ML_tapes (tapes ((TM.step (Abs_TM M') ^^ n)
               (TM.initial_config (Abs_TM M') w))) = tapes ((TM.step M\<^sub>L ^^ n)
               (TM.initial_config M\<^sub>L w))" using Suc 1 by simp
      have 4: "\<And>k. TM.TM.tape_count M\<^sub>L \<le> k \<Longrightarrow> k < tc \<Longrightarrow>
               tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! k =
               Tape [] None []" using Suc 1 by simp
      show ?case apply simp
        apply (subst (1 2) TM.step_def)
        apply auto
        using 2 One_nat_def apply presburger
        apply (metis 1 Suc_n_not_le_n T1'_min TM.run_def is_finalI le_trans nless_le
            suc_is_ge)
         apply (subst (asm) final_states_def)
        using 2 apply auto
        apply (subst M'_def)
        apply simp
        by (metis 3 ML_tapes_heads)
    next
      case 2
      have 1: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) =
               (1, state ((TM.step M\<^sub>L ^^ n) (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f,
               TM.TM.initial_state M\<^sub>g, 1, False, undefined)"
        using Suc 2 by simp
      have 3: "ML_tapes (tapes ((TM.step (Abs_TM M') ^^ n)
               (TM.initial_config (Abs_TM M') w))) = tapes ((TM.step M\<^sub>L ^^ n)
               (TM.initial_config M\<^sub>L w))" using Suc 2 by simp
      have 4: "\<And>k. TM.TM.tape_count M\<^sub>L \<le> k \<Longrightarrow> k < tc \<Longrightarrow>
               tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! k =
               Tape [] None []" using Suc 2 by simp
      have 6: "length (tapes ((TM.step M\<^sub>L ^^ n) (TM.initial_config M\<^sub>L w))) = TM.tape_count M\<^sub>L"
        using TM.run_tapes_len by blast
      show ?case apply simp
        apply (subst (1 2) TM.step_def)
        apply auto
        using 3 apply order
          apply (subst (asm) final_states_def)
        using 1 apply auto
         apply (metis 2 T1'_min TM.run_def is_finalI less_eq_Suc_le)
        apply (rule nth_equalityI)
         apply auto
         apply (subst ML_tapes_def)
         apply simp
         apply (subst TM.next_actions_def)
         apply simp
         apply (subst tape_count_step_equal)
          apply auto
          apply (simp add: TM.init_conf_len)
        apply (simp add: TM.init_conf_len TM.next_actions_simps(2) TM.next_moves_simps(2)
            TM.next_writes_simps(2) TM.run_tapes_len tc_def)
        apply (subst 5)
          apply auto
        unfolding ML_tapes_def apply auto
        apply (subst (1 2) map2_subst)
             apply auto
          apply (simp_all add: TM.next_actions_simps(2) 6)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def apply (subst nth_zip)
          apply (simp add: TM.next_writes_simps(2))
         apply (simp add: TM.next_moves_simps(2))
        apply simp
        unfolding TM.next_moves_def TM.next_writes_def apply simp
        apply (subst (1 4) M'_def)
        apply simp
        using 3 5[of _ "tapes ((TM.step (Abs_TM M') ^^ n)
          (TM.initial_config (Abs_TM M') w))"] ML_tapes_heads
            [of "tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))"]
        by presburger
    next
      case 3
      have 1: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) =
               (1, state ((TM.step M\<^sub>L ^^ n) (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f,
               TM.TM.initial_state M\<^sub>g, 1, False, undefined)"
        using Suc 3 by simp
      have 2: "ML_tapes (tapes ((TM.step (Abs_TM M') ^^ n)
               (TM.initial_config (Abs_TM M') w))) = tapes ((TM.step M\<^sub>L ^^ n)
               (TM.initial_config M\<^sub>L w))" using Suc 3 by simp
      have 4: "\<And>k. TM.TM.tape_count M\<^sub>L \<le> k \<Longrightarrow> k < tc \<Longrightarrow>
               tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! k =
               Tape [] None []" using Suc 3 by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
         apply (rule 4)
          apply (rule 3)+
        apply (subst nth_map2)
          apply (simp add: "3.prems"(2) TM.next_actions_simps(2))
         apply (simp add: "3.prems"(2) TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply (subst (1 2) nth_zip)
          apply auto
          apply (rule 3)+
        apply (subst (1 2) nth_map)
         apply simp_all
         apply (rule 3)
        unfolding 1
        apply (subst M'_def)
        using "3.prems"(1,2) apply auto
        apply (subst M'_def)
        apply auto
        by (metis 4 M'_tc TM.run_tapes_len TM_abbrevs.tape_shift.simps(5)
            TM_abbrevs.tape_write_id')
    }
  qed
  have T1'_le_T1: "\<And>w. T1' w \<le> T1 (length w) + length w"
  proof (rule ccontr)
    fix w :: "'a list"
    assume "\<not> T1' w \<le> T1 (length w) + length w"
    hence 1: "T1' w > T1 (length w) + length w" by simp
    note T1'_min [OF 1]
    thus False using 3 unfolding TM.time_bounded_word_def ..
  qed
  have T2'_le_T2: "\<And>w. T2' w \<le> T2 (length w)"
  proof (rule ccontr)
    fix w :: "'a list"
    assume "\<not> T2' w \<le> T2 (length w)"
    hence 1: "T2' w > T2 (length w)" by simp
    note T2'_min [OF 1]
    thus False using a6 unfolding TM.time_bounded_word_def ..
  qed
  have T2'_le_T3: "\<And>w. T3' w \<le> T3 (length w)"
  proof (rule ccontr)
    fix w :: "'a list"
    assume "\<not> T3' w \<le> T3 (length w)"
    hence 1: "T3' w > T3 (length w)" by simp
    note T3'_min [OF 1]
    thus False using a9 unfolding TM.time_bounded_word_def ..
  qed
  have f21: "state (TM.steps (Abs_TM M') (Suc (T1' w)) (TM.initial_config (Abs_TM M') w)) =
             (4, state (TM.steps M\<^sub>L (T1' w) (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 1, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))), undefined)" and
       f22: "tapes (TM.steps (Abs_TM M') (Suc (T1' w)) (TM.initial_config (Abs_TM M') w)) =
             tapes (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w))"
       for w :: "'a list"
        apply simp
        apply (subst TM.step_def)
        apply auto
         apply (subst (asm) f11)
          apply simp
         apply (subst (asm) final_states_def)
         apply simp
        apply (subst f11)
         apply simp
        apply (subst M'_def)
        apply auto
    using T1'_final apply (simp add: TM.is_final_def TM.run_def)
    apply (subst TM.step_def)
    apply auto
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
      TM.next_moves_def apply simp
    apply (rule nth_equalityI)
     apply auto
     apply (simp add: TM.run_tapes_len)
    apply (subst (1 2) f11)
  proof simp_all
    fix i :: nat
    assume a1: "state ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))
                \<notin> final_states" and a2: "i < tc" and
           a3: "i < length (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))"
    have 1: "TM_abbrevs.tape_shift No_Shift (TM_abbrevs.tape_write
             (heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i)
             (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! i)) =
             tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! i"
      unfolding TM_abbrevs.tape_shift.simps
      using TM_abbrevs.tape_write_id' a3 by blast
    show "TM_abbrevs.tape_shift (next_move M'
          (Suc 0, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
          TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, Suc 0, False, undefined)
          (heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) i)
          (TM_abbrevs.tape_write (next_write M'
          (Suc 0, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
          TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, Suc 0, False, undefined)
          (heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) i)
          (tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i)) =
          tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
       apply (subst (1 4) M'_def)
       apply auto
        apply (metis T1'_final TM.run_def is_finalD)
      using 1 by simp_all
  qed
  have 6: "\<And>w. map head (take (TM.TM.tape_count M\<^sub>L) (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)))) ! 0 = heads ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0"
    apply (subst (1 2) nth_map)
     apply auto
    by (metis M'_tc TM.init_conf_len TM.steps_l_tps less_nat_zero_code list.size(3)
        tc_ge_tcL)+
  have 7: "\<And>w. heads ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0 =
           heads ((TM.step M\<^sub>L ^^ (T1 (length w) + (length w))) (TM.initial_config M\<^sub>L w)) ! 0"
    using T1'_le_T1 T1'_final
    by (metis TM.final_mono TM.final_steps_rev TM.run_def)
  have f31: "state (TM.steps (Abs_TM M') (Suc (T1' w + 1))
             (TM.initial_config (Abs_TM M') w)) =
             (4, state (TM.steps M\<^sub>L (T1' w) (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 2, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))), hd w)" and
       f32: "\<And>i. i > 0 \<Longrightarrow> i < tc \<Longrightarrow> tapes (TM.steps (Abs_TM M') (Suc (T1' w + 1))
             (TM.initial_config (Abs_TM M') w)) ! i =
             tapes (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! i" and
       f33: "length w > 1 \<Longrightarrow> tapes (TM.steps (Abs_TM M') (Suc (T1' w + 1))
             (TM.initial_config (Abs_TM M') w)) ! 0 = Tape (head (tapes (TM.steps
             (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0)#
             left (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0))
             (hd (right (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)))
             (tl (right (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)))" and
       f34: "length w = 1 \<Longrightarrow> tapes (TM.steps (Abs_TM M') (Suc (T1' w + 1))
             (TM.initial_config (Abs_TM M') w)) ! 0 = Tape (head (tapes (TM.steps
             (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0)#
             left (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)) None
             (tl (right (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)))" if "w \<noteq> []"
       for w :: "'a list"
      apply (simp_all del: One_nat_def)
      apply (subst TM.step_def)
      apply auto[1]
       apply (subst (asm) f21 [simplified])
       apply (subst (asm) final_states_def)
       apply simp
    apply (subst f21 [simplified])
      apply (subst M'_def)
      apply simp
    unfolding f22 [simplified] f12 [of "T1' w" w, simplified, THEN arg_cong,
        of "map head", THEN arg_cong, of "\<lambda>l. l ! 0", unfolded ML_tapes_def, simplified,
        unfolded 6 7]
    apply auto[1]
    using that 2 [of w]
        apply (smt (verit, ccfv_SIG) 2 TM.init_conf_len TM.initial_config_heads_0
        TM.run_tapes_len hd_conv_nth length_0_conv list.map_disc_iff list.map_sel(1)
        trim_tapes_heads)
       apply (smt (verit, ccfv_SIG) 2 TM.init_conf_len TM.initial_config_heads_0
        TM.run_tapes_len hd_conv_nth length_0_conv list.map_disc_iff list.map_sel(1)
        option.inject that trim_tapes_heads)
     apply (subst TM.step_def)
     apply auto[1]
    using f22 [simplified] apply presburger
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
      TM.next_moves_def apply simp
     apply (subst nth_map2)
       apply auto[1]
      apply (simp add: TM.run_tapes_len TM.step_l_tps)
     apply simp
    unfolding f21 [simplified] f22 [simplified]
  proof -
    fix i :: nat
    assume a1: "0 < i" and a2: "i < tc"
    show "TM_abbrevs.tape_shift (next_move M'
            (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
             TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, Suc 0,
             TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
             undefined)
            (heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) i)
          (TM_abbrevs.tape_write (next_write M'
              (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
               TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, Suc 0,
               TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
               undefined)
              (heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) i)
            (tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i)) =
         tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
      using f12 [of "T1' w" w, simplified, THEN arg_cong,
        of "map head", THEN arg_cong, of "\<lambda>l. l ! i", unfolded ML_tapes_def, simplified]
      apply (subst (1 4) M'_def)
       using a1 apply auto
       by (metis M'_tc TM.run_tapes_len TM_abbrevs.tape_shift.simps(5)
           TM_abbrevs.tape_write_id' a2)
   next
     assume a1: "1 < length w"
     have 1: "[0..<tc] ! 0 = 0"
       using tc_ge_tcg by auto
     have 3: "tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))) ! 0 =
              tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0"
       using f22 [simplified] by presburger
     have 4: "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))) ! 0 =
              heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0"
       using f22 [simplified] by simp
     show "tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + 1))
           (TM.initial_config (Abs_TM M') w))) ! 0 =
           Tape (head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0) #
           left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0))
           (hd (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0)))
           (tl (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0)))"
       apply (subst TM.step_def)
       apply auto
        apply (subst (asm) final_states_def)
       unfolding f21 [simplified] apply simp
       apply (subst nth_map2)
         apply auto
       apply (metis TM.at_least_one_tape' TM.next_actions_simps(2) list.size(3)
           not_one_le_zero)
        apply (metis TM.at_least_one_tape' TM.init_conf_len TM.step_l_tps TM.steps_l_tps
           less_one linorder_not_less list.size(3))
       unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
         TM.next_moves_def apply simp
       apply (subst (1 2) nth_zip)
         apply auto
       using M'_tc apply blast+
       apply (subst (1 2) nth_map)
        apply auto
       using M'_tc apply blast
       unfolding 1 apply (subst (1 5) M'_def)
       apply (simp add: 3 4)
       apply (subst TM_abbrevs.tape_write_id')
        apply auto
       apply (metis TM.run_def TM.run_tapes_non_empty)
       apply (rule tape.expand)
        apply auto
       unfolding TM_abbrevs.tape_shift.simps apply auto
       apply (metis (mono_tags, lifting) 2 TM.at_least_one_tape TM.head_input_None_iff
           TM.init_conf_len TM.run_tapes_len f12 [of "T1' w" w, simplified, THEN arg_cong,
        of "map head", THEN arg_cong, of "\<lambda>l. l ! 0", unfolded ML_tapes_def, simplified,
        unfolded 6 7] hd_conv_nth le_numeral_extra(3) length_map linorder_not_less
      list.map_sel(1) list.size(3) that trim_tapes_heads)
       apply (metis (mono_tags, lifting) "2" TM.at_least_one_tape' TM.head_input_None_iff
           TM.init_conf_len TM.run_tapes_len f12 [of "T1' w" w, simplified, THEN arg_cong,
        of "map head", THEN arg_cong, of "\<lambda>l. l ! 0", unfolded ML_tapes_def, simplified,
        unfolded 6 7] hd_conv_nth length_map list.map_sel(1) list.size(3) not_one_le_zero
        that trim_tapes_heads)
       apply (metis (mono_tags, lifting) 2 TM.at_least_one_tape TM.head_input_None_iff
           TM.init_conf_len TM.run_tapes_len f12 [of "T1' w" w, simplified, THEN arg_cong,
        of "map head", THEN arg_cong, of "\<lambda>l. l ! 0", unfolded ML_tapes_def, simplified,
        unfolded 6 7] bot_nat_0.not_eq_extremum hd_conv_nth length_map list.map_sel(1)
        list.size(3) that trim_tapes_heads)
       apply (rule tape.expand)
       apply auto
       apply (rule Shift_Right_is_right_not_empty)
     proof
       assume right_empty: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                            (TM.initial_config (Abs_TM M') w)) ! 0) = []"
       have 1: "right (tapes (trim_tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))) ! 0) = []" using right_empty
        trim_tapes_prefix_right [of 0 "(TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)"]
         by (metis TM.at_least_one_tape TM.init_conf_len TM.initial_tapes_non_empty_Nil
             TM.run_tapes_len tape.sel(3) trim_tapes_init_conf trim_tapes_right)
       have 2: "right (tapes (TM.initial_config (Abs_TM M') w) ! 0) = []" using 1 2 [of w]
         by (smt (verit, ccfv_SIG) T1'_final T1'_le_T1 TM.at_least_one_tape TM.final_le_run
             TM.initial_config_def TM.run_def TM.run_tapes_len TM_config.sel(2)
             ML_tapes_def f12 hd_conv_nth hd_take length_greater_0_conv
             list.map_disc_iff list.sel(1) nat_le_linear nth_Cons_0 trim_tapes_heads
             trim_tapes_right)
       show False using a1 2 unfolding TM.initial_config_def
         apply (simp add: TM_abbrevs.input_tape_def)
         apply (cases "w = []")
          apply auto
         by (simp add: Nitpick.size_list_simp(2))
     qed
   next
     assume "length w = 1"
     then obtain x :: 'a where w_def: "w = [x]"
       by (metis One_nat_def Suc_length_conv length_0_conv)
     have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
       unfolding f21 [simplified] final_states_def by simp
     have [simp]: "[0..<tc] ! 0 = 0" using tc_ge_tcg by auto
     have 1: "Tape (left (tapes (TM.step (Abs_TM M')
              ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) ! 0))
              (heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))) ! 0)
              (right (tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))) ! 0)) =
              tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))) ! 0"
       by (metis TM.at_least_one_tape TM.run_tapes_len TM_abbrevs.tape_write_def
           TM_abbrevs.tape_write_id' f22 [simplified])
     have 2: "hd (tapes (trim_tapes ((TM.step M\<^sub>L ^^ (T1' [x]))
              (TM.initial_config M\<^sub>L [x])))) = hd (tapes (TM.initial_config M\<^sub>L [x]))"
       using 3 [of "[x]"] T1'_final [of "[x]"]
       by (metis (no_types, opaque_lifting) 2 T1'_le_T1 TM.final_le_steps TM.run_def)
     have 3: "0 < length (tapes ((TM.step M\<^sub>L ^^ T1' [x]) (TM_config (TM.TM.initial_state M\<^sub>L)
              (Tape [] (Some x) [] # Tape [] None [] \<up> (TM.TM.tape_count M\<^sub>L - Suc 0)))))"
       apply simp
       by (metis Suc_pred TM.at_least_one_tape TM.at_least_one_tape' TM.steps_l_tps
           TM_config.sel(2) length_Cons length_replicate list.size(3) not_one_le_zero)
     show "tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + 1))
           (TM.initial_config (Abs_TM M') w))) ! 0 =
           Tape (head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0) # left (tapes ((TM.step (Abs_TM M') ^^
           T1' w) (TM.initial_config (Abs_TM M') w)) ! 0)) None
           (tl (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0)))"
       apply (subst TM.step_def)
       apply auto
       unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
         TM_abbrevs.tape_action_def apply (subst nth_map2)
         apply auto
       using M'_tc apply blast
        apply (metis TM.run_def TM.run_tapes_non_empty f22 [simplified])
       apply (subst (1 2) nth_zip)
         apply auto
       using M'_tc apply blast+
       apply (subst (1 2) nth_map)
        apply simp
       using M'_tc apply blast
       unfolding f21 [simplified] apply simp
       apply (subst M'_def)
       apply simp
       apply (subst (4) M'_def)
       apply auto
       apply (rule tape.expand)
       apply auto
       unfolding TM_abbrevs.tape_write_def
       apply (metis 2 7[of w] TM.at_least_one_tape[of M\<^sub>L] TM.head_input_None_iff[of M\<^sub>L w]
           TM.init_conf_len[of M\<^sub>L w] TM.run_tapes_len[of "T1' w" M\<^sub>L w]
           \<open>\<And>w. tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w))) = tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w))\<close>[of w]
           \<open>heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0 =
            heads ((TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w)) ! 0\<close>
           bot_nat_0.not_eq_extremum[of "0"] hd_conv_nth[of "tapes (TM.initial_config M\<^sub>L w)"]
           hd_conv_nth[of "heads ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))"]
           list.map_disc_iff[of head "tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))"]
           list.map_disc_iff[of head "[]"]
           list.map_sel(1)[of "tapes (trim_tapes ((TM.step M\<^sub>L ^^ T1' w)
            (TM.initial_config M\<^sub>L w)))" head]
           list.size(3) that trim_tapes_heads[of "(TM.step M\<^sub>L ^^ T1' w)
            (TM.initial_config M\<^sub>L w)"] w_def)
         apply (metis 2 7[of w] TM.at_least_one_tape[of M\<^sub>L] TM.head_input_None_iff[of M\<^sub>L w]
           TM.init_conf_len[of M\<^sub>L w] TM.run_tapes_len[of "T1' w" M\<^sub>L w]
           \<open>\<And>w. tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w))) = tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w))\<close>[of w]
           \<open>heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0 =
            heads ((TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w)) ! 0\<close>
           bot_nat_0.not_eq_extremum[of "0"] hd_conv_nth[of "tapes (TM.initial_config M\<^sub>L w)"]
           hd_conv_nth[of "heads ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))"]
           list.map_disc_iff[of head "tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))"]
           list.map_disc_iff[of head "[]"]
           list.map_sel(1)[of "tapes (trim_tapes ((TM.step M\<^sub>L ^^ T1' w)
            (TM.initial_config M\<^sub>L w)))" head]
           list.size(3) that trim_tapes_heads[of "(TM.step M\<^sub>L ^^ T1' w)
            (TM.initial_config M\<^sub>L w)"] w_def)
        apply (metis 2 7[of w] TM.at_least_one_tape[of M\<^sub>L] TM.head_input_None_iff[of M\<^sub>L w]
           TM.init_conf_len[of M\<^sub>L w] TM.run_tapes_len[of "T1' w" M\<^sub>L w]
           \<open>\<And>w. tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w))) = tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w))\<close>[of w]
           \<open>heads ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0 =
            heads ((TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w)) ! 0\<close>
           bot_nat_0.not_eq_extremum[of "0"] hd_conv_nth[of "tapes (TM.initial_config M\<^sub>L w)"]
           hd_conv_nth[of "heads ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))"]
           list.map_disc_iff[of head "tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))"]
           list.map_disc_iff[of head "[]"]
           list.map_sel(1)[of "tapes (trim_tapes ((TM.step M\<^sub>L ^^ T1' w)
            (TM.initial_config M\<^sub>L w)))" head]
           list.size(3) that trim_tapes_heads[of "(TM.step M\<^sub>L ^^ T1' w)
            (TM.initial_config M\<^sub>L w)"] w_def)
       apply (rule tape.expand)
       apply auto
          apply (subst M'_def)
          apply simp
          apply (metis 1 TM_abbrevs.tape_write_def f22 [simplified] tape.sel(2))
       using f22 [simplified] apply force
       unfolding 1 unfolding f22 [simplified] w_def
        apply (cases "right (tapes ((TM.step (Abs_TM M') ^^ T1' [x])
                      (TM.initial_config (Abs_TM M') [x])) ! 0) = []")
         apply auto
       apply (frule Shift_Right_is_right_not_empty)
       using 2 unfolding trim_tapes_def apply simp
       apply (subst (asm) hd_map)
        apply auto
        apply (metis TM.run_def TM.run_tapes_non_empty)
       apply (rule ccontr)
       apply auto
       by (smt (verit, best) One_nat_def Suc_pred TM.at_least_one_tape TM.initial_config_def
           TM.initial_tapes_non_empty_Cons TM.run_tapes_len TM_config.sel(2)
           ML_tapes_def dropWhile_eq_Nil_conv f12 hd_conv_nth
           head_in_right_tape length_Cons length_replicate less_one list.map_disc_iff
           list.size(3) nat_le_linear not_less_eq nth_take option.distinct(1)
           rev_is_Nil_conv set_rev tape.sel(3))
   qed
  have f31': "P [] \<Longrightarrow> state (TM.steps (Abs_TM M') (Suc (T1' [] + 1))
              (TM.initial_config (Abs_TM M') [])) =
              (2, state (TM.steps M\<^sub>L (T1' []) (TM.initial_config M\<^sub>L [])), TM.initial_state M\<^sub>f,
              TM.initial_state M\<^sub>g, 1, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' [])
              (TM.initial_config M\<^sub>L []))), undefined)" and
       f32': "P [] \<Longrightarrow> tapes (TM.steps (Abs_TM M') (Suc (T1' [] + 1))
              (TM.initial_config (Abs_TM M') [])) =
              tapes (TM.steps (Abs_TM M') (T1' []) (TM.initial_config (Abs_TM M') []))"
     apply (simp_all del: One_nat_def)
     apply (subst TM.step_def)
     apply auto [1]
    unfolding f21 [simplified] final_states_def apply (auto simp del: One_nat_def)
     apply (subst M'_def)
  proof (auto simp del: One_nat_def)
    assume [unfolded a1 [of "[]", symmetric]]: "P []"
    hence 1: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])))"
      using a4 [of "[]"] 3 [of "[]"] T1'_final [of "[]"]
      by (metis TM.run_def TM_decider.decides_def TM_decider.rejI TM_decider.rejects_altdef
          is_finalD)
    show "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))) ! 0 = None" using 2 [of "[]"] 3 [of "[]"]
      T1'_final [of "[]"] f22 [simplified, of "[]"]
      by (smt (z3) 6 7 ML_tapes_def Nat.add_0_right TM.at_least_one_tape TM.heads_empty_none
          TM.init_conf_len TM.run_def TM.run_tapes_non_empty bot_nat_0.not_eq_extremum
          f12 hd_conv_nth le_add1 length_0_conv length_map list.map_sel(1) trim_tapes_heads)
    thus "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))) ! 0 = None" .
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L []))) \<Longrightarrow>
          \<exists>y. heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))) ! 0 = Some y" using 1 by contradiction
    show "tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
          (TM.initial_config (Abs_TM M') []))) = tapes ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))"
      apply (rule nth_equalityI)
    proof (simp add: TM.run_tapes_len TM.step_l_tps del: One_nat_def)
      fix i :: nat
      assume a1: "i < length (tapes (TM.step (Abs_TM M')
                  ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
                  (TM.initial_config (Abs_TM M') []))))"
      have 1: "length (tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
               (TM.initial_config (Abs_TM M') [])))) = tc"
        using M'_tc TM.run_tapes_len TM.step_l_tps by blast
      have [simp]: "[0..<tc] ! i = i" using a1 unfolding 1 by simp
      have 2: "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
               (TM.initial_config (Abs_TM M') []))) ! 0 =
               head (tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
               (TM.initial_config (Abs_TM M') []))) ! 0)"
        by (simp add: TM.run_tapes_len TM.step_l_tps tc_def)
      show "tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
            (TM.initial_config (Abs_TM M') []))) ! i =
            tapes ((TM.step (Abs_TM M') ^^ T1' []) (TM.initial_config (Abs_TM M') [])) ! i"
        apply (subst TM.step_def)
        apply auto
        unfolding f21 [simplified] final_states_def apply auto
        apply (subst nth_map2)
          apply (metis TM.next_actions_simps(2) TM.run_tapes_len TM.step_l_tps a1)
         apply (metis TM.run_tapes_len TM.step_l_tps a1)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
          TM_abbrevs.tape_action_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
          apply (fact a1 [unfolded 1])+
        apply (subst (1 2) nth_map)
         apply auto
         apply (fact a1 [unfolded 1])
        apply (subst M'_def)
        apply auto
         apply (subst M'_def)
           apply (simp add: 2)
        unfolding TM_abbrevs.tape_shift.simps(5)
        unfolding f22 [of "[]", simplified] apply (metis TM_abbrevs.tape_write_id)
          apply (subst M'_def)
          apply simp
          apply (metis 1 M'_tc TM.run_tapes_len TM_abbrevs.tape_write_id' a1)
         apply (subst M'_def)
        apply simp
        using
          \<open>heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
            (TM.initial_config (Abs_TM M') []))) ! 0 = None\<close>
          \<open>tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
            (TM.initial_config (Abs_TM M') []))) = tapes ((TM.step (Abs_TM M') ^^ T1' [])
            (TM.initial_config (Abs_TM M') []))\<close>
        by fastforce+
    qed
  qed
  have f31'': "\<not>P [] \<Longrightarrow> state (TM.steps (Abs_TM M') (Suc (T1' [] + 1))
               (TM.initial_config (Abs_TM M') [])) =
               (3, state (TM.steps M\<^sub>L (T1' []) (TM.initial_config M\<^sub>L [])),
               TM.initial_state M\<^sub>f, TM.initial_state M\<^sub>g, 1,
               TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' [])
               (TM.initial_config M\<^sub>L []))), undefined)" and
       f32'': "\<not>P [] \<Longrightarrow> tapes (TM.steps (Abs_TM M') (Suc (T1' [] + 1))
               (TM.initial_config (Abs_TM M') [])) =
               tapes (TM.steps (Abs_TM M') (T1' []) (TM.initial_config (Abs_TM M') []))"
     apply (simp_all del: One_nat_def)
     apply (subst TM.step_def)
     apply auto [1]
    unfolding f21 [simplified] final_states_def apply (auto simp del: One_nat_def)
     apply (subst M'_def)
  proof (auto simp del: One_nat_def)
    assume [unfolded a1 [of "[]", symmetric]]: "\<not>P []"
    hence 1: "\<not>TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])))"
      using a4 [of "[]"] 3 [of "[]"] T1'_final [of "[]"]
      by (metis TM.compute_run_eqI TM.run_def TM_decider.accI TM_decider.accepts_def
          TM_decider.decides_def is_finalD)
    show "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))) ! 0 = None" using 2 [of "[]"] 3 [of "[]"]
      T1'_final [of "[]"] f22 [simplified, of "[]"]
      by (smt (z3) 6 7 ML_tapes_def Nat.add_0_right TM.at_least_one_tape TM.heads_empty_none
          TM.init_conf_len TM.run_def TM.run_tapes_non_empty bot_nat_0.not_eq_extremum
          f12 hd_conv_nth le_add1 length_0_conv length_map list.map_sel(1) trim_tapes_heads)
    thus "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))) ! 0 = None" .
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L []))) \<Longrightarrow>
          \<exists>y. heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))) ! 0 = Some y" using 1 by contradiction
    show "tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
          (TM.initial_config (Abs_TM M') []))) = tapes ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') []))"
      apply (rule nth_equalityI)
    proof (simp add: TM.run_tapes_len TM.step_l_tps del: One_nat_def)
      fix i :: nat
      assume a1: "i < length (tapes (TM.step (Abs_TM M')
                  ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
                  (TM.initial_config (Abs_TM M') []))))"
      have 1: "length (tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
               (TM.initial_config (Abs_TM M') [])))) = tc"
        using M'_tc TM.run_tapes_len TM.step_l_tps by blast
      have [simp]: "[0..<tc] ! i = i" using a1 unfolding 1 by simp
      have 2: "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
               (TM.initial_config (Abs_TM M') []))) ! 0 =
               head (tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
               (TM.initial_config (Abs_TM M') []))) ! 0)"
        by (simp add: TM.run_tapes_len TM.step_l_tps tc_def)
      show "tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + 1))
            (TM.initial_config (Abs_TM M') []))) ! i =
            tapes ((TM.step (Abs_TM M') ^^ T1' []) (TM.initial_config (Abs_TM M') [])) ! i"
        apply (subst TM.step_def)
        apply auto
        unfolding f21 [simplified] final_states_def apply auto
        apply (subst nth_map2)
          apply (metis TM.next_actions_simps(2) TM.run_tapes_len TM.step_l_tps a1)
         apply (metis TM.run_tapes_len TM.step_l_tps a1)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
          TM_abbrevs.tape_action_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
          apply (fact a1 [unfolded 1])+
        apply (subst (1 2) nth_map)
         apply auto
         apply (fact a1 [unfolded 1])
        apply (subst M'_def)
        apply auto
         apply (subst M'_def)
           apply (simp add: 2)
        unfolding TM_abbrevs.tape_shift.simps(5)
        unfolding f22 [of "[]", simplified] apply (metis TM_abbrevs.tape_write_id)
          apply (subst M'_def)
          apply simp
          apply (metis 1 M'_tc TM.run_tapes_len TM_abbrevs.tape_write_id' a1)
         apply (subst M'_def)
        apply simp
        using
          \<open>heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
            (TM.initial_config (Abs_TM M') []))) ! 0 = None\<close>
          \<open>tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ T1' [])
            (TM.initial_config (Abs_TM M') []))) = tapes ((TM.step (Abs_TM M') ^^ T1' [])
            (TM.initial_config (Abs_TM M') []))\<close>
        by fastforce+
    qed
  qed
  have f32''': "tapes ((TM.step (Abs_TM M') ^^ Suc (T1' [] + 1))
                (TM.initial_config (Abs_TM M') [])) = tapes ((TM.step (Abs_TM M') ^^ T1' [])
                (TM.initial_config (Abs_TM M') []))" using f32' f32'' by blast
  have f41: "state (TM.steps (Abs_TM M') (T1' w + 2 + n)
             (TM.initial_config (Abs_TM M') w)) =
             (4, state (TM.steps M\<^sub>L (T1' w) (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 2, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))), w ! n)" and
       f42: "\<And>i. i > 0 \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.tape_count M\<^sub>f \<Longrightarrow>
             i \<noteq> tc - TM.tape_count M\<^sub>g \<Longrightarrow> tapes (TM.steps (Abs_TM M') (T1' w + 2 + n)
             (TM.initial_config (Abs_TM M') w)) ! i =
             tapes (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! i" and
       f43: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + n)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>f) =
             Tape (rev (take n (map Some w))) None []" and
       f44: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.tape_count M\<^sub>f \<noteq> TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + n)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>g) =
             Tape [] None []" and
       f45: "\<not>TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + n)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>g) =
             Tape (rev (take n (map Some w))) None []" and
       f46: "\<not>TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.tape_count M\<^sub>f \<noteq> TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + n)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>f) =
             Tape [] None []" and
       f47: "length w > Suc n \<Longrightarrow> tapes (TM.steps (Abs_TM M') (T1' w + 2 + n)
             (TM.initial_config (Abs_TM M') w)) ! 0 =
             Tape ((rev (take n (right (tapes
             (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
             [head (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)]@
             left (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0))
             (right (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0) ! n)
             (drop (Suc n) (right (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)))"
       if "n < length w" for w :: "'a list" and n :: nat using that
  proof (induction n)
    case 0
    {
      case 1
      then show ?case using f31 [of w] apply simp
        using hd_conv_nth by blast
    next
      case 2
      then show ?case using f32 [of w i] by simp
    next
      case 3
      then show ?case using f32 [of w "tc - TM.tape_count M\<^sub>f"] apply simp
        by (metis M'_tc Nat.add_diff_assoc[of "TM.TM.tape_count M\<^sub>f"
              "max (TM.TM.tape_count M\<^sub>f) (TM.TM.tape_count M\<^sub>g)" "TM.TM.tape_count M\<^sub>L"]
            TM.at_least_one_tape[of M\<^sub>f] TM.at_least_one_tape[of "Abs_TM M'"]
            diff_less[of "TM.TM.tape_count M\<^sub>f" tc] f13[of "T1' w" w
              "tc - TM.TM.tape_count M\<^sub>f"]
            le_add1[of "TM.TM.tape_count M\<^sub>L"
              "max (TM.TM.tape_count M\<^sub>f) (TM.TM.tape_count M\<^sub>g) - TM.TM.tape_count M\<^sub>f"]
            max.cobounded1[of "TM.TM.tape_count M\<^sub>f" "TM.TM.tape_count M\<^sub>g"]
            nat_le_linear[of "T1' w" "T1' w"] tc_def tc_ge_tcf)
    next
      case 4
      then show ?case using f32 [of w "tc - TM.tape_count M\<^sub>g"] apply simp
        by (simp add: f13 max_def tc_def)
    next
      case 5
      then show ?case using f32 [of w "tc - TM.tape_count M\<^sub>g"] apply simp
        by (metis M'_tc Nat.add_diff_assoc[of "TM.TM.tape_count M\<^sub>g"
              "TM.TM.tape_count M\<^sub>g" "TM.TM.tape_count M\<^sub>L"]
            Nat.add_diff_assoc[of "TM.TM.tape_count M\<^sub>g" "TM.TM.tape_count M\<^sub>f"
              "TM.TM.tape_count M\<^sub>L"]
            TM.at_least_one_tape[of "Abs_TM M'"] TM.at_least_one_tape[of M\<^sub>g]
            diff_less[of "TM.TM.tape_count M\<^sub>g" "TM.TM.tape_count M\<^sub>L + TM.TM.tape_count M\<^sub>g"]
            diff_less[of "TM.TM.tape_count M\<^sub>g" "TM.TM.tape_count M\<^sub>L + TM.TM.tape_count M\<^sub>f"]
            f13[of "T1' w" w "tc - TM.TM.tape_count M\<^sub>g"]
            le_add1[of "TM.TM.tape_count M\<^sub>L"
              "max (TM.TM.tape_count M\<^sub>f) (TM.TM.tape_count M\<^sub>g) - TM.TM.tape_count M\<^sub>g"]
            max_def[of "TM.TM.tape_count M\<^sub>f" "TM.TM.tape_count M\<^sub>g"]
            nat_le_linear[of "TM.TM.tape_count M\<^sub>g" "TM.TM.tape_count M\<^sub>g"]
            nat_le_linear[of "TM.TM.tape_count M\<^sub>f" "TM.TM.tape_count M\<^sub>g"]
            nat_le_linear[of "T1' w" "T1' w"] tc_def tc_ge_tcg)
    next
      case 6
      then show ?case using f32 [of w "tc - TM.tape_count M\<^sub>f"] apply simp
        by (metis M'_tc Nat.add_diff_assoc[of "TM.TM.tape_count M\<^sub>f"
              "max (TM.TM.tape_count M\<^sub>f) (TM.TM.tape_count M\<^sub>g)" "TM.TM.tape_count M\<^sub>L"]
            TM.at_least_one_tape[of M\<^sub>f] TM.at_least_one_tape[of "Abs_TM M'"]
            diff_less[of "TM.TM.tape_count M\<^sub>f" tc] f13[of "T1' w" w
              "tc - TM.TM.tape_count M\<^sub>f"]
            le_add1[of "TM.TM.tape_count M\<^sub>L"
              "max (TM.TM.tape_count M\<^sub>f) (TM.TM.tape_count M\<^sub>g) - TM.TM.tape_count M\<^sub>f"]
            max.cobounded1[of "TM.TM.tape_count M\<^sub>f" "TM.TM.tape_count M\<^sub>g"]
            nat_le_linear[of "T1' w" "T1' w"] tc_def tc_ge_tcf)
    next
      case 7
      have 1: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0) \<noteq> []"
      proof
        assume "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)) ! 0) = []"
        hence *: "right (hd (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                  (TM.initial_config (Abs_TM M') w)))) = []"
          by (metis TM.at_least_one_tape TM.run_tapes_len hd_conv_nth less_numeral_extra(3)
              list.size(3))
        have 1: "hd (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))) =
                 hd (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
          by (metis (no_types, lifting) "5" TM.at_least_one_tape TM.run_tapes_len f12
              hd_conv_nth less_numeral_extra(3) list.size(3) nat_le_linear)
        have 2: "\<And>w. hd (tapes (trim_tapes ((TM.step M\<^sub>L ^^ T1' w)
                 (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))"
          using 2 T1'_final by (metis T1'_le_T1 TM.final_le_steps TM.run_def)
        show False using * unfolding 1 using 2 [of w, THEN arg_cong, of right]
          unfolding trim_tapes_def apply simp
          apply (subst (asm) hd_map)
           apply (metis TM.run_def TM.run_tapes_non_empty)
          apply simp
          apply (subst (asm) (2) TM.initial_config_def)
          unfolding TM_abbrevs.input_tape_def apply simp
          using 7(1) by (metis (full_types) "7.prems"(2) Nitpick.size_list_simp(2)
              less_not_refl list.map_disc_iff tape.sel(3))
      qed
      show ?case using 7 f33 [of w] apply auto
         apply (subst (3) zeroth_is_head)
          apply (rule 1)
         apply standard
        by (simp add: drop_Suc)
    }
  next
    case (Suc n)
    {
      case 1
      hence tl_w_not_empty: "tl w \<noteq> []"
        by (metis Nitpick.size_list_simp(2) One_nat_def Zero_not_Suc less_one not_less_zero)
      hence w_not_empty: "w \<noteq> []" by fastforce
      have 2: "n < length w" using 1 by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
         apply (subst (asm) Suc(1) [OF 2, simplified])
         apply (subst (asm) final_states_def)
         apply auto
        apply (subst Suc(1) [OF 2, simplified])
        apply (subst M'_def)
      proof auto
        have *: "set w \<subseteq> TM.TM.symbols M\<^sub>L" using a3 by blast
        have 3: "heads (TM.step (Abs_TM M') (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^
                 (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) ! 0 =
                 Some (w ! Suc n)"
          apply (subst nth_map)
           apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
          unfolding Suc(7) [OF 1 2, THEN arg_cong, of head, simplified]
          unfolding f12 [of "T1' w" w, simplified, unfolded ML_tapes_def, THEN arg_cong,
              of "\<lambda>l. l ! 0", simplified]
        proof -
          note T1'_final [of w] a12 [OF *] a2 [OF *]
          have 1: "hd (tapes (trim_tapes ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                   (TM.initial_config M\<^sub>L w)))) = hd (tapes (trim_tapes
                   ((TM.step M\<^sub>L ^^ (T1' w)) (TM.initial_config M\<^sub>L w))))"
            using T1'_final [of w] a2 [OF *]
            by (metis (no_types, lifting) TM.final_steps_rev TM.run_def
                TM.time_bounded_wordD)
          have 2: "tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0 =
                   hd (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
            by (metis TM.at_least_one_tape TM.run_tapes_len hd_conv_nth less_numeral_extra(3)
                list.size(3))
          have 3: "n < length (right (hd (tapes (trim_tapes ((TM.step M\<^sub>L ^^ T1' w)
                   (TM.initial_config M\<^sub>L w))))))"
            unfolding a12 [OF *, unfolded 1]
            apply (simp add: TM.initial_config_def TM_abbrevs.input_tape_def w_not_empty)
            by (simp add: "1.prems" less_diff_conv)
          show "right (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0) ! n =
                Some (w ! Suc n)" unfolding 2
            apply (subst zeroth_is_head [symmetric])
            apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (rule trim_tapes_right_nth_Some')
              apply (simp add: TM.run_tapes_len)
            using 3
             apply (metis TM.at_least_one_tape TM.run_tapes_len hd_conv_nth list.size(3)
                not_less0 trim_tapes_tape_count)
            apply (subst zeroth_is_head)
            apply (metis TM.at_least_one_tape TM.run_tapes_len list.size(3) not_less0
                trim_tapes_tape_count)
            unfolding a12 [OF *, unfolded 1] unfolding TM.initial_config_def apply simp
            unfolding TM_abbrevs.input_tape_def apply (simp add: w_not_empty)
            by (metis "1.prems" Nitpick.size_list_simp(2) Suc_less_eq nth_map nth_tl
                w_not_empty)
        qed
        thus "\<exists>y. heads (TM.step (Abs_TM M') (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^
              (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) ! 0 = Some y" by blast
        fix y :: 'a
        assume "heads (TM.step (Abs_TM M') (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^
                (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) ! 0 = Some y"
        thus "y = w ! Suc n" unfolding 3 by simp
      qed
    next
      case 2
      hence tl_w_not_empty: "tl w \<noteq> []"
        by (metis Nitpick.size_list_simp(2) One_nat_def Zero_not_Suc less_one not_less_zero)
      hence w_not_empty: "w \<noteq> []" by fastforce
      have 1: "n < length w" using 2 by simp
      have [simp]: "[0..<tc] ! i = i" by (simp add: "2.prems"(2))
      have 4: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
               tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) =
               Tape ((rev (take n (right (tapes
               (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
               [head (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)]@
               left (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0))
               (right (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0) ! n)
               (drop (Suc n) (right (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)))#
               (take (tc - TM.tape_count M\<^sub>f - 1) (tl (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)))))@
               [Tape (rev (take n (map Some w))) None []] @
               (drop (tc - TM.tape_count M\<^sub>f) (tl (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)))))"
        apply (rule nth_equalityI')
         apply auto
        apply (smt (verit) M'_tc Nat.le_imp_diff_is_add One_nat_def Suc_diff_Suc
            TM.at_least_one_tape' TM.init_conf_len TM.step_l_tps TM.steps_l_tps
            add.left_commute diff_diff_cancel diff_le_mono2 diff_less le_eq_less_or_eq
            less_eq_Suc_le min.absorb2 plus_1_eq_Suc tc_ge_tcf)
      proof -
        fix i :: nat
        assume a1: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))" and
               a2: "i < Suc (Suc (min (length (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                    (TM.initial_config (Abs_TM M') w))) - Suc 0)
                    (tc - Suc (TM.TM.tape_count M\<^sub>f)) + (length (tapes
                    ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) -
                    Suc (tc - TM.TM.tape_count M\<^sub>f))))" and
               a3: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + n))
                    (TM.initial_config (Abs_TM M') w))))) = Suc (Suc (min (length
                    (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                    (TM.initial_config (Abs_TM M') w))) - Suc 0)
                    (tc - Suc (TM.TM.tape_count M\<^sub>f)) + (length (tapes
                    ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) -
                    Suc (tc - TM.TM.tape_count M\<^sub>f))))"
        have [simp]: "i < tc" using a2
          by (metis M'_tc TM.init_conf_len TM.step_l_tps TM.steps_l_tps a3)
        have 1: "i = 0 \<or> i > 0 \<and> i < tc - TM.tape_count M\<^sub>f \<or>
                 i = tc - TM.tape_count M\<^sub>f \<or> i > tc - TM.tape_count M\<^sub>f \<and> i < tc"
          by auto
        have *: "tapes ((TM.step (Abs_TM M') ^^ (T1' w))
                 (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>g) =
                 Tape [] None []" by (simp add: f13 tc_def)
        have 3: "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' w + n))
                 (TM.initial_config (Abs_TM M') w)))) ! 0 =
                 Tape ((rev (take n (right (tapes
                 (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
                 [head (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0)]@
                 left (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0))
                 (right (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0) ! n)
                 (drop (Suc n) (right (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0)))"
          using Suc(7) [OF \<open>Suc n < length w\<close> \<open>n < length w\<close>] by simp
        have 4: "i > 0 \<Longrightarrow> i < tc - TM.tape_count M\<^sub>f \<Longrightarrow>
                 tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' w + n))
                 (TM.initial_config (Abs_TM M') w)))) ! i =
                 (take (tc - Suc (TM.TM.tape_count M\<^sub>f)) (tl (tapes
                 ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))))) ! (i - 1)"
        proof -
          assume a4: "0 < i" and a5: "i < tc - TM.TM.tape_count M\<^sub>f"
          have *: "i = tc - TM.tape_count M\<^sub>g \<Longrightarrow> take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                   (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)))) ! (tc - Suc (TM.TM.tape_count M\<^sub>g)) =
                   Tape [] None []" using * a5
            by (metis (no_types, lifting) Suc_diff_Suc Suc_less_eq TM.at_least_one_tape
                TM.run_tapes_len length_greater_0_conv list.collapse nth_Cons_Suc nth_take
                tc_ge_tcf tc_ge_tcg)
          show "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                ((TM.step (Abs_TM M') ^^ (T1' w + n))
                (TM.initial_config (Abs_TM M') w)))) ! i =
                take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) ! (i - 1)"
            apply (cases "i = tc - TM.tape_count M\<^sub>g")
            using * apply simp
            using Suc(4) [OF a1] \<open>n < length w\<close> a5 apply simp
            by (smt (verit, ccfv_threshold) One_nat_def Suc_diff_Suc Suc_pred
                TM.at_least_one_tape TM.run_tapes_len
                Suc(2) [OF a4, simplified] \<open>n < length w\<close> a4 a5 length_greater_0_conv
                list.collapse nat_neq_iff not_less_eq nth_Cons_Suc nth_take tc_ge_tcf)
        qed
        have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + n))
                      (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
        proof
          assume "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + n))
                  (TM.initial_config (Abs_TM M') w))) \<in> final_states"
          hence "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                ((TM.step (Abs_TM M') ^^ (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) \<in>
                final_states"
            by (simp add: TM.step_def)
          thus False
            unfolding Suc(1) [OF \<open>n < length w\<close>, simplified] final_states_def by simp
        qed
        note 5 = Suc(3) [OF a1 \<open>n < length w\<close>, simplified]
        have 6: "i > tc - TM.tape_count M\<^sub>f \<Longrightarrow>
                 tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' w + n))
                 (TM.initial_config (Abs_TM M') w)))) ! i =
                 drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w)))) ! (i - Suc (tc - TM.tape_count M\<^sub>f))"
        proof -
          assume a4: "tc - TM.TM.tape_count M\<^sub>f < i"
          hence 1: "i > 0" using a1 by simp
          have 3: "i = tc - TM.tape_count M\<^sub>g \<Longrightarrow> TM.tape_count M\<^sub>f > TM.tape_count M\<^sub>g"
            using a4 by simp
          have 4: "i = tc - TM.tape_count M\<^sub>g \<Longrightarrow> TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g"
            using a4 by simp
          have *: "Suc (tc - Suc (TM.TM.tape_count M\<^sub>g)) < length (tapes
                   ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))"
            by (metis M'_tc Suc_diff_Suc TM.at_least_one_tape TM.run_tapes_len diff_less
                tc_ge_tcg)
          have **: "TM.TM.tape_count M\<^sub>f - Suc (TM.TM.tape_count M\<^sub>g) <
                    length (drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step
                    (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))))"
            apply simp
            by (smt (verit, ccfv_SIG) M'_tc Suc_diff_Suc Suc_eq_plus1 TM.at_least_one_tape
                TM.run_tapes_len \<open>i < tc\<close> a4 add_diff_cancel_left' add_diff_cancel_right'
                diff_less less_trans_Suc max.absorb3 not_add_less1 not_less_eq tc_def
                zero_less_diff)
          have 5: "TM.TM.tape_count M\<^sub>g < TM.TM.tape_count M\<^sub>f \<Longrightarrow>
                   drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)))) !
                   (TM.TM.tape_count M\<^sub>f - Suc (TM.TM.tape_count M\<^sub>g)) =
                   tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) !
                   (TM.TM.tape_count M\<^sub>f - Suc (TM.TM.tape_count M\<^sub>g) +
                   Suc (tc - TM.tape_count M\<^sub>f))" using tc_ge_tcf tc_ge_tcg apply simp
            using * ** by (simp add: nth_tl tc_def)
          show "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                ((TM.step (Abs_TM M') ^^ (T1' w + n))
                (TM.initial_config (Abs_TM M') w)))) ! i = drop (tc - TM.TM.tape_count M\<^sub>f)
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) ! (i - Suc (tc - TM.tape_count M\<^sub>f))"
            apply (cases "i = tc - TM.tape_count M\<^sub>g")
            using tc_ge_tcg tc_ge_tcf 3 apply simp
            using Suc(4) [OF a1 4] \<open>n < length w\<close> apply simp
             apply (subst f13 [OF Nat.le_refl, symmetric, of i w])
            apply (metis a4 add_diff_cancel_right' less_or_eq_imp_le max.absorb4 max.commute
                tc_def)
            using \<open>i < tc\<close> apply blast
             apply simp
            unfolding 5 apply simp
            using Suc_diff_Suc tc_ge_tcg apply presburger
            using Suc(2) [OF 1 \<open>i < tc\<close>] a4 \<open>n < length w\<close> apply simp
            by (metis (no_types, lifting) M'_tc TM.run_tapes_len \<open>i < tc\<close>
                add_diff_inverse_nat diff_le_self drop_Suc dual_order.asym less_eq_Suc_le
                nat_less_le nth_drop)
        qed
        have [simp]: "min (length (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                      (TM.initial_config (Abs_TM M') w))) - Suc 0)
                      (tc - Suc (TM.TM.tape_count M\<^sub>f)) = tc - Suc (TM.TM.tape_count M\<^sub>f)"
          by (simp add: TM.init_conf_len TM.steps_l_tps)
        show "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
              ((TM.step (Abs_TM M') ^^ (T1' w + n))
              (TM.initial_config (Abs_TM M') w)))) ! i =
              (Tape ((rev (take n (right (tapes
              (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
              head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0)#
              left (tapes (TM.steps (Abs_TM M') (T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0))
              (right (tapes (TM.steps (Abs_TM M') (T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) ! n)
              (drop (Suc n) (right (tapes (TM.steps (Abs_TM M') (T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0))) #
              take (tc - Suc (TM.TM.tape_count M\<^sub>f)) (tl (tapes
              ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))) @
              Tape (rev (take n (map Some w))) None [] # drop (tc - TM.TM.tape_count M\<^sub>f)
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) ! i"
          using 1 apply auto
          using 3 apply simp
            apply (smt (verit, best) 4 M'_tc One_nat_def TM.init_conf_len TM.steps_l_tps
              diff_le_mono2 diff_less_mono le_SucI length_take length_tl less_one
              min.absorb2 minus_nat.diff_0 minus_nat.simps(2) nth_append_left
              verit_comp_simplify1(3) zero_less_iff_neq_zero)
          unfolding 5
           apply (smt (verit, ccfv_threshold) 5 M'_tc Suc_diff_1 Suc_diff_diff
              TM.init_conf_len TM.steps_l_tps \<open>i < tc\<close> diff_Suc_1 length_take length_tl
              min.absorb4 minus_nat.simps(2) nth_Cons_pos nth_append_length tc_ge_tcf
              zero_less_diff)
          apply (subst 6)
           apply auto
          apply (subst nth_append)
          apply auto
          by (smt (verit, ccfv_threshold) 4 6 Suc_diff_Suc Suc_pred TM.run_tapes_len TM.step_l_tps
              a3 add_diff_cancel_left' bot_nat_0.not_eq_extremum diff_diff_left length_take length_tl
              lessI min_def not_add_less1 not_less_eq nth_Cons_Suc nth_append plus_1_eq_Suc
              tc_ge_tcf)
      qed
      have 5: "\<not>TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
               tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) =
               Tape ((rev (take n (right (tapes
               (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
               [head (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)]@
               left (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0))
               (right (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0) ! n)
               (drop (Suc n) (right (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)))#
               (take (tc - TM.tape_count M\<^sub>g - 1) (tl (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)))))@
               [Tape (rev (take n (map Some w))) None []] @
               (drop (tc - TM.tape_count M\<^sub>g) (tl (tapes (TM.steps (Abs_TM M') (T1' w)
               (TM.initial_config (Abs_TM M') w)))))"
        apply (rule nth_equalityI')
        apply auto
        apply (smt (z3) M'_tc One_nat_def Suc_diff_Suc Suc_le_eq TM.at_least_one_tape'
            TM.init_conf_len TM.step_l_tps TM.steps_l_tps add_diff_inverse_nat
            diff_diff_cancel diff_is_0_eq' diff_le_mono2 dual_order.strict_iff_not
            le_numeral_extra(4) min.absorb2 nat_arith.suc1
            ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 tc_ge_tcg)
      proof -
        fix i :: nat
        assume a1: "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
                    (TM.initial_config M\<^sub>L w)))" and
               a2: "i < Suc (Suc (min (length (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                    (TM.initial_config (Abs_TM M') w))) - Suc 0)
                    (tc - Suc (TM.TM.tape_count M\<^sub>g)) + (length (tapes
                    ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) -
                    Suc (tc - TM.TM.tape_count M\<^sub>g))))" and
               a3: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + n))
                    (TM.initial_config (Abs_TM M') w))))) = Suc (Suc (min (length
                    (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                    (TM.initial_config (Abs_TM M') w))) - Suc 0)
                    (tc - Suc (TM.TM.tape_count M\<^sub>g)) + (length (tapes
                    ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))) -
                    Suc (tc - TM.TM.tape_count M\<^sub>g))))"
        have [simp]: "i < tc" using a2
          by (metis M'_tc TM.init_conf_len TM.step_l_tps TM.steps_l_tps a3)
        have 1: "i = 0 \<or> i > 0 \<and> i < tc - TM.tape_count M\<^sub>g \<or>
                 i = tc - TM.tape_count M\<^sub>g \<or> i > tc - TM.tape_count M\<^sub>g \<and> i < tc"
          by auto
        have *: "tapes ((TM.step (Abs_TM M') ^^ (T1' w))
                 (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>f) =
                 Tape [] None []" by (simp add: f13 tc_def)
        have 3: "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' w + n))
                 (TM.initial_config (Abs_TM M') w)))) ! 0 =
                 Tape ((rev (take n (right (tapes
                 (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
                 [head (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0)]@
                 left (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0))
                 (right (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0) ! n)
                 (drop (Suc n) (right (tapes (TM.steps (Abs_TM M') (T1' w)
                 (TM.initial_config (Abs_TM M') w)) ! 0)))"
          using Suc(7) [OF \<open>Suc n < length w\<close> \<open>n < length w\<close>] by simp
        have 4: "i > 0 \<Longrightarrow> i < tc - TM.tape_count M\<^sub>g \<Longrightarrow>
                 tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' w + n))
                 (TM.initial_config (Abs_TM M') w)))) ! i =
                 (take (tc - Suc (TM.TM.tape_count M\<^sub>g)) (tl (tapes
                 ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))))) ! (i - 1)"
        proof -
          assume a4: "0 < i" and a5: "i < tc - TM.TM.tape_count M\<^sub>g"
          have *: "i = tc - TM.tape_count M\<^sub>f \<Longrightarrow> take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                   (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)))) ! (tc - Suc (TM.TM.tape_count M\<^sub>f)) =
                   Tape [] None []" using * a5
            by (metis (no_types, lifting) Suc_diff_Suc Suc_less_eq TM.at_least_one_tape
                TM.run_tapes_len length_greater_0_conv list.collapse nth_Cons_Suc nth_take
                tc_ge_tcf tc_ge_tcg)
          have 1: "take (tc - Suc (TM.TM.tape_count M\<^sub>g)) (tl (tapes ((TM.step
                   (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))) ! (i - 1) =
                   tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) ! i" using a4 a5
            by (simp add: TM.run_tapes_len nth_tl)
          show "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                ((TM.step (Abs_TM M') ^^ (T1' w + n))
                (TM.initial_config (Abs_TM M') w)))) ! i =
                take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) ! (i - 1)"
            apply (cases "i = tc - TM.tape_count M\<^sub>f")
            using * apply simp
            using Suc(6) [OF a1] \<open>n < length w\<close> a5 apply simp
            unfolding 1 apply (subst Suc(2) [simplified])
                 apply auto
              apply (rule a4)
            using a5 apply force
            by (rule \<open>n < length w\<close>)
        qed
        have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + n))
                      (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
        proof
          assume "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + n))
                  (TM.initial_config (Abs_TM M') w))) \<in> final_states"
          hence "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                ((TM.step (Abs_TM M') ^^ (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) \<in>
                final_states"
            by (simp add: TM.step_def)
          thus False
            unfolding Suc(1) [OF \<open>n < length w\<close>, simplified] final_states_def by simp
        qed
        have 5: "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' w + n))
                 (TM.initial_config (Abs_TM M') w)))) ! (tc - TM.tape_count M\<^sub>g) =
                 Tape (rev (take n (map Some w))) None []"
          unfolding Suc(5) [OF a1 \<open>n < length w\<close>, simplified] ..
        have 6: "i > tc - TM.tape_count M\<^sub>g \<Longrightarrow>
                 tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' w + n))
                 (TM.initial_config (Abs_TM M') w)))) ! i =
                 drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w)))) ! (i - Suc (tc - TM.tape_count M\<^sub>g))"
        proof -
          assume a4: "tc - TM.TM.tape_count M\<^sub>g < i"
          hence 1: "i > 0" using a1 by simp
          have 3: "i = tc - TM.tape_count M\<^sub>f \<Longrightarrow> TM.tape_count M\<^sub>g > TM.tape_count M\<^sub>f"
            using a4 by simp
          have 4: "i = tc - TM.tape_count M\<^sub>f \<Longrightarrow> TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g"
            using a4 by simp
          have *: "Suc (tc - Suc (TM.TM.tape_count M\<^sub>f)) < length (tapes
                   ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))"
            by (metis M'_tc Suc_diff_Suc TM.at_least_one_tape TM.run_tapes_len diff_less
                tc_ge_tcf)
          have **: "TM.TM.tape_count M\<^sub>g - Suc (TM.TM.tape_count M\<^sub>f) <
                    length (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step
                    (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))))"
            apply simp
            by (smt (verit, ccfv_SIG) M'_tc Suc_diff_Suc Suc_lessD TM.at_least_one_tape
                TM.run_tapes_len TM.step_l_tps a2 a3 a4 add_diff_cancel_left'
                add_diff_cancel_right' diff_less gr0I linorder_neqE_nat max.absorb4
                not_less_eq tc_def zero_less_diff)
          have 5: "TM.TM.tape_count M\<^sub>f < TM.TM.tape_count M\<^sub>g \<Longrightarrow>
                   drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)))) !
                   (TM.TM.tape_count M\<^sub>g - Suc (TM.TM.tape_count M\<^sub>f)) =
                   tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) !
                   (TM.TM.tape_count M\<^sub>g - Suc (TM.TM.tape_count M\<^sub>f) +
                   Suc (tc - TM.tape_count M\<^sub>g))" using tc_ge_tcf tc_ge_tcg apply simp
            using * ** by (simp add: nth_tl tc_def)
          show "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                ((TM.step (Abs_TM M') ^^ (T1' w + n))
                (TM.initial_config (Abs_TM M') w)))) ! i = drop (tc - TM.TM.tape_count M\<^sub>g)
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) ! (i - Suc (tc - TM.tape_count M\<^sub>g))"
            apply (cases "i = tc - TM.tape_count M\<^sub>f")
            using tc_ge_tcg tc_ge_tcf 3 apply simp
            using Suc(6) [OF a1 4] \<open>n < length w\<close> apply simp
             apply (subst f13 [OF Nat.le_refl, symmetric, of i w])
            apply (metis a4 add_diff_cancel_right' less_or_eq_imp_le max.absorb4 tc_def)
            using \<open>i < tc\<close> apply blast
             apply simp
            unfolding 5 apply simp
            using Suc_diff_Suc tc_ge_tcf apply presburger
            using Suc(2) [OF 1 \<open>i < tc\<close>] a4 \<open>n < length w\<close> apply simp
            by (metis (no_types, lifting) M'_tc TM.run_tapes_len \<open>i < tc\<close>
                add_diff_inverse_nat diff_le_self drop_Suc dual_order.asym less_eq_Suc_le
                nat_less_le nth_drop)
        qed
        have [simp]: "min (length (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                      (TM.initial_config (Abs_TM M') w))) - Suc 0)
                      (tc - Suc (TM.TM.tape_count M\<^sub>g)) = tc - Suc (TM.TM.tape_count M\<^sub>g)"
          by (simp add: TM.run_tapes_len)
        show "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
              ((TM.step (Abs_TM M') ^^ (T1' w + n))
              (TM.initial_config (Abs_TM M') w)))) ! i =
              (Tape ((rev (take n (right (tapes
              (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
              head (tapes (TM.steps (Abs_TM M') (T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0)#
              left (tapes (TM.steps (Abs_TM M') (T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0))
              (right (tapes (TM.steps (Abs_TM M') (T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) ! n)
              (drop (Suc n) (right (tapes (TM.steps (Abs_TM M') (T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0))) #
              take (tc - Suc (TM.TM.tape_count M\<^sub>g)) (tl (tapes ((TM.step (Abs_TM M') ^^
              T1' w) (TM.initial_config (Abs_TM M') w)))) @
              Tape (rev (take n (map Some w))) None [] # drop (tc - TM.TM.tape_count M\<^sub>g)
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) ! i"
          using 1 apply auto
          using 3 apply simp
          apply (smt (verit, ccfv_SIG) 4 One_nat_def Suc_diff_Suc Suc_less_eq Suc_pred
              TM.run_tapes_len TM.step_l_tps a3 add_diff_cancel_left' length_take length_tl
              lessI min_def not_add_less1 nth_append plus_1_eq_Suc tc_ge_tcg)
          apply (smt (verit) 5 One_nat_def Suc_diff_Suc TM.run_tapes_len TM.step_l_tps a3
              add_diff_cancel_left' length_take length_tl lessI min_def not_add_less1
              nth_Cons_Suc nth_append_length plus_1_eq_Suc tc_ge_tcg)
          apply (subst nth_append)
          apply auto
          by (smt (verit) 6 One_nat_def Suc_diff_Suc TM.run_tapes_len TM.step_l_tps a3
              add_diff_cancel_left' bot_nat_0.not_eq_extremum diff_diff_left length_take
              length_tl lessI min_def not_add_less1 not_less_eq nth_Cons_Suc nth_append
              plus_1_eq_Suc tc_ge_tcg)
      qed
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
         apply (subst (asm) Suc(1) [OF 1, simplified])
         apply (subst (asm) final_states_def)
         apply auto
        apply (subst nth_map2)
          apply (simp add: "2.prems"(2) TM.next_actions_simps(2))
         apply (simp add: "2.prems"(2) TM.run_tapes_len TM.step_l_tps)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
          TM_abbrevs.tape_action_def apply simp
        apply (subst (1 2) nth_zip)
          apply (simp add: "2.prems"(2))
         apply (simp add: "2.prems"(2))
        apply (subst (1 2 3) nth_map)
         apply simp
        using "2.prems"(2) apply fastforce
        apply simp
        unfolding Suc(1) [OF 1, simplified]
        apply (cases "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))")
        unfolding 4 5 apply auto
          apply (subst M'_def)
          apply auto
            apply (subst M'_def)
            apply auto
        using "2.prems"(3) apply force
        using "2.prems"(1) apply fastforce
          apply (subst M'_def)
          apply (auto simp add: TM_abbrevs.tape_shift.simps)
         apply (subst TM_abbrevs.tape_write_def)
        using "2.prems"(1) apply force+
        using "2.prems"(3) apply force
          apply (cases "i < tc - TM.tape_count M\<^sub>f")
           apply auto
          apply (rule tape.expand)
      proof auto
        assume a1: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
           and a2: "0 < i" and a3: "i < tc - TM.TM.tape_count M\<^sub>f"
        have 1: "(take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                 (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w)))) @
                 Tape (rev (take n (map Some w))) None [] #
                 drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0) =
                 (take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                 (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0)"
          using a2 a3 apply simp
          by (smt (verit, ccfv_SIG) "2.prems"(2) M'_tc One_nat_def Suc_diff_Suc Suc_less_eq
              Suc_pred TM.at_least_one_tape TM.run_tapes_len length_take length_tl min_def
              nth_append nth_take tc_ge_tcf)
        show "left ((take (tc - Suc (TM.TM.tape_count M\<^sub>f))
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))) @
              Tape (rev (take n (map Some w))) None [] #
              drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0)) =
              left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! i)" unfolding 1
          by (metis (no_types, lifting) "2.prems"(1) Suc_diff_Suc Suc_less_eq Suc_pred
              TM.at_least_one_tape TM.run_tapes_len a3 less_numeral_extra(3) list.collapse
              list.size(3) nth_Cons_Suc nth_take tc_ge_tcf)
        show "head (TM_abbrevs.tape_write (next_write M' (4, state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 2,
              True, w ! n) (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) ! n #
              map head (take (tc - Suc (TM.TM.tape_count M\<^sub>f))
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) @ None # map head
              (drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))))) i)
              ((take (tc - Suc (TM.TM.tape_count M\<^sub>f))
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))) @
              Tape (rev (take n (map Some w))) None [] #
              drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0))) =
              head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! i)"
          unfolding TM_abbrevs.tape_write_def apply simp
          apply (subst M'_def)
          apply auto
          using "2.prems"(3) apply blast
          apply (subst nth_Cons)
          apply (cases i)
           apply auto
          using a2 apply simp
          apply (subst nth_append)
          apply auto
            apply (simp add: nth_tl)
          apply (metis "2.prems"(2) M'_tc TM.run_tapes_len a2 diff_Suc_1' diff_less_mono
              less_eq_Suc_le)
          using a3 by linarith
        show "right ((take (tc - Suc (TM.TM.tape_count M\<^sub>f))
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))) @
              Tape (rev (take n (map Some w))) None [] #
              drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0)) =
              right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! i)" unfolding 1
          by (metis (no_types, opaque_lifting) Suc_diff_Suc Suc_less_eq Suc_pred TM.run_def
              TM.run_tapes_non_empty a2 a3 list.collapse nth_Cons_Suc nth_take tc_ge_tcf)
      next
        assume a1: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
           and a2: "i \<noteq> tc - TM.TM.tape_count M\<^sub>f" and a3: "\<not> i < tc - TM.TM.tape_count M\<^sub>f"
        have 1: "i > tc - TM.tape_count M\<^sub>f" using a2 a3 by simp
        have 2: "(take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                 (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w)))) @
                 Tape (rev (take n (map Some w))) None [] #
                 drop (tc - TM.TM.tape_count M\<^sub>f)
                 (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0) =
                 drop (tc - TM.TM.tape_count M\<^sub>f)
                 (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w)))) !
                 (i - Suc (Suc (tc - Suc (TM.tape_count M\<^sub>f))))"
          using 1 \<open>i < tc\<close>
          by (smt (verit) "2.prems"(1) M'_tc One_nat_def Suc_diff_Suc Suc_less_eq Suc_pred
              TM.at_least_one_tape TM.run_tapes_len a3 diff_diff_left diff_less length_take
              length_tl min.absorb4 nth_Cons_Suc nth_append plus_1_eq_Suc tc_ge_tcf)
        have 3: "(map head (take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                 (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))))) @ None # map head
                 (drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w)))))) ! (i - Suc 0) =
                 map head (drop (tc - TM.TM.tape_count M\<^sub>f)
                 (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                 (TM.initial_config (Abs_TM M') w))))) !
                 (i - Suc (Suc (tc - Suc (TM.tape_count M\<^sub>f))))"
          using 1 \<open>i < tc\<close>
          by (smt (verit, ccfv_threshold) "2.prems"(1) M'_tc One_nat_def Suc_diff_Suc
              Suc_pred TM.init_conf_len TM.steps_l_tps diff_diff_left length_map length_take
              length_tl less_SucI less_trans_Suc min.absorb4 not_less_eq nth_Cons_Suc
              nth_append plus_1_eq_Suc tc_ge_tcf)
        show "TM_abbrevs.tape_write (next_write M' (4, state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 2,
              True, w ! n) (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) ! n #
              map head (take (tc - Suc (TM.TM.tape_count M\<^sub>f))
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) @ None # map head
              (drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))))) i)
              ((take (tc - Suc (TM.TM.tape_count M\<^sub>f))
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))) @
              Tape (rev (take n (map Some w))) None [] #
              drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0)) =
              tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
          apply (subst M'_def)
          apply auto
          using a2 apply fastforce
          unfolding 2 apply (rule tape.expand)
          apply auto
          apply (smt (verit, best) 1 "2.prems"(1) M'_tc One_nat_def Suc_diff_Suc
              TM.at_least_one_tape' TM.run_tapes_len add_diff_inverse_nat
              bot_nat_0.not_eq_extremum diff_diff_left diff_le_mono2 length_tl
              less_eq_Suc_le list.collapse list.size(3) not_less_eq nth_Cons_Suc nth_drop
              plus_1_eq_Suc tc_ge_tcf)
           apply (subst nth_Cons)
           apply (cases i)
            apply auto
          using "2.prems"(1) apply force
           apply (subst nth_append)
           apply auto
             apply (metis Suc_diff_Suc Suc_less_eq a3 tc_ge_tcf)
          apply (metis "2.prems"(1,2) M'_tc TM.run_tapes_len diff_Suc_1' diff_less_mono
              less_eq_Suc_le)
           apply (smt (verit) 1 "2.prems"(2) 3 M'_tc One_nat_def Suc_diff_Suc
              TM.at_least_one_tape TM.run_tapes_len TM_abbrevs.tape_write_id'
              add_diff_inverse_nat diff_Suc_1' diff_Suc_Suc diff_less diff_less_mono
              length_drop length_map length_take length_tl less_Suc_eq_le
              min.absorb4 not_less_eq nth_append nth_drop nth_tl tc_ge_tcf)
          by (metis (no_types, opaque_lifting) "2.prems"(2) M'_tc Suc_diff_Suc
              TM.run_tapes_len a3 add_diff_inverse_nat diff_less_Suc drop_Suc less_antisym
              less_eq_Suc_le nth_drop tc_ge_tcf)
      next
        assume a1: "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
                    (TM.initial_config M\<^sub>L w)))"
        show "TM_abbrevs.tape_shift (next_move M' (4, state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f,
              TM.TM.initial_state M\<^sub>g, 2, False, w ! n)
              (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) ! n #
              map head (take (tc - Suc (TM.TM.tape_count M\<^sub>g))
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) @ None # map head
              (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))))) i) (TM_abbrevs.tape_write
              (next_write M' (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
              TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 2, False, w ! n)
              (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) ! n # map head (take (tc - Suc
              (TM.TM.tape_count M\<^sub>g)) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) @ None # map head
              (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)))))) i) ((Tape (rev (take n (right
              (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0))) @ head
              (tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0)
              # left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0))
              (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) ! n) (drop (Suc n) (right
              (tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) !
              0))) # take (tc - Suc (TM.TM.tape_count M\<^sub>g)) (tl (tapes ((TM.step
              (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))) @
              Tape (rev (take n (map Some w))) None [] #
              drop (tc - TM.TM.tape_count M\<^sub>g)
              (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w))))) ! i)) =
              tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
          apply (subst M'_def)
          apply auto
            apply (subst M'_def)
            apply auto
          using "2.prems"(4) apply fastforce
           apply (subst M'_def)
           apply auto
          using "2.prems"(1) apply fastforce+
          using "2.prems"(4) apply force
          apply (subst M'_def)
          apply auto
          unfolding TM_abbrevs.tape_write_def TM_abbrevs.tape_shift.simps
        proof (cases "i < tc - TM.TM.tape_count M\<^sub>g")
          case True
          assume a1: "0 < i"
          have 1: "(take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                   (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)))) @
                   Tape (rev (take n (map Some w))) None [] #
                   drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step
                   (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))))) !
                   (i - Suc 0) = tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w))) ! (i - Suc 0)"
            using a1 True by (simp add: TM.run_tapes_len nth_append_left)
          have 2: "(map head (take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                   (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w))))) @ None # map head
                   (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step
                   (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))))) !
                   (i - Suc 0) = head (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w))) ! (i - Suc 0))"
            using a1 True
            by (simp add: Suc_less_SucD TM.init_conf_len TM.steps_l_tps nth_append)
          show "Tape (left ((take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) @
                Tape (rev (take n (map Some w))) None [] #
                drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step
                (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))))) !
                (i - Suc 0))) ((map head (take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) @ None # map head
                (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^
                T1' w) (TM.initial_config (Abs_TM M') w)))))) ! (i - Suc 0))
                (right ((take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) @
                Tape (rev (take n (map Some w))) None [] # drop (tc - TM.TM.tape_count M\<^sub>g)
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0))) =
                tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)) ! i"
            unfolding 1 apply (rule tape.expand)
            apply auto
              apply (metis (no_types, opaque_lifting) One_nat_def TM.at_least_one_tape
                TM.run_tapes_len a1 length_greater_0_conv list.collapse nth_Cons_pos)
            unfolding 2
            by (metis (no_types, opaque_lifting) One_nat_def TM.at_least_one_tape
                TM.run_tapes_len a1 length_greater_0_conv list.collapse nth_Cons_pos)+
        next
          case False
          assume a1: "0 < i" and a2: "i \<noteq> tc - TM.TM.tape_count M\<^sub>g"
          have 1: "i > tc - TM.TM.tape_count M\<^sub>g" using False a2 by simp
          have 2: "(take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                   (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)))) @
                   Tape (rev (take n (map Some w))) None [] #
                   drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step
                   (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))))) !
                   (i - Suc 0) = tapes ((TM.step
                   (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
            apply (subst nth_append)
            apply auto
              apply (simp add: a1 nth_tl)
             apply (metis "2.prems"(2) M'_tc TM.run_tapes_len a1 diff_less_mono
                less_eq_Suc_le)
            using 1 \<open>i < tc\<close>
            by (smt (verit, best) M'_tc Nat.diff_add_assoc One_nat_def Suc_diff_Suc
                Suc_less_eq Suc_pred TM.at_least_one_tape TM.run_tapes_len a1
                add_diff_inverse_nat diff_less length_tl less_eq_Suc_le min.absorb4
                nth_Cons_pos nth_drop nth_tl tc_ge_tcg zero_less_diff)
          have [simp]: "min (length (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                        (TM.initial_config (Abs_TM M') w))) - Suc 0)
                        (tc - Suc (TM.TM.tape_count M\<^sub>g)) = tc - Suc (TM.tape_count M\<^sub>g)"
            by (simp add: TM.run_tapes_len)
          have 3: "(map head (take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                   (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w))))) @ None # map head
                   (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step
                   (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)))))) !
                   (i - Suc 0) = heads ((TM.step
                   (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
            apply (subst nth_append)
            apply auto
            using 1 apply linarith
            apply (subst nth_Cons)
            apply (cases "i - Suc (tc - Suc (TM.TM.tape_count M\<^sub>g))")
             apply auto
             apply (metis 1 Suc_diff_Suc dual_order.strict_iff_not tc_ge_tcg)
            apply (subst nth_map)
             apply auto
             apply (metis 1 "2.prems"(2) M'_tc Suc_diff_Suc TM.run_tapes_len
                diff_less_mono less_eq_Suc_le tc_ge_tcg)
            apply (subst nth_drop)
             apply auto
             apply (metis M'_tc One_nat_def TM.at_least_one_tape' TM.run_tapes_len
                diff_le_mono2)
            by (metis (no_types, lifting) "2.prems"(2) False M'_tc Suc_diff_Suc TM.run_def
                TM.run_tapes_len TM.run_tapes_non_empty add.left_commute
                add_diff_inverse_nat list.collapse nth_Cons_Suc nth_map plus_1_eq_Suc
                tc_ge_tcg)
          show "Tape (left ((take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) @
                Tape (rev (take n (map Some w))) None [] #
                drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step
                (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w))))) !
                (i - Suc 0))) ((map head (take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) @ None # map head
                (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^
                T1' w) (TM.initial_config (Abs_TM M') w)))))) ! (i - Suc 0))
                (right ((take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) @
                Tape (rev (take n (map Some w))) None [] # drop (tc - TM.TM.tape_count M\<^sub>g)
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0))) =
                tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)) ! i"
            unfolding 2 apply (rule tape.expand)
            apply auto
            unfolding 3 by (simp add: "2.prems"(2) TM.run_tapes_len)
        next
          assume a1: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                      (TM.initial_config (Abs_TM M') w)) ! 0) ! n = None"
          have *: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) ! 0) ! n = Some (w ! (Suc n))"
            unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
                of "\<lambda>l. l ! 0", simplified]
            using T1'_final [of w] 2(5) \<open>\<And>w. hd (tapes (trim_tapes
                ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))\<close> [of w,
              THEN arg_cong, of right]
            unfolding trim_tapes_def apply auto
            apply (subst (asm) hd_map)
             apply auto
             apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (subst (asm) (2) TM.initial_config_def)
            unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
            by (smt (verit, best) T1'_le_T1 TM.at_least_one_tape' TM.final_le_steps
                TM.init_conf_len TM.run_def TM.run_tapes_non_empty TM.steps_l_tps
                antisym_conv3 diff_Suc_1 diff_less_mono leD length_map length_tl less_one
                less_zeroE linorder_le_less_linear nat.discI nth_map nth_tl trim_tapes_right
                trim_tapes_right_nth_Some' zeroth_is_head)
          show "Tape (left ((take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) @
                Tape (rev (take n (map Some w))) None [] #
                drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0)))
                (next_write M' (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
                TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 2, False, w ! n)
                (None # map head (take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) @ None # map head
                (drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))))) i)
                (right ((take (tc - Suc (TM.TM.tape_count M\<^sub>g))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) @
                Tape (rev (take n (map Some w))) None [] #
                drop (tc - TM.TM.tape_count M\<^sub>g) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0))) =
                tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
            apply (rule FalseE)
            using a1 * by simp
        qed
      next
        assume a1: "(4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
                    TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 2, True, w ! n)
                    \<notin> final_states" and
               a2: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
           and a3: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                    (TM.initial_config (Abs_TM M') w)) ! 0) ! n = None"
        have *: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) ! 0) ! n = Some (w ! (Suc n))"
            unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
                of "\<lambda>l. l ! 0", simplified]
            using T1'_final [of w] 2(5) \<open>\<And>w. hd (tapes (trim_tapes
                ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))\<close> [of w,
              THEN arg_cong, of right]
            unfolding trim_tapes_def apply auto
            apply (subst (asm) hd_map)
             apply auto
             apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (subst (asm) (2) TM.initial_config_def)
            unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
            by (smt (verit, best) T1'_le_T1 TM.at_least_one_tape' TM.final_le_steps
                TM.init_conf_len TM.run_def TM.run_tapes_non_empty TM.steps_l_tps
                antisym_conv3 diff_Suc_1 diff_less_mono leD length_map length_tl less_one
                less_zeroE linorder_le_less_linear nat.discI nth_map nth_tl trim_tapes_right
                trim_tapes_right_nth_Some' zeroth_is_head)
          show "TM_abbrevs.tape_write (next_write M' (4, state ((TM.step M\<^sub>L ^^ T1' w)
                (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 2,
                True, w ! n) (None # map head (take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) @ None # map head
                (drop (tc - TM.TM.tape_count M\<^sub>f) (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))))) i)
                ((take (tc - Suc (TM.TM.tape_count M\<^sub>f))
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)))) @
                Tape (rev (take n (map Some w))) None [] # drop (tc - TM.TM.tape_count M\<^sub>f)
                (tl (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w))))) ! (i - Suc 0)) =
                tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
          apply (rule FalseE)
          using a3 * by simp
      qed
    next
      case 3
      have "n < length w" using 3(2) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + n))
                    (TM.initial_config (Abs_TM M') w)))) \<notin> final_states"
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>] final_states_def by simp
      have "w \<noteq> []" using 3(2) by auto
      have *: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) ! 0) ! n = Some (w ! (Suc n))"
            unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
                of "\<lambda>l. l ! 0", simplified]
            using T1'_final [of w] 3(2) \<open>\<And>w. hd (tapes (trim_tapes
                ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))\<close> [of w,
              THEN arg_cong, of right]
            unfolding trim_tapes_def apply auto
            apply (subst (asm) hd_map)
             apply auto
             apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (subst (asm) (2) TM.initial_config_def)
            unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
            by (smt (verit, best) T1'_le_T1 TM.at_least_one_tape' TM.final_le_steps
                TM.init_conf_len TM.run_def TM.run_tapes_non_empty TM.steps_l_tps
                antisym_conv3 diff_Suc_1 diff_less_mono leD length_map length_tl less_one
                less_zeroE linorder_le_less_linear nat.discI nth_map nth_tl trim_tapes_right
                trim_tapes_right_nth_Some' zeroth_is_head)
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>]
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
        using tc_ge_tcL apply auto
        unfolding Suc(3) [OF 3(1) \<open>n < length w\<close>, simplified] apply (subst M'_def)
        using 3 apply auto
             apply (subst M'_def)
        unfolding TM_abbrevs.tape_write_def apply simp
        unfolding TM_abbrevs.tape_shift.simps
             apply (simp add: \<open>n < length w\<close> take_Suc_conv_app_nth)
            apply (subst M'_def)
            apply simp
        unfolding TM_abbrevs.tape_shift.simps
        apply (subst (asm) nth_map)
         apply (simp add: TM.run_tapes_len TM.step_l_tps)
        using linorder_not_less tc_ge_tcf apply blast
         apply (subst M'_def)
         apply (auto simp add: TM_abbrevs.tape_shift.simps)
          apply (simp add: take_Suc_conv_app_nth)
         apply (subst (asm) nth_map)
          apply (simp add: TM.run_tapes_len TM.step_l_tps)
        unfolding Suc(7) [OF 3(2) \<open>n < length w\<close>, simplified] apply simp
        using 2 [of w] * apply simp
        apply (subst (asm) nth_map)
         apply (simp add: TM.run_tapes_len TM.step_l_tps)
        unfolding Suc(7) [OF 3(2) \<open>n < length w\<close>, simplified] apply simp
        using 2 [of w] * by simp
    next
      case 4
      have "n < length w" using 4(3) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + n))
                    (TM.initial_config (Abs_TM M') w)))) \<notin> final_states"
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        by (simp add: tc_def)
      have "w \<noteq> []" using 4(3) by auto
      have *: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) ! 0) ! n = Some (w ! (Suc n))"
            unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
                of "\<lambda>l. l ! 0", simplified]
            using T1'_final [of w] 4(3) \<open>\<And>w. hd (tapes (trim_tapes
                ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))\<close> [of w,
              THEN arg_cong, of right]
            unfolding trim_tapes_def apply auto
            apply (subst (asm) hd_map)
             apply auto
             apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (subst (asm) (2) TM.initial_config_def)
            unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
            by (smt (verit, best) T1'_le_T1 TM.at_least_one_tape' TM.final_le_steps
                TM.init_conf_len TM.run_def TM.run_tapes_non_empty TM.steps_l_tps
                antisym_conv3 diff_Suc_1 diff_less_mono leD length_map length_tl less_one
                less_zeroE linorder_le_less_linear nat.discI nth_map nth_tl trim_tapes_right
                trim_tapes_right_nth_Some' zeroth_is_head)
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>]
          Suc(4) [OF 4(1, 2) \<open>n < length w\<close>, simplified]
        unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
        using tc_ge_tcL apply force
        apply simp
        apply (subst (1 2) nth_map)
         apply simp
        using M'_tc diff_less apply blast
        apply simp
        apply (subst M'_def)
        using 4 apply auto
        using linorder_not_less tc_ge_tcg apply blast
        using linorder_not_less tc_ge_tcg apply blast
         apply (subst M'_def)
         apply (simp add: TM_abbrevs.tape_shift.simps)
        using Suc(4) [simplified, OF 4(1, 2) \<open>n < length w\<close>]
        apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
            TM_abbrevs.tape_write_id' diff_less)
        using * Suc(7) [OF 4(3) \<open>n < length w\<close>] apply simp
        by (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
            TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' option.distinct(1)
            tape.sel(2))
    next
      case 5
      have "n < length w" using 5(2) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + n))
                    (TM.initial_config (Abs_TM M') w)))) \<notin> final_states"
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>] final_states_def by simp
      have "w \<noteq> []" using 5(2) by auto
      have *: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) ! 0) ! n = Some (w ! (Suc n))"
            unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
                of "\<lambda>l. l ! 0", simplified]
            using T1'_final [of w] 5(2) \<open>\<And>w. hd (tapes (trim_tapes
                ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))\<close> [of w,
              THEN arg_cong, of right]
            unfolding trim_tapes_def apply auto
            apply (subst (asm) hd_map)
             apply auto
             apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (subst (asm) (2) TM.initial_config_def)
            unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
            by (smt (verit, best) T1'_le_T1 TM.at_least_one_tape' TM.final_le_steps
                TM.init_conf_len TM.run_def TM.run_tapes_non_empty TM.steps_l_tps
                antisym_conv3 diff_Suc_1 diff_less_mono leD length_map length_tl less_one
                less_zeroE linorder_le_less_linear nat.discI nth_map nth_tl trim_tapes_right
                trim_tapes_right_nth_Some' zeroth_is_head)
      have 1: "right (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' w + n)) (TM.initial_config (Abs_TM M') w)))) !
               (tc - TM.TM.tape_count M\<^sub>g)) = []"
        using Suc(5) [OF 5(1) \<open>n < length w\<close>] by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
        unfolding Suc(1) [OF \<open>n < length w\<close>, simplified] TM_abbrevs.tape_action_def
          TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
        using tc_ge_tcL apply fastforce+
        apply simp
        apply (subst (1 2) nth_map)
        using tc_ge_tcL apply auto
        apply (subst M'_def)
        using 5 apply auto
          apply (subst M'_def)
          apply simp
        using Suc(5) [simplified, OF 5(1) \<open>n < length w\<close>] apply simp
        unfolding TM_abbrevs.tape_write_def apply simp
        unfolding TM_abbrevs.tape_shift.simps
         apply (simp add: \<open>n < length w\<close> take_Suc_conv_app_nth)
        using * Suc(7) [OF 5(2) \<open>n < length w\<close>] apply simp
        apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
            TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' option.distinct(1)
            tape.sel(2))
         apply (subst (5) M'_def)
         apply auto
        unfolding 1 unfolding TM_abbrevs.tape_shift.simps apply auto
        apply (simp add: Suc(5) [simplified, OF 5(1) \<open>n < length w\<close>]
            take_Suc_conv_app_nth)
         apply (subst (asm) nth_map)
          apply (simp add: TM.run_tapes_len TM.step_l_tps)
        unfolding Suc(7) [OF 5(2) \<open>n < length w\<close>, simplified] apply simp
        unfolding * apply simp
        apply (subst (asm) nth_map)
         apply (simp add: TM.run_tapes_len TM.step_l_tps)
        unfolding Suc(7) [OF 5(2) \<open>n < length w\<close>, simplified] apply simp
        unfolding * by simp
    next
      case 6
      have "n < length w" using 6(3) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + n))
                    (TM.initial_config (Abs_TM M') w)))) \<notin> final_states"
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        by (simp add: tc_def)
      have "w \<noteq> []" using 6(3) by auto
      have *: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                   (TM.initial_config (Abs_TM M') w)) ! 0) ! n = Some (w ! (Suc n))"
            unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
                of "\<lambda>l. l ! 0", simplified]
            using T1'_final [of w] 6(3) \<open>\<And>w. hd (tapes (trim_tapes
                ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))\<close> [of w,
              THEN arg_cong, of right]
            unfolding trim_tapes_def apply auto
            apply (subst (asm) hd_map)
             apply auto
             apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (subst (asm) (2) TM.initial_config_def)
            unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
            by (smt (verit, best) T1'_le_T1 TM.at_least_one_tape' TM.final_le_steps
                TM.init_conf_len TM.run_def TM.run_tapes_non_empty TM.steps_l_tps
                antisym_conv3 diff_Suc_1 diff_less_mono leD length_map length_tl less_one
                less_zeroE linorder_le_less_linear nat.discI nth_map nth_tl trim_tapes_right
                trim_tapes_right_nth_Some' zeroth_is_head)
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
         apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
        apply simp
        apply (subst (1 2) nth_map)
        apply simp
        using M'_tc diff_less apply blast
        apply simp
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>]
          Suc(6) [OF 6(1, 2) \<open>n < length w\<close>, simplified]
        apply (subst M'_def)
        using 6 apply auto
        using linorder_not_less tc_ge_tcf apply blast
        using linorder_not_less tc_ge_tcf apply blast
        apply (subst M'_def)
        apply (simp add: TM_abbrevs.tape_shift.simps)
        using Suc(6) [OF 6(1, 2) \<open>n < length w\<close>, simplified]
        apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
            TM_abbrevs.tape_write_id' diff_less)
        using * Suc(7) [OF 6(3) \<open>n < length w\<close>] apply simp
        by (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
            TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' option.distinct(1)
            tape.sel(2))
    next
      case 7
      have "n < length w" using 7(1) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + n))
                    (TM.initial_config (Abs_TM M') w)))) \<notin> final_states"
        unfolding Suc(1) [simplified, OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! 0 = 0" by (simp add: tc_def)
      have *: "\<And>l n. Suc n < length l \<Longrightarrow> (l ! n)#(rev (take n l)) = rev (take (Suc n) l)"
        by (simp add: take_Suc_conv_app_nth)
      have "w \<noteq> []" using 7(2) by auto
      have **: "right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                (TM.initial_config (Abs_TM M') w)) ! 0) ! n = Some (w ! (Suc n))"
            unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
                of "\<lambda>l. l ! 0", simplified]
            using T1'_final [of w] 7(2) \<open>\<And>w. hd (tapes (trim_tapes
                ((TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))\<close> [of w,
              THEN arg_cong, of right]
            unfolding trim_tapes_def apply auto
            apply (subst (asm) hd_map)
             apply auto
             apply (metis TM.run_def TM.run_tapes_non_empty)
            apply (subst (asm) (2) TM.initial_config_def)
            unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
            by (smt (verit, best) T1'_le_T1 TM.at_least_one_tape' TM.final_le_steps
                TM.init_conf_len TM.run_def TM.run_tapes_non_empty TM.steps_l_tps
                antisym_conv3 diff_Suc_1 diff_less_mono leD length_map length_tl less_one
                less_zeroE linorder_le_less_linear nat.discI nth_map nth_tl trim_tapes_right
                trim_tapes_right_nth_Some' zeroth_is_head)
      have 1: "length (right (tapes ((TM.step M\<^sub>L ^^ T1' w)
               (TM_config (TM.TM.initial_state M\<^sub>L)
               (Tape [] (Some (hd w)) (map Some (tl w)) #
               Tape [] None [] \<up> (TM.TM.tape_count M\<^sub>L - Suc 0)))) ! 0)) \<ge> length w - 1"
      proof -
        have 1: "(TM.step M\<^sub>L ^^ T1' w)
                 (TM_config (TM.TM.initial_state M\<^sub>L) (Tape [] (Some (hd w))
                 (map Some (tl w)) # Tape [] None [] \<up> (TM.TM.tape_count M\<^sub>L - Suc 0))) =
                 (TM.step M\<^sub>L ^^ (T1 (length w) + length w))
                 (TM_config (TM.TM.initial_state M\<^sub>L) (Tape [] (Some (hd w))
                 (map Some (tl w)) # Tape [] None [] \<up> (TM.TM.tape_count M\<^sub>L - Suc 0)))"
          using T1'_final [of w] 3 [of w]
          by (metis (no_types, opaque_lifting) One_nat_def T1'_le_T1 TM.final_mono
              TM.final_steps_rev TM.initial_config_def TM.run_def TM_abbrevs.input_tape_def
              bot_nat_0.extremum_strict list.size(3) that)
        show "length w - 1 \<le> length (right (tapes ((TM.step M\<^sub>L ^^ T1' w)
              (TM_config (TM.TM.initial_state M\<^sub>L) (Tape [] (Some (hd w)) (map Some (tl w)) #
              Tape [] None [] \<up> (TM.TM.tape_count M\<^sub>L - Suc 0)))) ! 0))"
          unfolding 1 using 2 [of w] unfolding trim_tapes_def apply simp
          apply (subst (asm) hd_map)
          apply (metis TM.at_least_one_tape TM.run_tapes_len less_numeral_extra(3)
              list.size(3))
          apply (subst (asm) (4) zeroth_is_head [symmetric])
          apply (metis TM.at_least_one_tape TM.init_conf_len less_numeral_extra(3)
              list.size(3))
          apply (subst (asm) (4) TM.initial_config_def)
          unfolding TM_abbrevs.input_tape_def apply auto
          apply (cases "w = []")
           apply auto
          apply (drule arg_cong [where f=length])
          apply simp
          apply (subst (asm) (4) zeroth_is_head [symmetric])
          apply (metis TM.at_least_one_tape TM.run_tapes_len less_numeral_extra(3)
              list.size(3))
          by (metis One_nat_def TM.initial_config_def TM_abbrevs.input_tape.simps(2)
              length_dropWhile_le length_rev list.collapse)
      qed
      have 2: "length (right (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0))
               > n" using 1 unfolding TM.initial_config_def TM_abbrevs.input_tape_def
        apply auto
        using 7(1) apply simp
        using "7.prems"(2) by auto
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
         apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
        using tc_ge_tcL apply force+
        apply simp
        apply (subst (1 2) nth_map)
         apply (simp add: tc_def)
        unfolding Suc(1) [OF \<open>n < length w\<close>, simplified] apply (subst M'_def)
        apply auto
         apply (subst M'_def)
         apply auto
        using linorder_not_less tc_ge_tcf apply blast
        apply (simp add: TM.run_tapes_len TM.step_l_tps)
        unfolding Suc(7) [OF 7(2) \<open>n < length w\<close>, simplified] apply simp
        unfolding TM_abbrevs.tape_write_def apply simp
         apply (rule tape.expand)
           apply auto
             apply (erule subst)
           apply (rule *)
        unfolding f12 [OF Nat.le_refl, of w, unfolded ML_tapes_def, THEN arg_cong,
            of "\<lambda>l. l ! 0", simplified] apply (subst TM.initial_config_def)
           apply simp
           apply (subst TM_abbrevs.input_tape_def)
           apply auto
        using that apply force
        apply (smt (verit, best) * 1 2 "7.prems"(1) One_nat_def Suc_lessI Suc_less_eq2
            TM.initial_config_def TM_abbrevs.input_tape.simps(2) diff_Suc_1' linorder_not_less
            list.collapse)
          apply (subst Shift_Right_is_right_not_empty)
           apply simp
        using 1 apply (smt (verit, best) "7.prems"(1) One_nat_def Suc_diff_Suc
            TM.initial_config_def TM_abbrevs.input_tape.simps(2) diff_zero
            length_greater_0_conv list.collapse nat_less_le not_less_eq not_less_zero
            order.strict_trans1)
          apply simp
          apply (smt (verit, best) 1 "7.prems"(1,2) One_nat_def Suc_less_eq2
            TM.initial_config_def TM_abbrevs.input_tape.simps(2) add_diff_cancel_left'
            hd_drop_conv_nth le_eq_less_or_eq less_trans_Suc list.collapse list.size(3)
            not_less_zero plus_1_eq_Suc)
         apply (simp add: drop_Suc tl_drop)
        apply (subst M'_def)
        apply auto
        using less_le_not_le tc_ge_tcg apply blast
        apply (rule tape.expand)
        apply auto
        using 2 apply (simp add: TM.init_conf_len TM.step_l_tps TM.steps_l_tps
            f12 [OF Nat.le_refl, of w, unfolded ML_tapes_def, THEN arg_cong,
              of "\<lambda>l. l ! 0", simplified] Suc(7) [OF 7(2) \<open>n < length w\<close>, simplified]
            take_Suc_conv_app_nth)
        apply (subst Shift_Right_is_right_not_empty)
          apply auto
          apply (smt (verit, ccfv_SIG) 1 "7.prems"(1) One_nat_def Suc_less_eq2
            TM.initial_config_def TM_abbrevs.input_tape.simps(2) add_diff_cancel_left'
            less_nat_zero_code less_not_refl list.collapse list.size(3) order.strict_trans1
            plus_1_eq_Suc)
        apply (metis 1 2 "7.prems"(1) One_nat_def Suc_less_eq2[of "Suc n" "length w"]
            TM.initial_config_def[of M\<^sub>L "hd w # tl w"]
            TM_abbrevs.input_tape.simps(2)[of "hd w" "tl w"] add_diff_cancel_left'[of "1"]
            hd_drop_conv_nth[of "Suc n"
              "right (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0)"]
            less_eq_Suc_le[of n
              "length (right (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0))"]
            linorder_not_less[of "Suc n"] list.collapse[of w] list.size(3)
            nat_less_le[of "Suc n"
              "length (right (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0))"]
            not_less_zero[of "Suc (Suc n)"] plus_1_eq_Suc)
          apply (simp add: drop_Suc tl_drop)
        using Suc(7) [OF 7(2) \<open>n < length w\<close>] apply simp
        apply (metis ** TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
            TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' option.distinct(1)
            tape.sel(2))
        using Suc(7) [OF 7(2) \<open>n < length w\<close>] apply simp
        by (metis ** TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
            TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' option.distinct(1)
            tape.sel(2))
    }
  qed
  have f51: "tapes (TM.steps (Abs_TM M') (T1' w + 1 + length w)
             (TM.initial_config (Abs_TM M') w)) ! 0 =
             Tape ((rev (take (length w - 1) (right (tapes
             (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))))@
             [head (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)]@
             left (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0))
             None (drop (length w) (right (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)))" if "w \<noteq> []" for w :: "'a list"
    apply simp
    apply (subst TM.step_def)
    apply auto
    apply (cases "w = []")
    using f41 [of "length w - 1" w] apply simp
      apply (subst (asm) final_states_def)
    unfolding f11 [OF Nat.le_refl, of "[]"]
  proof (simp, rule FalseE)
    assume a1: "state ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                (TM.initial_config (Abs_TM M') w)) \<in> final_states" and
           a2: "w \<noteq> []"
    have 1: "length w - 1 < length w" using a2 by simp
    have 2: "T1' w + 2 + (length w - 1) = T1' w + length w + 1" using a2 by simp
    note 3 = f41 [of "length w - 1" w, OF 1, unfolded 2]
    have 4: "state ((TM.step (Abs_TM M') ^^ (T1' w + length w + 1))
             (TM.initial_config (Abs_TM M') w)) \<in> final_states" using a1
      by (simp add: TM.step_def)
    show False using 4 unfolding 3 final_states_def by simp
  next
    assume a1: "state ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
    have 2: "hd (tapes (trim_tapes ((TM.step M\<^sub>L ^^ (T1' w))
             (TM.initial_config M\<^sub>L w)))) = hd (tapes (TM.initial_config M\<^sub>L w))"
      using 2 T1'_final by (metis T1'_le_T1 TM.final_le_steps TM.run_def)
    have 3: "length w \<noteq> Suc 0 \<Longrightarrow> \<exists>x y t. w = x#y#t" using that
      by (metis length_1_ex_iff remdups_adj.cases)
    have 4: "length w \<noteq> Suc 0 \<Longrightarrow> state ((TM.step (Abs_TM M') ^^ (T1' w + length w))
             (TM.initial_config (Abs_TM M') w)) =
             (4, state (TM.steps M\<^sub>L (T1' w) (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 2, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))), w ! (length w - 2))"
      apply (drule 3)
      using f41 [of "length w - 2" w] by fastforce
    have 5: "length w \<noteq> Suc 0 \<Longrightarrow> T1' w + 2 + (length w - 2) = T1' w + length w"
      using that by (simp add: nat_neq_iff)
    have 6: "length w \<noteq> Suc 0 \<Longrightarrow> tapes ((TM.step (Abs_TM M') ^^ (T1' w + length w))
             (TM.initial_config (Abs_TM M') w)) ! 0 = Tape (rev (take (length w - 2)
             (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0))) @ [head (tapes
             ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0)] @
             left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0))
             (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0) ! (length w - 2))
             (drop (Suc (length w - 2)) (right (tapes
             ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0)))"
      using f47 by (smt (verit) 5 Suc_diff_Suc add_2_eq_Suc' add_diff_cancel_left'
          dual_order.strict_iff_not not_add_less1 not_less_eq)
    have 7: "tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0 =
             tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0"
      using f12 [OF Nat.le_refl, of w, unfolded ML_tapes_def]
      by (metis TM.at_least_one_tape TM.run_def TM.run_tapes_non_empty hd_conv_nth
          hd_take)
    have 8: "\<And>l n. n < length l \<Longrightarrow> l ! n # (rev (take n l)) = rev (take (Suc n) l)"
      by (simp add: take_Suc_conv_app_nth)
    have 9: "length w \<noteq> Suc 0 \<Longrightarrow> Suc (length w - 2) = length w - 1" using that
      by (metis One_nat_def Suc_1 Suc_diff_Suc length_Suc0_not_empty
          nat_less_le)
    have 10: "trimRight None xs = map Some ys \<Longrightarrow> \<exists>n. xs = map Some ys@(replicate n None)"
      for xs :: "'a option list" and ys :: "'a list"
    proof (induction xs arbitrary: ys rule: rev_induct)
      case Nil
      then show ?case by simp
    next
      case (snoc x xs)
      show ?case
      proof (cases x)
        case None
        then show ?thesis using snoc apply auto
          by (metis replicate_Suc replicate_append_same)
      next
        case (Some a)
        then show ?thesis using snoc by simp
      qed
    qed
    have 11: "length (right (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0))
              \<le> length w - Suc 0 \<Longrightarrow> length (right (tapes ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w)) ! 0)) = length w - Suc 0"
      using 2 unfolding trim_tapes_def using T1'_final [of w] apply auto
      apply (subst (asm) hd_map)
       apply auto
       apply (metis TM.run_def TM.run_tapes_non_empty)
      by (smt (verit, ccfv_threshold) 3 One_nat_def TM.at_least_one_tape' TM.init_conf_len
          TM.initial_tapes_non_empty_Cons TM.run_def TM.run_tapes_non_empty diff_Suc_1'
          hd_conv_nth le_antisym le_zero_eq length_Cons length_dropWhile_le length_map
          length_rev list.size(3) not_less_eq tape.sel(3))
    have 12: "\<And>x. x \<in> set (drop (Suc (length w - 2)) (right (tapes ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w)) ! 0))) \<Longrightarrow> x = None"
      using 2 [unfolded trim_tapes_def, THEN arg_cong, of right] apply simp
      apply (subst (asm) hd_map)
       apply (metis TM.run_def TM.run_tapes_non_empty)
      apply simp
      apply (subst (asm) zeroth_is_head)
       apply (metis TM.run_def TM.run_tapes_non_empty)
      apply (rule ccontr)
    proof auto
      fix y :: 'a
      assume a1: "Some y \<in> set (drop (Suc (length w - 2))
                  (right (hd (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))))))" and
             a2: "trimRight None (right (hd (tapes ((TM.step M\<^sub>L ^^ T1' w)
                  (TM.initial_config M\<^sub>L w))))) = right (hd (tapes (TM.initial_config M\<^sub>L w)))"
      have 2: "Some y \<in> set (trimRight None (drop (Suc (length w - 2))
               (right (hd (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))))))"
        using a1 apply auto
        apply (cases "rev (drop (Suc (length w - 2))
                    (right (hd (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))))))")
         apply auto
        by (metis (mono_tags, lifting) dropWhile_append3 in_set_conv_decomp
            option.distinct(1))
      show False using 2 a2 apply (subst (asm) (3) TM.initial_config_def)
        unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
        apply (drule 10)
        by fastforce
    qed
    have 13: "length w \<noteq> Suc 0 \<Longrightarrow> T1' w + 2 + (length w - 2) =
              T1' w + length w" using 5 by blast
    have 14: "length w \<noteq> Suc 0 \<Longrightarrow> heads ((TM.step (Abs_TM M') ^^ (T1' w + length w))
              (TM.initial_config (Abs_TM M') w)) ! 0 = Some (last w)"
    proof -
      assume a1: "length w \<noteq> Suc 0"
      have 1: "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + (length w - 2)))
               (TM.initial_config (Abs_TM M') w)) ! 0 =
               Tape (rev (take (length w - 2) (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0))) @
               [head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)] @
               left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0))
               (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0) ! (length w - 2))
               (drop (Suc (length w - 2)) (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)))"
        using f47 a1 5 6 by argo
      show "heads ((TM.step (Abs_TM M') ^^ (T1' w + length w))
            (TM.initial_config (Abs_TM M') w)) ! 0 = Some (last w)"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding 1 [unfolded 13 [OF a1]] apply simp
        unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
            of "\<lambda>l. l ! 0", simplified]
        apply (subst zeroth_is_head)
         apply (metis TM.run_def TM.run_tapes_non_empty)
        using 2 [unfolded trim_tapes_def, THEN arg_cong, of right] apply simp
        apply (subst (asm) hd_map)
         apply (metis TM.run_def TM.run_tapes_non_empty)
        apply simp
        apply (subst (asm) (2) TM.initial_config_def)
        unfolding TM_abbrevs.input_tape_def apply (simp add: \<open>w \<noteq> []\<close>)
        apply (drule 10)
        apply auto
        by (metis (no_types, lifting) 9 a1 add_diff_cancel_left' add_is_0 last_conv_nth
            last_map last_tl length_map length_tl lessI list.size(3) nat_less_le
            nth_append_left plus_1_eq_Suc)
    qed
    show "map2 TM_abbrevs.tape_action (TM.next_actions (Abs_TM M')
          (state ((TM.step (Abs_TM M') ^^ (T1' w + length w))
          (TM.initial_config (Abs_TM M') w))) (heads ((TM.step (Abs_TM M') ^^
          (T1' w + length w)) (TM.initial_config (Abs_TM M') w))))
          (tapes ((TM.step (Abs_TM M') ^^ (T1' w + length w))
          (TM.initial_config (Abs_TM M') w))) ! 0 =
          Tape (rev (take (length w - Suc 0) (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)) ! 0))) @
          head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)) ! 0) #
          left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)) ! 0)) None
          (drop (length w) (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)) ! 0)))"
      apply (subst nth_map2)
        apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
       apply (metis TM.at_least_one_tape TM.run_tapes_len)
      apply (cases "length w = 1")
       apply auto
      unfolding f21 [simplified] f22 [simplified] TM_abbrevs.tape_action_def
        TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
       apply (subst (1 2) nth_zip)
         apply auto
      unfolding tc_def apply simp_all
       apply (subst M'_def)
       apply auto
        apply (subst (asm) nth_map)
         apply auto
         apply (metis TM.run_def TM.run_tapes_non_empty)
      unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
          of "\<lambda>l. l ! 0", simplified] apply (subst (asm) TM.initial_config_def)
      unfolding TM_abbrevs.input_tape_def using that apply auto
      using 2 apply (smt (verit, best) One_nat_def T1'_le_T1 TM.at_least_one_tape
          TM.final_mono TM.final_steps_rev TM.head_input_None_iff TM.init_conf_len
          TM.initial_config_def TM.run_tapes_len TM_abbrevs.input_tape.simps(2)
          hd_conv_nth length_map less_numeral_extra(3) list.collapse list.map_sel(1)
          list.size(3) trim_tapes_heads)
       apply (subst M'_def)
       apply (simp add: TM_abbrevs.tape_write_def)
       apply (cases "right (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0)")
        apply auto
      unfolding TM_abbrevs.tape_shift.simps apply auto
      apply (metis TM.at_least_one_tape TM.run_tapes_len
          f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
          of "\<lambda>l. l ! 0", simplified] nth_map)
      apply (metis TM.at_least_one_tape TM.run_tapes_len
          f12 [OF Nat.le_refl, unfolded ML_tapes_def, of w, THEN arg_cong,
          of "\<lambda>l. l ! 0", simplified] nth_map)
       apply (subst (asm) (2) zeroth_is_head)
        apply (metis TM.run_def TM.run_tapes_non_empty)
      using 2 unfolding trim_tapes_def apply auto
       apply (subst (asm) hd_map)
        apply (metis TM.run_def TM.run_tapes_non_empty)
       apply simp
      apply (smt (z3) Nil_is_append_conv TM.at_least_one_tape TM.init_conf_len
          TM.initial_config_def TM_abbrevs.input_tape.simps(2) TM_config.sel(2)
          bot_nat_0.not_eq_extremum dropWhile_append3 hd_conv_nth length_0_conv
          length_Suc_conv list.simps(8) nth_Cons_0 rev.simps(1) rev_eq_append_conv
          tape.inject)
      apply (frule 4)
      apply auto
      apply (subst M'_def)
      apply auto
       apply (subst M'_def)
       apply auto
      unfolding TM_abbrevs.tape_write_def
      using tc_ge_tcf apply linarith
       apply (rule tape.expand)
       apply auto
         apply (subst (asm) nth_map)
          apply auto
      apply (metis (no_types, lifting) TM.at_least_one_tape TM.run_tapes_len
          less_numeral_extra(3) list.size(3))
      unfolding 6 apply simp
      unfolding 7 apply auto
           apply (metis (no_types, opaque_lifting) 11 8 9 One_nat_def nat_less_le
          not_less_eq)
          apply (subst (asm) (2) TM.initial_config_def)
      unfolding TM_abbrevs.input_tape_def apply auto
          apply (subst (asm) hd_map)
           apply (metis TM.run_def TM.run_tapes_non_empty)
      using 12 apply (metis head_in_right_tape head_right_empty tape.sel(3))
      apply (metis (no_types, lifting) 9 One_nat_def Suc_pred drop_Suc length_greater_0_conv
          tl_drop)
      apply (cases "drop (Suc (length w - 2)) (right
                    (tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)) ! 0)) = []")
         apply auto
         apply (subst TM_abbrevs.tape_shift.simps)
         apply simp
         apply (subst M'_def)
         apply auto
      using linorder_not_less tc_ge_tcg apply blast
      using linorder_not_less tc_ge_tcg apply blast
          apply (metis (no_types, opaque_lifting) 11 6 7 8 9 One_nat_def
          TM.at_least_one_tape TM.run_tapes_len lessI nth_map tape.sel(2))
         apply (simp_all add: 9)
        apply (subst (asm) hd_map)
         apply auto
         apply (metis TM.run_def TM.run_tapes_non_empty)
        apply (drule arg_cong [where f=right])
        apply simp
        apply (subst (asm) (6) TM.initial_config_def)
      unfolding TM_abbrevs.input_tape_def apply auto
        apply (subst zeroth_is_head)
         apply auto
         apply (metis TM.run_def TM.run_tapes_non_empty)
        apply (subst M'_def)
        apply auto
      using tc_ge_tcg verit_comp_simplify1(3) apply blast
        apply (rule tape.expand)
        apply auto
          apply (erule subst [where s="heads ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                    (TM.initial_config (Abs_TM M') w)) ! 0"])
          apply (subst nth_map)
           apply auto
           apply (metis TM.run_def TM.run_tapes_non_empty)
          apply (subst zeroth_is_head)
           apply auto
           apply (metis TM.run_def TM.run_tapes_non_empty)
      using 6 apply (metis (no_types, opaque_lifting) 7 8 9 One_nat_def TM.run_def
          TM.run_tapes_non_empty hd_conv_nth nat_less_le not_less_eq tape.sel(2))
      using 12 apply (metis 9 One_nat_def head_in_right_tape head_right_empty tape.sel(3))
      apply (metis (no_types, lifting) One_nat_def Suc_diff_1 drop_Suc length_greater_0_conv
          tl_drop)
      apply (subst M'_def)
       apply (auto simp add: TM_abbrevs.tape_shift.simps)
      using linorder_not_less tc_ge_tcf apply blast
          apply (drule 14)
          apply simp
         apply (drule 14)
      by simp
  qed
  have f51': "state ((TM.step (Abs_TM M') ^^ (T1' [] + n + 2))
              (TM.initial_config (Abs_TM M') [])) =
              (2, state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])),
              state ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])),
              TM.TM.initial_state M\<^sub>g, 1, TM.TM.label M\<^sub>L
              (state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L []))), undefined)" and
       f52': "\<And>i. i < tc - TM.tape_count M\<^sub>f \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' [] + n + 2))
              (TM.initial_config (Abs_TM M') [])) ! i =
              tapes ((TM.step (Abs_TM M') ^^ (T1' []))
              (TM.initial_config (Abs_TM M') [])) ! i" and
       f53': "\<And>i. i \<ge> tc - TM.tape_count M\<^sub>f \<Longrightarrow> i < tc \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' [] + n + 2))
              (TM.initial_config (Abs_TM M') [])) ! i =
              tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f []))
              ! (i - (tc - TM.tape_count M\<^sub>f))"
       if "n \<le> T2' []" and "P []" for n :: nat using that
  proof (induction n)
    case 0
    {
      case 1
      then show ?case using f31' [OF that(2)] by (simp add: TM.initial_config_def)
    next
      case 2
      then show ?case using f32' [OF that(2)] by simp
    next
      case 3
      then show ?case apply simp
        unfolding f32' [OF that(2), simplified]
        using f13 [OF Nat.le_refl, of i "[]"]
        by (smt (verit, best) M'_final_states Nat.add_diff_assoc TM.init_conf_len
            TM.initial_tapes_empty TM.initial_tapes_non_empty_Nil a7 add_diff_inverse_nat
            diff_self_eq_0 dual_order.trans le_add1 le_eq_less_or_eq linorder_not_less
            local.initial_state_def max.cobounded1 nat_add_left_cancel_less
            nat_minus_add_max tc_def zero_less_diff)
    }
  next
    case (Suc n)
    {
      case 1
      have "n \<le> T2' []" using 1(1) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))) \<notin> final_states"
        using Suc(1) [OF \<open>n \<le> T2' []\<close> 1(2)] apply simp
        unfolding final_states_def apply auto
        using 1(1) T2'_min [of n "[]"]
        by (metis Suc_n_not_le_n TM.run_def \<open>n \<le> T2' []\<close> is_finalI le_neq_implies_less)
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding Suc(1) [OF \<open>n \<le> T2' []\<close> 1(2), simplified] apply (subst M'_def)
        apply auto
        apply (subst (3) TM.step_def)
        apply auto
        apply (metis "1.prems"(1) Suc_n_not_le_n T2'_min TM.run_def \<open>n \<le> T2' []\<close> is_finalI
            le_neq_implies_less)
        apply (rule arg_cong [where f="TM.next_state M\<^sub>f
          (state ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])))"])
      proof (rule nth_equalityI', auto)
        show "length (Mf_heads (heads (TM.step (Abs_TM M') (TM.step (Abs_TM M')
              ((TM.step (Abs_TM M') ^^ (T1' [] + n))
              (TM.initial_config (Abs_TM M') [])))))) = length (tapes ((TM.step M\<^sub>f ^^ n)
              (TM.initial_config M\<^sub>f [])))" unfolding Mf_heads_def
          by (simp add: TM.run_tapes_len TM.step_l_tps tc_ge_tcf)
      next
        fix i :: nat
        assume a1: "state ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])) \<notin>
                    TM.TM.final_states M\<^sub>f" and
               a2: "i < length (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])))" and
               a3: "length (Mf_heads (heads (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))))) =
                    length (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])))"
        have 1: "Mf_heads (heads (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                 (TM.initial_config (Abs_TM M') []))))) ! i =
                 heads (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                 (TM.initial_config (Abs_TM M') [])))) ! (i + (tc - TM.tape_count M\<^sub>f))"
          unfolding Mf_heads_def using a2 [folded a3, unfolded Mf_heads_def] apply simp
          unfolding rev_take by (simp add: TM.run_tapes_len TM.step_l_tps add.commute)
        show "Mf_heads (heads (TM.step (Abs_TM M') (TM.step (Abs_TM M')
              ((TM.step (Abs_TM M') ^^ (T1' [] + n))
              (TM.initial_config (Abs_TM M') []))))) ! i =
              head (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])) ! i)"
          unfolding 1 using Suc(3) [of "i + (tc - TM.TM.tape_count M\<^sub>f)",
              OF _ _ \<open>n \<le> T2' []\<close> \<open>P []\<close>] a2 a3 apply simp
          by (smt (verit, ccfv_SIG) M'_tc TM.run_tapes_len TM.step_l_tps
              add_diff_inverse_nat add_less_cancel_right linorder_not_less nat_less_le
              nth_map tc_ge_tcf)
      qed
    next
      case 2
      have "n \<le> T2' []" using 2(2) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))) \<notin> final_states"
        using Suc(1) [OF \<open>n \<le> T2' []\<close> 2(3)] apply simp
        unfolding final_states_def apply auto
        using 2(2) T2'_min [of n "[]"]
        by (metis Suc_n_not_le_n TM.run_def \<open>n \<le> T2' []\<close> is_finalI le_neq_implies_less)
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis "2.prems"(1) M'_tc TM.next_actions_simps(2) add_lessD1 less_diff_conv)
        apply (metis "2.prems"(1) M'_tc TM.run_tapes_len TM.step_l_tps add_lessD1
            less_diff_conv)
        unfolding Suc(1) [OF \<open>n \<le> T2' []\<close> 2(3), simplified] TM.next_actions_def
          TM.next_writes_def TM.next_moves_def TM_abbrevs.tape_action_def apply simp
        apply (subst (1 2) nth_zip)
        using "2.prems"(1) apply auto
        apply (subst M'_def)
        apply auto
        apply (subst M'_def)
        apply auto
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len TM.step_l_tps)
        unfolding Suc(2) [OF _ \<open>n \<le> T2' []\<close> 2(3), simplified] TM_abbrevs.tape_shift.simps
        TM_abbrevs.tape_write_def by simp
    next
      case 3
      have "n \<le> T2' []" using 3(3) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))) \<notin> final_states"
        using Suc(1) [OF \<open>n \<le> T2' []\<close> 3(4)] apply simp
        unfolding final_states_def apply auto
        using 3(3) T2'_min [of n "[]"]
        by (metis Suc_n_not_le_n TM.run_def \<open>n \<le> T2' []\<close> is_finalI le_neq_implies_less)
      have 1: "tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' [] + n))
               (TM.initial_config (Abs_TM M') [])))) ! i =
               tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])) !
               (i - (tc - TM.tape_count M\<^sub>f))" using Suc(3) [OF 3(1, 2) \<open>n \<le> T2' []\<close> 3(4)]
        by simp
      have [simp]: "[0..<TM.TM.tape_count M\<^sub>f] ! (i - (tc - TM.TM.tape_count M\<^sub>f)) =
                    i - (tc - TM.TM.tape_count M\<^sub>f)"
        by (metis "3.prems"(1,2) add_diff_inverse_nat less_diff_conv2 nth_upt
            order_less_asym' plus_nat.add_0 tc_ge_tcf)
      have 2: "Mf_heads (heads (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' [] + n))
               (TM.initial_config (Abs_TM M') []))))) =
               heads ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f []))"
        unfolding Mf_heads_def apply (rule nth_equalityI')
         apply auto
         apply (simp add: TM.run_tapes_len TM.step_l_tps tc_ge_tcf)
      proof -
        fix i :: nat
        assume a1: "min (length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))))) (TM.TM.tape_count M\<^sub>f) =
                    length (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])))" and
               a2: "i < length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))))" and
               a3: "i < TM.TM.tape_count M\<^sub>f"
        have 1: "\<And>l i. i < length l \<Longrightarrow> (rev l) ! i = l ! (length l - i - 1)"
          using rev_nth by fastforce
        have 2: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                 (TM.initial_config (Abs_TM M') []))))) = tc"
          using M'_tc TM.run_tapes_len TM.step_l_tps by blast
        have 4: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                 (TM.initial_config (Abs_TM M') []))))) - Suc (min (length (tapes
                 (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                 (TM.initial_config (Abs_TM M') [])))))) (TM.TM.tape_count M\<^sub>f) - Suc i) =
                 tc + i - TM.tape_count M\<^sub>f" unfolding 2 tc_def using a3 by simp
        show "rev (take (TM.TM.tape_count M\<^sub>f) (rev (heads (TM.step (Abs_TM M')
              (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + n))
              (TM.initial_config (Abs_TM M') []))))))) ! i =
              head (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f [])) ! i)"
          apply (subst 1)
           apply auto
          using a2 apply blast
           apply fact
          apply (subst nth_take)
           apply (simp add: TM.run_tapes_len a1)
          apply (subst 1)
           apply auto
           apply (simp add: TM.run_tapes_len TM.step_l_tps less_imp_diff_less tc_ge_tcf)
          unfolding 4
          apply (cases "(tc + i - TM.TM.tape_count M\<^sub>f) < tc - TM.tape_count M\<^sub>f")
           apply linarith
          using Suc(3) [of "tc + i - TM.tape_count M\<^sub>f"] 3
          by (simp add: 2 a3 less_diff_conv2 less_imp_le_nat tc_ge_tcf trans_le_add1)
      qed
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis "3.prems"(2) M'_tc TM.next_actions_simps(2))
         apply (simp add: "3.prems"(2) TM.init_conf_len TM.step_l_tps TM.steps_l_tps)
        unfolding Suc(1) [OF \<open>n \<le> T2' []\<close> 3(4), simplified] TM_abbrevs.tape_action_def
          TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply (simp_all add: "3.prems"(2))
        apply (subst M'_def)
        apply auto
        unfolding 1 apply (subst (5) TM.step_def)
         apply auto
          apply (metis "3.prems"(3) T2'_min TM.run_def is_finalI less_eq_Suc_le)
         apply (subst nth_map2)
           apply (metis "3.prems"(2) TM.next_actions_simps(2) diff_diff_cancel
            diff_less_mono nless_le tc_ge_tcf)
          apply (metis "3.prems"(2) TM.run_tapes_len add_diff_inverse_nat linorder_not_less
            max.absorb3 nat_add_left_cancel_less nat_minus_add_max tc_ge_tcf)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply (subst (1 2) nth_zip)
           apply (metis "3.prems"(2) diff_diff_cancel diff_less_mono diff_zero length_map
            length_upt nat_less_le tc_ge_tcf)
        using "3.prems"(2) apply fastforce
         apply simp
         apply (subst (1 2) nth_map)
          apply auto
        using "3.prems"(2) apply linarith
         apply (subst (5) M'_def)
        apply auto
        unfolding 2
        using Nat.diff_diff_right nat_less_le tc_ge_tcf apply presburger
        apply (subst M'_def)
        apply auto
        apply (subst (3) TM.step_def)
        apply auto
        using "3.prems"(1) apply blast
        apply (subst nth_map2)
          apply auto
        using "3.prems"(1) by blast+
    }
  qed
  have f51'': "state ((TM.step (Abs_TM M') ^^ (T1' [] + n + 2))
               (TM.initial_config (Abs_TM M') [])) =
               (3, state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])),
               TM.TM.initial_state M\<^sub>f, state ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g [])),
               1, TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L []))),
               undefined)" and
       f52'': "\<And>i. i < tc - TM.tape_count M\<^sub>g \<Longrightarrow>
               tapes ((TM.step (Abs_TM M') ^^ (T1' [] + n + 2))
               (TM.initial_config (Abs_TM M') [])) ! i =
               tapes ((TM.step (Abs_TM M') ^^ (T1' []))
               (TM.initial_config (Abs_TM M') [])) ! i" and
       f53'': "\<And>i. i \<ge> tc - TM.tape_count M\<^sub>g \<Longrightarrow> i < tc \<Longrightarrow>
               tapes ((TM.step (Abs_TM M') ^^ (T1' [] + n + 2))
               (TM.initial_config (Abs_TM M') [])) ! i =
               tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g []))
               ! (i - (tc - TM.tape_count M\<^sub>g))"
       if "n \<le> T3' []" and "\<not>P []" for n :: nat using that
  proof (induction n)
    case 0
    {
      case 1
      then show ?case using f31'' [OF 1(2)] by (simp add: TM.init_conf_state)
    next
      case 2
      then show ?case using f32'' [OF 2(3)] by simp
    next
      case 3
      then show ?case using f32'' [OF 3(4)] apply simp
        by (smt (verit, best) Nat.add_diff_assoc TM.init_conf_len TM.initial_tapes_empty
            TM.initial_tapes_non_empty_Nil add_implies_diff diff_le_self diff_self_eq_0
            dual_order.trans f13 le_add_diff_inverse less_diff_iff linorder_not_less
            max_def nless_le tc_def)
    }
  next
    case (Suc n)
    {
      case 1
      have "n \<le> T3' []" using 1(1) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))) \<notin> final_states"
        using Suc(1) [OF \<open>n \<le> T3' []\<close> 1(2)] apply simp
        unfolding final_states_def apply auto
        using 1(1) T3'_min [of n "[]"]
        by (metis Suc_n_not_le_n TM.run_def \<open>n \<le> T3' []\<close> is_finalI le_neq_implies_less)
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding Suc(1) [OF \<open>n \<le> T3' []\<close> 1(2), simplified] apply (subst M'_def)
        apply auto
        apply (subst (3) TM.step_def)
        apply auto
         apply (metis "1.prems"(1) T3'_min TM.run_def is_finalI less_eq_Suc_le)
        apply (rule arg_cong [where f="TM.TM.next_state M\<^sub>g (state ((TM.step M\<^sub>g ^^ n)
            (TM.initial_config M\<^sub>g [])))"])
        unfolding Mg_heads_def apply (rule nth_equalityI')
         apply auto
         apply (simp add: TM.run_tapes_len TM.step_l_tps tc_ge_tcg)
        apply (subst rev_nth)
         apply auto
        apply (subst rev_nth)
         apply auto
      proof -
        fix i :: nat
        assume a1: "state ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g [])) \<notin>
                    TM.TM.final_states M\<^sub>g" and
               a2: "min (length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))))) (TM.TM.tape_count M\<^sub>g) =
                    length (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g [])))" and
               a3: "i < length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))))" and
               a4: "i < TM.TM.tape_count M\<^sub>g"
        have 2: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                 ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                 (TM.initial_config (Abs_TM M') []))))) + i -
                 length (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g []))) =
                 tc + i - TM.tape_count M\<^sub>g"
          by (simp add: TM.run_tapes_len TM.step_l_tps)
        show "head (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
              ((TM.step (Abs_TM M') ^^ (T1' [] + n)) (TM.initial_config (Abs_TM M') [])))) !
              (length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
              ((TM.step (Abs_TM M') ^^ (T1' [] + n))
              (TM.initial_config (Abs_TM M') []))))) + i -
              length (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g []))))) =
              head (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g [])) ! i)"
          unfolding 2 apply (subst Suc(3) [OF _ _ \<open>n \<le> T3' []\<close> 1(2), simplified])
            apply auto
          using a4 tc_ge_tcf apply linarith
          using a4 tc_ge_tcg by force
      qed
    next
      case 2
      have "n \<le> T3' []" using 2(2) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))) \<notin> final_states"
        using Suc(1) [OF \<open>n \<le> T3' []\<close> 2(3)] apply simp
        unfolding final_states_def apply auto
        using 2(2) T3'_min [of n "[]"]
        by (metis Suc_n_not_le_n TM.run_def \<open>n \<le> T3' []\<close> is_finalI le_neq_implies_less)
      have [simp]: "[0..<tc] ! i = i" using "2.prems"(1) by fastforce
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis "2.prems"(1) M'_tc TM.next_actions_simps(2) diff_le_self
            dual_order.strict_trans linorder_cases order.strict_iff_not)
        apply (metis "2.prems"(1) M'_tc TM.run_tapes_len TM.step_l_tps add_lessD1
            less_diff_conv)
        unfolding Suc(1) [OF \<open>n \<le> T3' []\<close> 2(3), simplified]
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
        using "2.prems"(1) apply auto
        apply (subst M'_def)
        apply (simp add: TM_abbrevs.tape_shift.simps)
        apply (subst M'_def)
        apply (simp add: TM_abbrevs.tape_write_def)
        unfolding Suc(2) [OF _ \<open>n \<le> T3' []\<close> 2(3), simplified]
        by (simp add: TM.run_tapes_len TM.step_l_tps
            Suc(2) [OF _ \<open>n \<le> T3' []\<close> 2(3), simplified])
    next
      case 3
      have "n \<le> T3' []" using 3(3) by simp
      have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))) \<notin> final_states"
        using Suc(1) [OF \<open>n \<le> T3' []\<close> 3(4)] apply simp
        unfolding final_states_def apply auto
        using 3(3) T3'_min [of n "[]"]
        by (metis Suc_n_not_le_n TM.run_def \<open>n \<le> T3' []\<close> is_finalI le_neq_implies_less)
      have [simp]: "[0..<tc] ! i = i" using "3.prems"(2) by fastforce
      have 1: "Mg_heads (heads (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' [] + n))
               (TM.initial_config (Abs_TM M') []))))) =
               heads ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g []))"
        unfolding Mg_heads_def apply (subst nth_equalityI')
          apply auto
         apply (simp add: TM.run_tapes_len TM.step_l_tps tc_ge_tcg)
      proof -
        fix i :: nat
        assume a1: "min (length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') []))))))
                    (TM.TM.tape_count M\<^sub>g) = length (tapes ((TM.step M\<^sub>g ^^ n)
                    (TM.initial_config M\<^sub>g [])))" and
               a2: "i < length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                    (TM.initial_config (Abs_TM M') [])))))" and
               a3: "i < TM.TM.tape_count M\<^sub>g"
        have [simp]: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                      ((TM.step (Abs_TM M') ^^ (T1' [] + n))
                      (TM.initial_config (Abs_TM M') []))))) = tc"
          using M'_tc TM.run_tapes_len TM.step_l_tps by blast
        show "rev (take (TM.TM.tape_count M\<^sub>g) (rev (heads (TM.step (Abs_TM M')
              (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' [] + n))
              (TM.initial_config (Abs_TM M') []))))))) ! i =
              head (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g [])) ! i)"
          unfolding rev_take apply simp
          using Suc(3) [of "tc - TM.TM.tape_count M\<^sub>g + i", OF _ _ \<open>n \<le> T3' []\<close> 3(4)]
          a3 apply simp
          using tc_def by auto
      qed
      have [simp]: "[0..<TM.TM.tape_count M\<^sub>g] ! (i - (tc - TM.TM.tape_count M\<^sub>g)) =
                    i - (tc - TM.TM.tape_count M\<^sub>g)"
        by (metis "3.prems"(1,2) add_0 add_diff_inverse_nat dual_order.asym less_diff_conv2
            nth_upt tc_ge_tcg)
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (simp add: "3.prems"(2) TM.next_actions_simps(2))
         apply (simp add: "3.prems"(2) TM.run_tapes_len TM.step_l_tps)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
          apply fact+
        apply (subst (1 2) nth_map)
         apply simp
         apply fact
        unfolding Suc(1) [OF \<open>n \<le> T3' []\<close> 3(4), simplified] apply (subst M'_def)
        apply auto
        unfolding 1 apply (subst M'_def)
         apply (auto simp add: 1)
        unfolding Suc(3) [OF 3(1, 2) \<open>n \<le> T3' []\<close> 3(4), simplified]
         apply (subst TM.step_def)
         apply auto
        apply (metis "3.prems"(3) T3'_min TM.run_def is_finalI linorder_not_less
            not_less_eq_eq)
         apply (subst nth_map2)
        apply (metis "3.prems"(2) TM.next_actions_simps(2) diff_diff_cancel diff_less_mono
            less_or_eq_imp_le tc_ge_tcg)
        apply (metis "3.prems"(2) TM.run_tapes_len add_diff_inverse_nat dual_order.asym
            less_diff_conv2 tc_ge_tcg)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def
          TM.next_writes_def apply (subst (1 2) nth_zip)
        using "3.prems"(2) apply fastforce+
         apply (subst (1 2) nth_map)
        apply (metis "3.prems"(2) add_diff_inverse_nat diff_zero dual_order.asym length_upt
            less_diff_conv2 tc_ge_tcg)
         apply simp
        using "3.prems"(2) less_diff_conv2 tc_ge_tcg apply simp
        using "3.prems"(1) by argo
    }
  qed
  have function_Nil: "TM.computes_word (Abs_TM M') [] (if P [] then f [] else g [])"
    unfolding TM.computes_word_def apply auto
  proof -
    have 1: "(2, state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])),
             state ((TM.step M\<^sub>f ^^ T2' []) (TM.initial_config M\<^sub>f [])),
             TM.TM.initial_state M\<^sub>g, 1, TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' [])
             (TM.initial_config M\<^sub>L []))), undefined) \<in> final_states"
      unfolding final_states_def states_def apply auto
      using T1'_final [of "[]"]
        apply (simp add: TM.final_states_valid TM.is_final_def TM.run_def)
      using T2'_final [of "[]"]
      by (simp_all add: TM.final_states_valid TM.is_final_def TM.run_def)
    have 2: "(3, state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])),
             TM.TM.initial_state M\<^sub>f, state ((TM.step M\<^sub>g ^^ T3' [])
             (TM.initial_config M\<^sub>g [])), 1, TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' [])
             (TM.initial_config M\<^sub>L []))), undefined) \<in> final_states"
      unfolding final_states_def states_def apply auto
      using T1'_final [of "[]"]
        apply (simp add: TM.final_states_valid TM.is_final_def TM.run_def)
      using T3'_final [of "[]"]
      by (simp_all add: TM.final_states_valid TM.is_final_def TM.run_def)
    show "TM.halts (Abs_TM M') []"
      apply (cases "P []")
      unfolding TM.halts_def TM.halts_config_def using f51' [OF Nat.le_refl] 1 apply simp
       apply (metis M'_final_states One_nat_def f51' [OF Nat.le_refl] is_finalI)
      using f51'' [OF Nat.le_refl] 2 apply simp
      by (metis M'_final_states One_nat_def f51'' [OF Nat.le_refl] is_finalI)
  next
    assume "P []"
    have 1: "(if TM.clean_output (TM.compute M\<^sub>f []) then
             Some (TM.output_of (TM.compute M\<^sub>f [])) else None) = Some (f []) \<Longrightarrow>
             TM.clean_output (TM.compute M\<^sub>f []) \<Longrightarrow> TM.output_of (TM.compute M\<^sub>f []) = f []"
      by simp
    have 2: "TM.clean_output (TM.compute M\<^sub>f [])"
      by (metis TM.clean_output_of_def TM.computes_def TM.computes_word_def
          TM.has_output_def a5 option.distinct(1))
    have 3: "(LEAST n. TM.is_final M\<^sub>f ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f []))) =
             T2' []" using T2'_final T2'_min by (simp add: Least_natI TM.run_def)
    have 4: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
             (TM.initial_config (Abs_TM M') []))) = T1' [] + 2 + T2' []"
      apply standard
       apply auto
      unfolding TM.is_final_def using f51' [OF Nat.le_refl \<open>P []\<close>] apply simp
      unfolding final_states_def states_def apply auto
         apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
        apply (metis T2'_final TM.final_states_valid TM.is_final_def TM.run_def)
       apply (metis T2'_final TM.run_def is_finalD)
    proof -
      fix n :: nat
      assume a1: "n < Suc (Suc (T1' [] + T2' []))" and
             a2: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') []))
                  \<in> final_states"
      note f51' [OF _ \<open>P []\<close>]
      show False
      proof (cases "T2' [] = 0")
        case True
        hence 1: "n < Suc (Suc (T1' []))" using a1 unfolding True by simp
        have 2: "state ((TM.step (Abs_TM M') ^^ (Suc (T1' [])))
                 (TM.initial_config (Abs_TM M') [])) \<notin> final_states"
          unfolding f21 unfolding final_states_def states_def by simp
        show ?thesis using 1 a2 2
          by (metis (no_types, lifting) M'_final_states TM.final_mono is_finalD is_finalI
              less_Suc_eq_le)
      next
        case False
        have 0: "T1' [] + (T2' [] - 1) + 2 = T1' [] + T2' [] + 1" using False by simp
        have "state ((TM.step (Abs_TM M') ^^ (Suc (T1' [] + T2' [])))
              (TM.initial_config (Abs_TM M') [])) \<notin> final_states"
          using f51' [of "T2' [] - 1", OF _ \<open>P []\<close>, unfolded 0] apply simp
          unfolding final_states_def states_def apply auto
          by (metis False Suc_pred T2'_min TM.is_final_def TM.run_def lessI not_gr_zero)
        then show ?thesis using a1 a2
          by (metis (no_types, lifting) M'_final_states TM.final_mono is_finalD is_finalI
              less_Suc_eq_le)
      qed
    qed
    have 5: "tc - TM.TM.tape_count M\<^sub>f \<le> tc - Suc 0"
      by (simp add: Suc_leI diff_le_mono2)
    have 6: "tc - Suc 0 < tc" unfolding tc_def by simp
    have [simp]: "length (tapes ((TM.step M\<^sub>f ^^ T2' []) (TM.initial_config M\<^sub>f []))) =
                  TM.tape_count M\<^sub>f" using TM.run_tapes_len by blast
    have 7: "head (last (tapes ((TM.step M\<^sub>f ^^ T2' []) (TM.initial_config M\<^sub>f [])))) =
             head (last (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
             ((TM.step (Abs_TM M') ^^ (T1' [] + T2' []))
             (TM.initial_config (Abs_TM M') []))))))"
      apply (subst last_conv_nth)
       apply (metis TM.run_def TM.run_tapes_non_empty)
      apply simp
      using f53' [OF Nat.le_refl \<open>P []\<close>, of "tc - 1", simplified, OF 5 6]
      by (smt (verit, del_insts) M'_tc One_nat_def TM.run_tapes_len TM.step_l_tps
          add_diff_cancel_left' diff_zero last_conv_nth list.size(3) max.absorb3
          max_nat.eq_neutr_iff minus_nat.simps(2) nat_less_le nat_minus_add_max tc_ge_tcf)
    show "TM.has_output (TM.compute (Abs_TM M') []) (f [])" unfolding TM.has_output_def
        TM.clean_output_of_def apply auto
      unfolding TM.output_of_def Let_def
      using a5 [unfolded TM.computes_def, THEN spec, of "[]", unfolded TM.computes_word_def,
          THEN conjunct2, unfolded TM.has_output_def TM.clean_output_of_def, THEN 1, OF 2,
          unfolded TM.output_of_def Let_def]
      unfolding TM.compute_def TM.compute_config_def 3
      using f53' [OF Nat.le_refl, of "tc - 1", simplified, OF \<open>P []\<close>, simplified, OF 5 6]
      unfolding 4 apply auto
      unfolding 7 [symmetric]
       apply (cases "head (last (tapes ((TM.step M\<^sub>f ^^ T2' []) (TM.initial_config M\<^sub>f []))))")
        apply auto
      apply (smt (verit, best) M'_tc One_nat_def TM.at_least_one_tape TM.run_tapes_len
          TM.step_l_tps add_diff_cancel_right last_conv_nth le_add_diff_inverse list.size(3)
          nat_less_le plus_1_eq_Suc tc_ge_tcf)
      unfolding TM.clean_output_def
    proof (rule exI [where x="f []"])
      note 1 = f53' [OF Nat.le_refl \<open>P []\<close> 5 6, simplified]
      have 2: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' [] + T2' []))
               (TM.initial_config (Abs_TM M') []))))) = tc"
        using M'_tc TM.run_tapes_len TM.step_l_tps by blast
      have [simp]: "tapes ((TM.step M\<^sub>f ^^ T2' []) (TM.initial_config M\<^sub>f [])) !
                    (tc - Suc (tc - TM.TM.tape_count M\<^sub>f)) =
                    last (tapes ((TM.step M\<^sub>f ^^ T2' []) (TM.initial_config M\<^sub>f [])))"
        by (metis One_nat_def TM.run_def TM.run_tapes_len TM.run_tapes_non_empty
            diff_diff_cancel diff_zero dual_order.strict_trans2 last_conv_nth less_not_refl
            minus_nat.simps(2) nle_le tc_ge_tcf)
      have 3: "(if TM.clean_output (TM.compute M\<^sub>f []) then
               Some (TM.output_of (TM.compute M\<^sub>f [])) else None) = Some (f []) \<Longrightarrow>
               TM.output_of (TM.compute M\<^sub>f []) = f []"
        by (meson option.distinct(1) option.inject)
      show "last (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
            ((TM.step (Abs_TM M') ^^ (T1' [] + T2' []))
            (TM.initial_config (Abs_TM M') []))))) = TM_abbrevs.input_tape (f [])"
        apply (subst last_conv_nth)
         apply auto
        apply (metis M'_tc TM.run_tapes_len TM.step_l_tps list.size(3) not_less_zero
            tc_ge_tcf)
        unfolding 2 unfolding 1 apply simp
        using a5 [unfolded TM.computes_def, THEN spec, of "[]",
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.clean_output_of_def, THEN 3, unfolded TM.output_of_def Let_def]
        by (metis T2'_final TM.computes_def TM.computes_word_def TM.final_run_compute
            TM.has_output_altdef TM.run_def a5)
    qed
  next
    assume "\<not>P []"
    have 1: "(if TM.clean_output (TM.compute M\<^sub>g []) then
             Some (TM.output_of (TM.compute M\<^sub>g [])) else None) = Some (g []) \<Longrightarrow>
             TM.clean_output (TM.compute M\<^sub>g []) \<Longrightarrow> TM.output_of (TM.compute M\<^sub>g []) = g []"
      by simp
    have 2: "TM.clean_output (TM.compute M\<^sub>g [])"
      by (metis TM.clean_output_of_def TM.computes_def TM.computes_word_def
          TM.has_output_def a8 option.distinct(1))
    have 3: "(LEAST n. TM.is_final M\<^sub>g ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g []))) =
             T3' []" using T3'_final T3'_min by (simp add: Least_natI TM.run_def)
    have 4: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
             (TM.initial_config (Abs_TM M') []))) = T1' [] + 2 + T3' []"
      apply standard
       apply auto
      unfolding TM.is_final_def using f51'' [OF Nat.le_refl \<open>\<not>P []\<close>] apply simp
      unfolding final_states_def states_def apply auto
         apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
        apply (metis T3'_final TM.final_states_valid TM.is_final_def TM.run_def)
       apply (metis T3'_final TM.run_def is_finalD)
    proof -
      fix n :: nat
      assume a1: "n < Suc (Suc (T1' [] + T3' []))" and
             a2: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') []))
                  \<in> final_states"
      note f51'' [OF _ \<open>\<not>P []\<close>]
      show False
      proof (cases "T3' [] = 0")
        case True
        hence 1: "n < Suc (Suc (T1' []))" using a1 unfolding True by simp
        have 2: "state ((TM.step (Abs_TM M') ^^ (Suc (T1' [])))
                 (TM.initial_config (Abs_TM M') [])) \<notin> final_states"
          unfolding f21 unfolding final_states_def states_def by simp
        show ?thesis using 1 a2 2
          by (metis (no_types, lifting) M'_final_states TM.final_mono is_finalD is_finalI
              less_Suc_eq_le)
      next
        case False
        have 0: "T1' [] + (T3' [] - 1) + 2 = T1' [] + T3' [] + 1" using False by simp
        have "state ((TM.step (Abs_TM M') ^^ (Suc (T1' [] + T3' [])))
              (TM.initial_config (Abs_TM M') [])) \<notin> final_states"
          using f51'' [of "T3' [] - 1", OF _ \<open>\<not>P []\<close>, unfolded 0] apply simp
          unfolding final_states_def states_def apply auto
          by (metis False Suc_pred T3'_min TM.is_final_def TM.run_def lessI not_gr_zero)
        then show ?thesis using a1 a2
          by (metis (no_types, lifting) M'_final_states TM.final_mono is_finalD is_finalI
              less_Suc_eq_le)
      qed
    qed
    have 5: "tc - TM.TM.tape_count M\<^sub>g \<le> tc - Suc 0"
      by (simp add: Suc_leI diff_le_mono2)
    have 6: "tc - Suc 0 < tc" unfolding tc_def by simp
    have [simp]: "length (tapes ((TM.step M\<^sub>g ^^ T2' []) (TM.initial_config M\<^sub>g []))) =
                  TM.tape_count M\<^sub>g" using TM.run_tapes_len by blast
    have 7: "head (last (tapes ((TM.step M\<^sub>g ^^ T3' []) (TM.initial_config M\<^sub>g [])))) =
             head (last (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
             ((TM.step (Abs_TM M') ^^ (T1' [] + T3' []))
             (TM.initial_config (Abs_TM M') []))))))"
      apply (subst last_conv_nth)
       apply (metis TM.run_def TM.run_tapes_non_empty)
      apply simp
      using f53'' [OF Nat.le_refl \<open>\<not>P []\<close>, of "tc - 1", simplified, OF 5 6]
      by (smt (verit, del_insts) M'_tc One_nat_def TM.run_tapes_len TM.step_l_tps
          add_diff_cancel_left' diff_zero last_conv_nth list.size(3) max.absorb3
          max_nat.eq_neutr_iff minus_nat.simps(2) nat_less_le nat_minus_add_max tc_ge_tcg)
    show "TM.has_output (TM.compute (Abs_TM M') []) (g [])" unfolding TM.has_output_def
        TM.clean_output_of_def apply auto
      unfolding TM.output_of_def Let_def
      using a8 [unfolded TM.computes_def, THEN spec, of "[]", unfolded TM.computes_word_def,
          THEN conjunct2, unfolded TM.has_output_def TM.clean_output_of_def, THEN 1, OF 2,
          unfolded TM.output_of_def Let_def]
      unfolding TM.compute_def TM.compute_config_def 3
      using f53'' [OF Nat.le_refl, of "tc - 1", simplified, OF \<open>\<not>P []\<close>, simplified, OF 5 6]
      unfolding 4 apply auto
      unfolding 7 [symmetric]
       apply (cases "head (last (tapes ((TM.step M\<^sub>g ^^ T3' []) (TM.initial_config M\<^sub>g []))))")
        apply auto
      apply (smt (verit, best) M'_tc One_nat_def TM.at_least_one_tape TM.run_tapes_len
          TM.step_l_tps add_diff_cancel_right last_conv_nth le_add_diff_inverse list.size(3)
          nat_less_le plus_1_eq_Suc tc_ge_tcg)
      unfolding TM.clean_output_def
    proof (rule exI [where x="g []"])
      note 1 = f53'' [OF Nat.le_refl \<open>\<not>P []\<close> 5 6, simplified]
      have 2: "length (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
               ((TM.step (Abs_TM M') ^^ (T1' [] + T3' []))
               (TM.initial_config (Abs_TM M') []))))) = tc"
        using M'_tc TM.run_tapes_len TM.step_l_tps by blast
      have [simp]: "tapes ((TM.step M\<^sub>g ^^ T3' []) (TM.initial_config M\<^sub>g [])) !
                    (tc - Suc (tc - TM.TM.tape_count M\<^sub>g)) =
                    last (tapes ((TM.step M\<^sub>g ^^ T3' []) (TM.initial_config M\<^sub>g [])))"
        by (metis One_nat_def TM.run_def TM.run_tapes_len TM.run_tapes_non_empty
            diff_diff_cancel diff_zero dual_order.strict_trans2 last_conv_nth less_not_refl
            minus_nat.simps(2) nle_le tc_ge_tcg)
      have 3: "(if TM.clean_output (TM.compute M\<^sub>g []) then
               Some (TM.output_of (TM.compute M\<^sub>g [])) else None) = Some (g []) \<Longrightarrow>
               TM.output_of (TM.compute M\<^sub>g []) = g []"
        by (meson option.distinct(1) option.inject)
      show "last (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
            ((TM.step (Abs_TM M') ^^ (T1' [] + T3' []))
            (TM.initial_config (Abs_TM M') []))))) = TM_abbrevs.input_tape (g [])"
        apply (subst last_conv_nth)
         apply auto
        apply (metis M'_tc TM.run_tapes_len TM.step_l_tps list.size(3) not_less_zero
            tc_ge_tcg)
        unfolding 2 unfolding 1 apply simp
        using a8 [unfolded TM.computes_def, THEN spec, of "[]",
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.clean_output_of_def, THEN 3, unfolded TM.output_of_def Let_def]
        by (metis T3'_final TM.computes_def TM.computes_word_def TM.final_run_compute
            TM.has_output_altdef TM.run_def a8)
    qed
    have 1: "(2, state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])),
             state ((TM.step M\<^sub>f ^^ T2' []) (TM.initial_config M\<^sub>f [])),
             TM.TM.initial_state M\<^sub>g, 1, TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' [])
             (TM.initial_config M\<^sub>L []))), undefined) \<in> final_states"
      unfolding final_states_def states_def apply auto
      using T1'_final [of "[]"]
        apply (simp add: TM.final_states_valid TM.is_final_def TM.run_def)
      using T2'_final [of "[]"]
      by (simp_all add: TM.final_states_valid TM.is_final_def TM.run_def)
    have 2: "(3, state ((TM.step M\<^sub>L ^^ T1' []) (TM.initial_config M\<^sub>L [])),
             TM.TM.initial_state M\<^sub>f, state ((TM.step M\<^sub>g ^^ T3' [])
             (TM.initial_config M\<^sub>g [])), 1, TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' [])
             (TM.initial_config M\<^sub>L []))), undefined) \<in> final_states"
      unfolding final_states_def states_def apply auto
      using T1'_final [of "[]"]
        apply (simp add: TM.final_states_valid TM.is_final_def TM.run_def)
      using T3'_final [of "[]"]
      by (simp_all add: TM.final_states_valid TM.is_final_def TM.run_def)
    show "TM.halts (Abs_TM M') []"
      apply (cases "P []")
      unfolding TM.halts_def TM.halts_config_def using f51' [OF Nat.le_refl] 1 apply simp
       apply (metis M'_final_states One_nat_def f51' [OF Nat.le_refl] is_finalI)
      using f51'' [OF Nat.le_refl] 2 apply simp
      by (metis M'_final_states One_nat_def f51'' [OF Nat.le_refl] is_finalI)
  qed
  have time_bounded_Nil: "TM.time_bounded_word (Abs_TM M')
                          (\<lambda>n. Suc (Suc (T1 n + max (T2 n) (T3 n) + 3 * n))) []"
    unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def
  proof simp
    have 1: "P [] \<Longrightarrow> state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
             ((TM.step (Abs_TM M') ^^ (T1' [] + T2' []))
             (TM.initial_config (Abs_TM M') [])))) \<in> final_states"
      unfolding f51' [OF Nat.le_refl, simplified] final_states_def states_def apply auto
        apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
       apply (metis T2'_final TM.final_states_valid TM.run_def is_finalD)
      by (metis T2'_final TM.run_def is_finalD)
    have 2: "\<not>P [] \<Longrightarrow> state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
             ((TM.step (Abs_TM M') ^^ (T1' [] + T3' []))
             (TM.initial_config (Abs_TM M') [])))) \<in> final_states"
    unfolding f51'' [OF Nat.le_refl, simplified] final_states_def states_def apply auto
        apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
       apply (metis T3'_final TM.final_states_valid TM.run_def is_finalD)
    by (metis T3'_final TM.run_def is_finalD)
  have 3: "T1' [] + T2' [] \<le> T1 0 + max (T2 0) (T3 0)" using T1'_le_T1 [of "[]"]
      T2'_le_T2 [of "[]"] by simp
  have 4: "T1' [] + T3' [] \<le> T1 0 + max (T2 0) (T3 0)" using T1'_le_T1 [of "[]"]
      T2'_le_T3 [of "[]"] by simp
    show "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
          ((TM.step (Abs_TM M') ^^ (T1 0 + max (T2 0) (T3 0)))
          (TM.initial_config (Abs_TM M') [])))) \<in> final_states"
      apply (cases "P []")
       apply (drule 1)
      using 3
      apply (metis (no_types, lifting) M'_final_states TM.final_mono funpow_swap1 is_finalD
          is_finalI)
      apply (drule 2)
      using 4
      by (metis (no_types, lifting) M'_final_states TM.final_mono funpow_swap1 is_finalD
          is_finalI)
  qed
  have f61: "state (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) =
             (4, state (TM.steps M\<^sub>L (T1' w) (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 3, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))), w ! (length w - 1))" and
       f62: "\<And>i. i > 0 \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.tape_count M\<^sub>f \<Longrightarrow>
             i \<noteq> tc - TM.tape_count M\<^sub>g \<Longrightarrow> tapes (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) ! i =
             tapes (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! i" and
       f63: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>f) =
             Tape (rev (map Some (butlast w))) (Some (last w)) []" and
       f64: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.tape_count M\<^sub>f \<noteq> TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>g) =
             Tape [] None []" and
       f65: "\<not>TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>g) =
             Tape (rev (map Some (butlast w))) (Some (last w)) []" and
       f66: "\<not>TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.tape_count M\<^sub>f \<noteq> TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>f) =
             Tape [] None []"
       if "w \<noteq> []" for w :: "'a list"
  proof -
    have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
      using f41 [of "length w - 1" w] that apply simp
      unfolding final_states_def by simp
    show "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + length w))
          (TM.initial_config (Abs_TM M') w)) =
          (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
          TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 3,
          TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
          w ! (length w - 1))" apply simp
      apply (subst TM.step_def)
      apply auto
      using f41 [of "length w - 1" w] that apply simp
      apply (subst M'_def)
      apply simp
      apply (subst nth_map)
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      unfolding f51 [OF that, simplified] by simp
  next
    fix i :: nat
    assume a1: "0 < i" and a2: "i < tc" and a3: "i \<noteq> tc - TM.TM.tape_count M\<^sub>f" and
           a4: "i \<noteq> tc - TM.TM.tape_count M\<^sub>g"
    have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
      using f41 [of "length w - 1" w] that apply simp
      unfolding final_states_def by simp
    have [simp]: "[0..<tc] ! i = i" using a2 by simp
    have 1: "T1' w + 2 + (length w - 1) = T1' w + 1 + length w" using that by simp
    have [simp]: "state (TM.step (Abs_TM M')
                  ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) =
                  (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
                  TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 2,
                  TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
                  w ! (length w - Suc 0))"
      using f41 [of "length w - 1" w] that unfolding 1 by simp
    have [simplified, simp]: "state (TM.step (Abs_TM M')
                  ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
      using f41 [of "length w - 1" w] that apply simp
      unfolding final_states_def by simp
    show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + length w))
          (TM.initial_config (Abs_TM M') w)) ! i =
          tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
      apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (simp add: TM.next_actions_simps(2) a2)
       apply (simp add: TM.init_conf_len TM.step_l_tps TM.steps_l_tps a2)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply auto
        apply fact+
      apply (subst (1 2) nth_map)
       apply auto
       apply fact
      apply (subst M'_def)
      using a1 a2 a3 a4 apply auto
      unfolding TM_abbrevs.tape_shift.simps apply (subst M'_def)
       apply (simp add: TM_abbrevs.tape_write_def)
       apply (subst nth_map)
      apply (simp add: TM.init_conf_len TM.step_l_tps TM.steps_l_tps)
       apply simp
      using f42 [of "length w - 1" w i, OF _ a1 a2 a3 a4, unfolded 1] that apply simp
      apply (subst M'_def)
      apply (simp add: TM_abbrevs.tape_write_def)
      apply (subst nth_map)
       apply (simp add: TM.run_tapes_len TM.step_l_tps)
      apply simp
      using f42 [of "length w - 1" w i, OF _ a1 a2 a3 a4, unfolded 1] that by simp
  next
    assume a1: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
    have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
      using f41 [of "length w - 1" w] that apply simp
      unfolding final_states_def by simp
    have *: "T1' w + 2 + (length w - 1) = T1' w + length w + 1"
      using that by simp
    have 1: "right (tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
             (TM.initial_config (Abs_TM M') w))) ! (tc - TM.TM.tape_count M\<^sub>f)) = []"
      using f43 [of "length w - 1" w, unfolded *] that apply simp
      using a1 by force
    show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
          Tape (rev (map Some (butlast w))) (Some (last w)) []"
      apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
      using tc_ge_tcL apply force+
      apply simp
      apply (subst (1 2) nth_map)
      using tc_ge_tcL apply auto
      using f41 [of "length w - 1" w] that apply simp
      apply (subst M'_def)
      using a1 apply auto
      apply (subst M'_def)
       apply (simp add: TM_abbrevs.tape_write_def)
      using linorder_not_less tc_ge_tcf apply blast
      using linorder_not_less tc_ge_tcf apply blast
      using f51 [OF that] apply simp
       apply (simp add: TM.run_tapes_len TM.step_l_tps)
      apply (simp add: TM_abbrevs.tape_shift.simps)
      apply (subst M'_def)
      apply (auto simp add: TM_abbrevs.tape_write_def)
      using f43 [of "length w - 1" w, unfolded *] that apply simp
        apply (metis One_nat_def butlast_conv_take take_map)
       apply (metis One_nat_def last_conv_nth)
      by (rule 1)
    assume a2: "TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g"
    have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
      unfolding tc_def by simp
    show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
          Tape [] None []"
      apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply auto
      using M'_tc diff_less apply blast
      using M'_tc diff_less apply blast
      apply (subst (1 2) nth_map)
       apply auto
      using M'_tc diff_less apply blast
      using f41 [of "length w - 1" w, unfolded *] that apply simp
      apply (subst M'_def)
      using a1 a2 apply auto
      using tc_ge_tcg apply linarith+
      unfolding TM_abbrevs.tape_shift.simps
       apply (subst M'_def)
       apply (auto simp add: TM_abbrevs.tape_write_def)
      using f44 [of "length w - 1" w, unfolded *] apply simp_all
      apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
          TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' diff_less tape.sel(2))
      apply (subst M'_def)
      apply auto
      by (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
          TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' diff_less tape.sel(2))
  next
    assume a1: "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
    have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
      using f41 [of "length w - 1" w] that apply simp
      unfolding final_states_def by simp
    have *: "T1' w + 2 + (length w - 1) = T1' w + length w + 1"
      using that by simp
    have 1: "right (tapes (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
             (TM.initial_config (Abs_TM M') w))) ! (tc - TM.TM.tape_count M\<^sub>g)) = []"
      using f45 [of "length w - 1" w, unfolded *] that apply simp
      using a1 by force
    have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
      unfolding tc_def by simp
    show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
          Tape (rev (map Some (butlast w))) (Some (last w)) []"
      apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
      apply simp
      apply (subst (1 2) nth_map)
       apply auto
      using M'_tc diff_less apply blast
      using f41 [of "length w - 1" w, unfolded *] that apply simp
      apply (subst M'_def)
      using a1 apply auto
      using f51 [OF that] apply simp
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
          TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' option.distinct(1) tape.sel(2))
      apply (subst M'_def)
      apply auto
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      using f45 [of "length w - 1" w, unfolded *] that apply simp
      using linorder_not_less tc_ge_tcg apply blast
         apply (subst (asm) nth_map)
          apply (simp add: TM.run_tapes_len TM.step_l_tps)
      using f51 [OF that] apply simp
      using f45 [of "length w - 1" w, unfolded *] that apply simp
        apply (metis One_nat_def butlast_conv_take take_map)
       apply (subst M'_def)
       apply simp
       apply (metis One_nat_def last_conv_nth)
      by (rule 1)
    assume a2: "TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g"
    have 2: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
      unfolding tc_def by simp
    show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
          Tape [] None []"
      apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
      apply simp
      apply (subst nth_map)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_upt)
      using f41 [of "length w - 1" w, unfolded *] that apply simp
      apply (subst M'_def)
      using a1 a2 apply auto
         apply (metis M'_tc TM.at_least_one_tape add_diff_cancel_left' diff_diff_cancel
          diff_less diff_zero nat_less_le nth_upt tc_ge_tcf)
        apply (metis M'_tc TM.at_least_one_tape add_0 diff_less less_irrefl_nat nth_upt
          tc_ge_tcf zero_less_diff)
       apply (subst nth_map)
        apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_upt)
      unfolding TM_abbrevs.tape_shift.simps apply (subst M'_def)
       apply (auto simp add: 2 TM_abbrevs.tape_write_def)
      using f46 [of "length w - 1" w, unfolded *] that apply simp_all
      apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
          TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' diff_less tape.sel(2))
      unfolding 2 apply (subst M'_def)
      apply auto
      by (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps
          TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id' diff_less tape.sel(2))
  qed
  have f67: "left (tapes (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) ! 0) =
             (rev (take (length w - 1) (map Some w))) @
             left (tapes (TM.steps (Abs_TM M') (T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)" if "w \<noteq> []"
    for w :: "'a list"
  proof simp
    have *: "T1' w + 2 + (length w - 1) = T1' w + length w + 1" using that by simp
    have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
      using f41 [of "length w - 1" w, unfolded *] that apply simp
      unfolding final_states_def by simp
    have [simp]: "[0..<tc] ! 0 = 0" unfolding tc_def by simp
    have 1: "\<And>P. length w \<le> Suc 0 \<Longrightarrow> (\<And>x. w = [x] \<Longrightarrow> P) \<Longrightarrow> P"
      using that by (metis le_antisym length_1_ex_iff length_Suc0_not_empty)
    show "left (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
          ((TM.step (Abs_TM M') ^^ (T1' w + length w))
          (TM.initial_config (Abs_TM M') w)))) ! 0) =
          rev (take (length w - Suc 0) (map Some w)) @
          left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)) ! 0)"
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
      using tc_ge_tcL apply fastforce+
      apply (subst (1 2) nth_map)
      using tc_ge_tcL apply force
      apply simp
      using f41 [of "length w - 1" w, unfolded *] that apply simp
      apply (subst M'_def)
      apply auto
         apply (subst (asm) nth_map)
          apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      using f51 [OF that] apply simp
        apply (subst (asm) nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      using f51 [OF that] apply simp
      using f51 [OF that] apply simp
    proof (rule nth_equalityI')
      have *: "trimRight None xs = map Some ys \<Longrightarrow>
               \<exists>n. xs = map Some ys @ (replicate n None)" for xs :: "'a option list" and
        ys :: "'a list"
      proof (induction xs arbitrary: ys rule: rev_induct)
      case Nil
      then show ?case by simp
    next
      case (snoc x xs)
      show ?case
      proof (cases x)
        case None
        then show ?thesis using snoc apply auto
          by (metis replicate_Suc replicate_append_same)
      next
        case (Some a)
        then show ?thesis using snoc by simp
      qed
    qed
      have 1: "tapes ((TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w)) =
               tapes ((TM.step M\<^sub>L ^^ (T1' w)) (TM.initial_config M\<^sub>L w))"
        using 3 [of w] T1'_final [of w]
        by (metis (mono_tags, lifting) TM.final_steps_rev TM.run_def TM.time_bounded_wordD)
      have 3: "length (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)) \<ge> length w - 1"
        using 2 [of w, unfolded trim_tapes_def, THEN arg_cong, of right] T1'_final [of w]
        apply simp
        apply (subst (asm) hd_map)
         apply (metis TM.run_def TM.run_tapes_non_empty)
        apply simp
        apply (subst zeroth_is_head)
         apply (metis TM.run_def TM.run_tapes_non_empty)
        apply (subst (asm) (2) TM.initial_config_def)
        unfolding TM_abbrevs.input_tape_def apply (simp add: that)
        apply (drule *)
        apply auto
        unfolding 1 unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def,
            THEN arg_cong, of hd w, simplified] by simp
      show "length (tl (rev (take (length w - Suc 0) (right
            (tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w)) ! 0))) @
            head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w)) ! 0) # left
            (tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w)) ! 0))) = length
            (rev (take (length w - Suc 0) (map Some w)) @
            left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w)) ! 0))" using 3 by simp
      fix i :: nat
      assume a1: "i < length (tl (rev (take (length w - Suc 0) (right (tapes
                  ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))) @
                  head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                  (TM.initial_config (Abs_TM M') w)) ! 0) #
                  left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                  (TM.initial_config (Abs_TM M') w)) ! 0)))" and
             a2: "length (tl (rev (take (length w - Suc 0) (right (tapes
                  ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))) @
                  head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                  (TM.initial_config (Abs_TM M') w)) ! 0) #
                  left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                  (TM.initial_config (Abs_TM M') w)) ! 0))) =
                  length (rev (take (length w - Suc 0) (map Some w)) @ left
                  (tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) !
                  0))"
      have 0: "(TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w) =
               (TM.step M\<^sub>L ^^ (T1' w)) (TM.initial_config M\<^sub>L w)" using T1'_final
        by (metis T1'_le_T1 TM.final_mono TM.final_steps_rev TM.run_def)
      have 1: "tapes (trim_tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w))) ! 0 = TM_abbrevs.input_tape w"
        using 2 [of w] apply (subst (asm) (2) TM.initial_config_def)
        apply simp
        apply (subst zeroth_is_head)
         apply (metis TM.run_def TM.run_tapes_non_empty length_0_conv trim_tapes_tape_count)
        unfolding 0 using f12 [OF Nat.le_refl, unfolded ML_tapes_def, THEN arg_cong, of hd w,
            simplified]
        by (metis (lifting) TM.run_def TM.run_tapes_non_empty TM_config.sel(2) hd_map
            trim_tapes_def)
      have 2: "trimRight None xs = map Some ys \<Longrightarrow> \<exists>n. xs = map Some ys@(replicate n None)"
      for xs :: "'a option list" and ys :: "'a list"
    proof (induction xs arbitrary: ys rule: rev_induct)
      case Nil
      then show ?case by simp
    next
      case (snoc x xs)
      show ?case
      proof (cases x)
        case None
        then show ?thesis using snoc apply auto
          by (metis replicate_Suc replicate_append_same)
      next
        case (Some a)
        then show ?thesis using snoc by simp
      qed
    qed
    have 4: "\<forall>x\<in>set (left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0)). x = None \<Longrightarrow>
             \<exists>k. left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0) = replicate k None"
      by (metis replicate_length_same)
      show "tl (rev (take (length w - Suc 0) (right (tapes
            ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! 0))) @
            head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w)) ! 0) #
            left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w)) ! 0)) ! i =
            (rev (take (length w - Suc 0) (map Some w)) @
            left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
            (TM.initial_config (Abs_TM M') w)) ! 0)) ! i"
        apply (subst nth_tl)
         apply auto
        using a1 apply force
        apply (subst nth_append)
        apply auto
          apply (subst rev_nth)
           apply simp
        using 1 unfolding trim_tapes_def apply simp
          apply (subst (asm) nth_map)
           apply auto
        apply (metis TM.at_least_one_tape TM.run_tapes_len less_numeral_extra(3)
            list.size(3))
        using 3 apply simp
          apply (subst nth_append)
          apply auto
          apply (subst rev_nth)
           apply auto
        unfolding TM_abbrevs.input_tape_def apply (auto simp add: that)
          apply (drule 2)
          apply auto
          apply (simp add: Suc_diff_Suc nth_append_left nth_tl)
        using 1 unfolding trim_tapes_def apply simp
         apply (subst (asm) nth_map)
          apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding TM_abbrevs.input_tape_def apply (auto simp add: that)
         apply (drule 2)
         apply auto
         apply (drule 4)
      proof auto
        fix n k :: nat
        assume a3: "\<not> Suc i < length w - Suc 0 + n" and
               a4: "left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                    (TM.initial_config (Abs_TM M') w)) ! 0) = None \<up> k"
        have 1: "i < length w - 1 + k" using a1 a2 unfolding a4 by simp
        have 2: "\<And>P. (length w = 1 \<Longrightarrow> P) \<Longrightarrow> (length w \<ge> 2 \<Longrightarrow> P) \<Longrightarrow> P" using that
          by (metis Suc_1 length_Suc0_not_empty less_eq_Suc_le less_one
              not_less_iff_gr_or_eq)
        have 3: "\<not> Suc i < length w + n - Suc 0 \<Longrightarrow> Suc (Suc i) \<ge> length w + n" by simp
        have 4: "length w + n \<le> Suc (Suc i) \<Longrightarrow>
                 Suc (Suc i) \<le> length w \<Longrightarrow> length w = Suc (Suc i)" by simp
        show "(Some (hd w) # None \<up> k) ! (Suc i - (length w - Suc 0)) =
              (rev (take (length w - Suc 0) (map Some w)) @ None \<up> k) ! i"
          apply (cases "i = 0")
          using 1 a3 that apply auto
           apply (rule 2)
            apply simp_all
           apply (simp add: hd_conv_nth rev_nth)
          apply (drule 3)
          apply (cases "Suc (Suc i) - length w")
           apply auto
           apply (drule 4)
            apply assumption
           apply simp
           apply (subst rev_take)
           apply simp
           apply (subst nth_append)
           apply auto
           apply (simp add: hd_conv_nth rev_nth)
          apply (subst nth_append)
          by auto
      next
        assume a1: "\<not> Suc i < length w - Suc 0"
        have 0: "\<not> Suc i < length w - Suc 0 \<Longrightarrow>
                 i < length w - Suc 0 \<Longrightarrow> i = length w - 2" by simp
        show "(head (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0) #
              left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0)) ! (Suc i - min (length
              (right (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0))) (length w - Suc 0)) =
              (rev (take (length w - Suc 0) (map Some w)) @
              left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! 0)) ! i"
          apply (subst nth_append)
          using a1 apply auto
           apply (drule 0)
            apply assumption
           apply simp
          using 1 unfolding trim_tapes_def apply auto
           apply (subst (asm) nth_map)
            apply auto
            apply (metis TM.run_def TM.run_tapes_non_empty)
          unfolding TM_abbrevs.input_tape_def apply (auto simp add: that)
           apply (drule 2)
           apply (drule 4)
           apply auto
           apply (subst rev_nth)
            apply auto
           apply (simp add: hd_conv_nth that)
          apply (subst (asm) nth_map)
           apply auto
           apply (metis TM.run_def TM.run_tapes_non_empty)
          apply (drule 2)
          apply (drule 4)
          apply auto
          by (simp add: that)
      qed
    qed
  qed
  have f68: "head (tapes (TM.steps (Abs_TM M') (T1' w + 2 + length w)
             (TM.initial_config (Abs_TM M') w)) ! 0) = Some (last w)" if "w \<noteq> []"
    for w :: "'a list"
  proof simp
    have *: "T1' w + 2 + (length w - 1) = T1' w + length w + 1" using that by simp
    have [simp]: "state (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) \<notin> final_states"
      using f41 [of "length w - 1" w, unfolded *] that apply simp
      unfolding final_states_def by simp
    have [simp]: "[0..<TM.TM.tape_count (Abs_TM M')] ! 0 = 0"
      by (metis TM.at_least_one_tape add_diff_inverse_nat diff_is_0_eq' le_numeral_extra(3)
          less_numeral_extra(3) nth_upt)
    have [simp]: "[0..<tc] ! 0 = 0" unfolding tc_def by simp
    have [simp]: "heads (TM.step (Abs_TM M') ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w))) ! 0 = None"
      using f51 [OF that] apply simp
      by (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps TM_abbrevs.tape_write_hd
          TM_abbrevs.tape_write_id' tape.sel(2))
    have 1: "length w \<le> Suc 0 \<Longrightarrow> last w = hd w" using that
      by (simp add: le_Suc_eq length_1_hd_last)
    have 3: "trimRight None xs = map Some ys \<Longrightarrow> \<exists>n. xs = map Some ys@(replicate n None)"
      for xs :: "'a option list" and ys :: "'a list"
    proof (induction xs arbitrary: ys rule: rev_induct)
      case Nil
      then show ?case by simp
    next
      case (snoc x xs)
      show ?case
      proof (cases x)
        case None
        then show ?thesis using snoc apply auto
          by (metis replicate_Suc replicate_append_same)
      next
        case (Some a)
        then show ?thesis using snoc by simp
      qed
    qed
    have 4: "(TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w) =
             (TM.step M\<^sub>L ^^ (T1' w)) (TM.initial_config M\<^sub>L w)" using T1'_final [of w]
      by (metis T1'_le_T1 TM.final_le_steps TM.run_def)
    have 5: "tapes (trim_tapes ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) ! 0 =
             TM_abbrevs.input_tape w"
      apply (subst zeroth_is_head)
       apply (metis TM.run_def TM.run_tapes_non_empty length_0_conv trim_tapes_tape_count)
      using 2 [unfolded trim_tapes_def, of w] T1'_final [of w] apply simp
      apply (subst (asm) hd_map)
       apply (metis TM.run_def TM.run_tapes_non_empty)
      apply (subst (asm) (4) TM.initial_config_def)
      unfolding TM_abbrevs.input_tape_def apply (auto simp add: that)
      apply (rule tape.expand)
      apply auto
      unfolding 4 trim_tapes_def apply auto
        apply (subst hd_map)
         apply auto
        apply (metis TM.run_def TM.run_tapes_non_empty)
       apply (subst hd_map)
        apply auto
       apply (metis TM.run_def TM.run_tapes_non_empty)
      apply (subst hd_map)
       apply auto
      by (metis TM.run_def TM.run_tapes_non_empty)
    show "head (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
          ((TM.step (Abs_TM M') ^^ (T1' w + length w))
          (TM.initial_config (Abs_TM M') w)))) ! 0) = Some (last w)"
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply (subst (1 2) nth_zip)
      apply (metis TM.at_least_one_tape diff_zero length_greater_0_conv length_upt
          list.map_disc_iff)
       apply (metis TM.at_least_one_tape TM.next_moves_def TM.next_moves_simps(2))
      apply simp
      apply (subst nth_map)
       apply (simp add: tc_def)
      using f41 [of "length w - 1" w, unfolded *] that apply simp
      apply (subst M'_def)
      apply (auto simp add: TM_abbrevs.tape_shift.simps)
       apply (subst nth_map)
      apply (metis bot_nat_0.not_eq_extremum diff_zero length_upt less_nat_zero_code
          tc_ge_tcL)
       apply auto
       apply (subst M'_def)
       apply auto
      using leD tc_ge_tcf apply blast
      unfolding TM_abbrevs.tape_write_def apply (subst Shift_Left_is_left_not_empty)
        apply auto
      using f51 [OF that] apply simp
      unfolding f51 [OF that, simplified] apply simp
         apply (subst hd_append)
         apply auto
      unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, THEN arg_cong, of "\<lambda>l. l ! 0" w,
          simplified] unfolding 1 using 5 unfolding trim_tapes_def apply auto
           apply (subst (asm) nth_map)
            apply auto
      apply (metis TM.at_least_one_tape TM.run_tapes_len less_numeral_extra(3)
          list.size(3))
      unfolding TM_abbrevs.input_tape_def apply (auto simp add: that)
          apply (subst (asm) nth_map)
           apply auto
           apply (metis TM.run_def TM.run_tapes_non_empty)
          apply (metis Nitpick.size_list_simp(2) length_1_hd_last that)
         apply (subst (asm) nth_map)
          apply auto
          apply (metis TM.run_def TM.run_tapes_non_empty)
      apply (drule 3)
         apply auto
          apply (metis hd_rev last_map last_tl)
         apply (metis One_nat_def diff_is_0_eq hd_rev last_map last_tl length_tl
          list.size(3))
        apply (subst (asm) nth_map)
         apply auto
       apply (metis TM.run_def TM.run_tapes_non_empty)
      apply (subst nth_map)
       apply auto
      using tc_ge_tcg apply linarith
      apply (subst M'_def)
      apply auto
      using linorder_not_le tc_ge_tcg apply blast
      apply (subst Shift_Left_is_left_not_empty)
       apply auto
      apply (subst hd_append)
      apply auto
        apply (drule 1)
        apply simp
      using that apply (metis last.simps list.collapse)
      apply (drule 3)
      apply auto
       apply (metis hd_rev last_map last_tl)
      by (metis One_nat_def diff_is_0_eq hd_rev last_map last_tl length_tl list.size(3))
  qed
  have f_left_0: "\<exists>n. left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                  (TM.initial_config (Abs_TM M') w)) ! 0) = replicate n None"
    for w :: "'a list"
    using 2 [of w, unfolded trim_tapes_def] T1'_final [of w] apply simp
    apply (subst (asm) hd_map)
     apply auto
    apply (metis TM.at_least_one_tape TM.run_tapes_len less_numeral_extra(3)
        list.size(3))
    apply (subst (asm) (4) TM.initial_config_def)
    unfolding TM_abbrevs.input_tape_def apply simp
    apply (cases w)
     apply auto
  proof -
    assume a1: "TM.is_final M\<^sub>L (TM.run M\<^sub>L (T1' []) [])" and a2: "w = []" and
           a3: "\<forall>x\<in>set (left (hd (tapes ((TM.step M\<^sub>L ^^ T1 0)
                (TM.initial_config M\<^sub>L []))))). x = None" and
           a4: "head (hd (tapes ((TM.step M\<^sub>L ^^ T1 0) (TM.initial_config M\<^sub>L [])))) = None"
       and a5: "\<forall>x\<in>set (right (hd (tapes ((TM.step M\<^sub>L ^^ T1 0)
                (TM.initial_config M\<^sub>L []))))). x = None"
    have 1: "(TM.step M\<^sub>L ^^ T1 0) (TM.initial_config M\<^sub>L []) = (TM.step M\<^sub>L ^^ T1' [])
             (TM.initial_config M\<^sub>L [])" using a1
      by (metis Nat.add_0_right T1'_le_T1 TM.final_le_steps TM.run_def list.size(3))
    have 2: "\<And>y. (\<forall>x \<in> set l. x = y) \<longleftrightarrow> (\<exists>n. l = replicate n y)" for l :: "'a option list"
    proof (induction l)
      case Nil
      then show ?case by simp
    next
      case (Cons a l)
      then show ?case apply auto
          apply (metis replicate_Suc)
         apply (meson Cons_replicate_eq)
        by (simp add: Cons_replicate_eq)
    qed
    show "\<exists>n. left (tapes ((TM.step (Abs_TM M') ^^ T1' [])
          (TM.initial_config (Abs_TM M') [])) ! 0) = None \<up> n"
      apply (subst zeroth_is_head)
       apply (metis TM.run_def TM.run_tapes_non_empty)
      using a3 [unfolded 1 2]
      by (metis (no_types, lifting) TM.at_least_one_tape ML_tapes_def add.right_neutral
          f12 hd_take le_add1)
  next
    fix h :: 'a and t :: "'a list"
    assume a1: "TM.is_final M\<^sub>L (TM.run M\<^sub>L (T1' (h # t)) (h # t))" and
           a2: "w = h # t" and
           a3: "\<forall>x\<in>set (left (hd (tapes (TM.step M\<^sub>L
                ((TM.step M\<^sub>L ^^ (T1 (Suc (length t)) + length t))
                (TM.initial_config M\<^sub>L (h # t))))))). x = None" and
           a4: "head (hd (tapes (TM.step M\<^sub>L
                ((TM.step M\<^sub>L ^^ (T1 (Suc (length t)) + length t))
                  (TM.initial_config M\<^sub>L (h # t)))))) = Some h" and
           a5: "trimRight None (right (hd (tapes (TM.step M\<^sub>L
                ((TM.step M\<^sub>L ^^ (T1 (Suc (length t)) + length t))
                (TM.initial_config M\<^sub>L (h # t))))))) = map Some t"
    have 1 [unfolded a2, simplified]: "(TM.step M\<^sub>L ^^ (T1 (length w) + length w))
             (TM.initial_config M\<^sub>L (h#t)) = (TM.step M\<^sub>L ^^ (T1' (h#t)))
             (TM.initial_config M\<^sub>L (h#t))" using a1 3 [of "h#t"]
      unfolding TM.time_bounded_word_def apply simp
      unfolding TM.run_def apply simp
      apply (subst TM.final_steps_rev)
      by (auto simp add: a2)
    have 2: "\<And>y. (\<forall>x \<in> set l. x = y) \<longleftrightarrow> (\<exists>n. l = replicate n y)" for l :: "'a option list"
    proof (induction l)
      case Nil
      then show ?case by simp
    next
      case (Cons a l)
      then show ?case apply auto
          apply (metis replicate_Suc)
         apply (meson Cons_replicate_eq)
        by (simp add: Cons_replicate_eq)
    qed
    show "\<exists>n. left (tapes ((TM.step (Abs_TM M') ^^ T1' (h # t))
          (TM.initial_config (Abs_TM M') (h # t))) ! 0) = None \<up> n"
      apply (subst zeroth_is_head)
       apply (metis TM.run_def TM.run_tapes_non_empty)
      using a3 unfolding 1 2 apply auto
      by (metis (no_types, lifting) 5 TM.at_least_one_tape TM.run_tapes_len f12 hd_conv_nth
          lessI linorder_not_less list.size(3) not_less_eq)
  qed
  have f71: "state (TM.steps (Abs_TM M') (T1' w + 3 + length w)
             (TM.initial_config (Abs_TM M') w)) =
             (4, state (TM.steps M\<^sub>L (T1' w) (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 4, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))), w ! (length w - 1))" and
       f72: "\<And>i. i > 0 \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.tape_count M\<^sub>f \<Longrightarrow>
             i \<noteq> tc - TM.tape_count M\<^sub>g \<Longrightarrow> tapes (TM.steps (Abs_TM M')
             (T1' w + 3 + length w)
             (TM.initial_config (Abs_TM M') w)) ! i =
             tapes (TM.steps (Abs_TM M') (T1' w) (TM.initial_config (Abs_TM M') w)) ! i" and
       f73: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 3 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>f) =
             Tape (rev (map Some (butlast w))) (Some (last w)) []" and
       f74: "TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.tape_count M\<^sub>f \<noteq> TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 3 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>g) =
             Tape [] None []" and
       f75: "\<not>TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 3 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>g) =
             Tape (rev (map Some (butlast w))) (Some (last w)) []" and
       f76: "\<not>TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.tape_count M\<^sub>f \<noteq> TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes (TM.steps (Abs_TM M') (T1' w + 3 + length w)
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.tape_count M\<^sub>f) =
             Tape [] None []" and
       f77: "left (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
             (TM.initial_config (Abs_TM M') w)) ! 0) = drop 2
             ((rev (map Some w)) @ left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0))" and
       f78: "length w = 1 \<Longrightarrow> head (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
             (TM.initial_config (Abs_TM M') w)) ! 0) = None" and
       f79: "length w > 1 \<Longrightarrow> head (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
             (TM.initial_config (Abs_TM M') w)) ! 0) = Some (w ! (length w - 2))"
       if "w \<noteq> []" for w :: "'a list"
  proof -
    have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                  ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                  (TM.initial_config (Abs_TM M') w)))) \<notin> final_states"
      unfolding f61 [OF that, simplified] final_states_def by simp
    obtain k :: nat where left_repl [simp]: "left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
           (TM.initial_config (Abs_TM M') w)) ! 0) = replicate k None" using f_left_0 ..
    show "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) = (4, state ((TM.step M\<^sub>L ^^ T1' w)
          (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
          TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
          w ! (length w - 1))"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      unfolding f61 [OF that, simplified] apply (subst M'_def)
      by simp
    show "\<And>i. 0 < i \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.TM.tape_count M\<^sub>f \<Longrightarrow>
          i \<noteq> tc - TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! i =
          tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
    proof -
      fix i :: nat
      assume a1: "0 < i" and a2: "i < tc" and a3: "i \<noteq> tc - TM.TM.tape_count M\<^sub>f" and
             a4: "i \<noteq> tc - TM.TM.tape_count M\<^sub>g"
      have [simp]: "[0..<tc] ! i = i" using a2 by simp
      have [simp]: "[0..<tc] ! i \<noteq> 0" using a1 by simp
      show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
            (TM.initial_config (Abs_TM M') w)) ! i =
            tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
        unfolding numeral_3_eq_3 apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2) a2)
         apply (simp add: TM.run_tapes_len TM.step_l_tps a2)
        unfolding f61 [OF that, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
          TM.next_writes_def TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply simp_all
          apply fact+
        apply (subst (1 2) nth_map)
         apply simp_all
         apply fact
        apply (subst M'_def)
        using a1 apply auto
        apply (subst M'_def)
        using a1 apply auto
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len TM.step_l_tps a2)
        unfolding f62 [OF that a1 a2 a3 a4, simplified]
        by (simp add: TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def)
    qed
    have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
      by (metis M'_tc TM.at_least_one_tape add_0 diff_less nth_upt)
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
          Tape (rev (map Some (butlast w))) (Some (last w)) []"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding f61 [OF that, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def apply (subst (1 2) nth_zip)
        apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
      apply simp
      apply (subst (1 2) nth_map)
       apply simp_all
      using M'_tc diff_less apply blast
      apply (subst M'_def)
      apply auto
      using linorder_not_le tc_ge_tcf apply blast
      apply (subst M'_def)
      apply auto
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      unfolding f63 [OF that, simplified] apply auto
      apply (subst nth_map)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding f63 [OF that, simplified] by simp
    have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.tape_count M\<^sub>g"
      unfolding tc_def by simp
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) = Tape [] None []"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding f61 [OF that, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def apply simp
      apply (subst nth_zip)
        apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
      apply simp
      apply (subst nth_map)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_upt)
      apply (subst M'_def)
      apply auto
      using linorder_not_less tc_ge_tcg apply blast
      apply (subst M'_def)
      apply auto
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      unfolding f64 [OF that, simplified] apply simp_all
      apply (subst nth_map)
       apply (simp add: TM.run_tapes_len TM.step_l_tps)
      unfolding f64 [OF that, simplified] by simp
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
          Tape (rev (map Some (butlast w))) (Some (last w)) []"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding f61 [OF that, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
      apply simp
      apply (subst (1 2) nth_map)
      using tc_ge_tcL apply simp
      apply (subst M'_def)
      apply auto
      using tc_ge_tcg apply linarith
      apply (subst M'_def)
      apply auto
      unfolding TM_abbrevs.tape_write_def TM_abbrevs.tape_shift.simps apply auto
      unfolding f65 [OF that, simplified] apply simp_all
      apply (subst nth_map)
       apply (simp add: TM.run_tapes_len TM.step_l_tps)
      unfolding f65 [OF that, simplified] by simp
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) = Tape [] None []"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding f61 [OF that, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
       apply (metis M'_tc TM.at_least_one_tape diff_less diff_zero length_map length_upt)
      apply simp
      apply (subst (1 2) nth_map)
      using tc_ge_tcL apply simp
      apply (subst M'_def)
      apply auto
      using tc_ge_tcf verit_comp_simplify1(3) apply blast
      apply (subst M'_def)
      apply auto
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      unfolding f66 [OF that, simplified] apply simp_all
      apply (subst nth_map)
       apply (simp add: TM.run_tapes_len TM.step_l_tps)
      unfolding f66 [OF that, simplified] by simp
    show "left (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! 0) = drop 2 (rev (map Some w) @
          left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)) ! 0))"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply auto
      apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_numeral_extra(3)
          list.size(3))
      apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps less_numeral_extra(3)
          list.size(3))
      unfolding f61 [OF that, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
      using tc_ge_tcf apply force+
      apply simp
      apply (subst (1 2) nth_map)
       apply (simp add: tc_def)
      apply (subst M'_def)
      apply (auto simp add: tc_def)
      unfolding f67 [OF that, simplified]
      by (smt (verit, ccfv_threshold) Nitpick.size_list_simp(2) append_eq_append_conv2
          diff_Suc_1' diff_is_0_eq drop_Suc drop_replicate length_drop length_map length_rev
          minus_nat.diff_0 nat_less_le numeral_2_eq_2 rev_take_is_drop self_append_conv that
          tl_append2 tl_drop tl_eqI verit_comp_simplify1(3))
    show "head (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! 0) = None" if "length w = 1"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      unfolding f61 [OF \<open>w \<noteq> []\<close>, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
      apply (metis M'_tc TM.at_least_one_tape diff_zero length_greater_0_conv length_upt
          list.map_disc_iff)
      using tc_ge_tcL apply force
      apply simp
      apply (subst (1 2) nth_map)
       apply (simp add: tc_def)
      apply (subst M'_def)
      apply (auto simp add: tc_def)
      apply (cases "left (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                    (TM.initial_config (Abs_TM M') w)))) ! 0) = []")
       apply auto
      apply (subst Shift_Left_is_left_not_empty)
       apply auto
      unfolding f67 [OF \<open>w \<noteq> []\<close>, simplified] using that by simp
    show "1 < length w \<Longrightarrow> head (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w))
          (TM.initial_config (Abs_TM M') w)) ! 0) = Some (w ! (length w - 2))"
      unfolding numeral_3_eq_3 apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      unfolding f61 [OF that, simplified] TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply (auto simp add: tc_def)
      apply (subst M'_def)
      apply auto
      apply (cases "left (tapes (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                    ((TM.step (Abs_TM M') ^^ (T1' w + length w))
                    (TM.initial_config (Abs_TM M') w)))) ! 0) = []")
      unfolding f67 [OF that, simplified] apply simp
      apply (subst Shift_Left_is_left_not_empty)
       apply auto
      unfolding f67 [OF that, simplified] apply auto
       apply (subst zeroth_is_head [symmetric])
        apply auto
       apply (subst rev_nth)
        apply auto
      unfolding numeral_2_eq_2 apply simp
      apply (subst zeroth_is_head [symmetric])
       apply auto
      apply (subst nth_append)
      apply auto
      apply (subst rev_nth)
      by simp_all
  qed
  have f91: "state (TM.steps (Abs_TM M') (T1' w + 3 + length w + n)
             (TM.initial_config (Abs_TM M') w)) =
             (4, state (TM.steps M\<^sub>L (T1' w) (TM.initial_config M\<^sub>L w)), TM.initial_state M\<^sub>f,
             TM.initial_state M\<^sub>g, 4, TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))), w ! (length w - 1))" and
       f92: "\<And>i. 0 < i \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.TM.tape_count M\<^sub>f \<Longrightarrow>
             i \<noteq> tc - TM.TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
             (TM.initial_config (Abs_TM M') w)) ! i =
             tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
   and f93: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
             Tape (drop (Suc n) (rev (map Some w)))
             (Some (w ! (length w - 1 - n))) (drop (length w - n) (map Some w))" and
       f94: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
             Tape [] None []" and
       f95: "\<not>TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
             (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
             Tape (drop (Suc n) (rev (map Some w)))
             (Some (w ! (length w - 1 - n))) (drop (length w - n) (map Some w))" and
       f96: "\<not>TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
             TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
             tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
             (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
             Tape [] None []" and
       f97: "left (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
             (TM.initial_config (Abs_TM M') w)) ! 0) =
             drop (2 + n) (rev (map Some w) @ left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
             (TM.initial_config (Abs_TM M') w)) ! 0))" and
       f98: "length w = Suc n \<Longrightarrow>
             head (tapes ((TM.step (Abs_TM M') ^^
             (T1' w + 3 + length w + n)) (TM.initial_config (Abs_TM M') w)) ! 0) = None" and
       f99: "length w > Suc n \<Longrightarrow> head (tapes ((TM.step (Abs_TM M') ^^
             (T1' w + 3 + length w + n)) (TM.initial_config (Abs_TM M') w)) ! 0) =
             Some (w ! (length w - 2 - n))"
       if "n < length w" for w :: "'a list" and n :: nat using that
  proof (induction n)
    case 0
    {
      case 1
      hence "w \<noteq> []" by fastforce
      show ?case using f71 [OF \<open>w \<noteq> []\<close>] by simp
    next
      case 2
      hence "w \<noteq> []" by fastforce
      show ?case using f72 [OF \<open>w \<noteq> []\<close> 2(1, 2, 3, 4)] by simp
    next
      case 3
      hence "w \<noteq> []" by fastforce
      show ?case using f73 [OF \<open>w \<noteq> []\<close> 3(1)] apply auto
         apply (simp add: butlast_conv_take drop_map rev_map)
        by (simp add: \<open>w \<noteq> []\<close> last_conv_nth)
    next
      case 4
      hence "w \<noteq> []" by fastforce
      show ?case using f74 [OF \<open>w \<noteq> []\<close> 4(1, 2)] by simp
    next
      case 5
      hence "w \<noteq> []" by fastforce
      show ?case using f75 [OF \<open>w \<noteq> []\<close> 5(1)] apply auto
         apply (simp add: butlast_conv_take drop_map rev_map)
        by (simp add: \<open>w \<noteq> []\<close> last_conv_nth)
    next
      case 6
      hence "w \<noteq> []" by fastforce
      show ?case using f76 [OF \<open>w \<noteq> []\<close> 6(1, 2)] by simp
    next
      case 7
      hence "w \<noteq> []" by fastforce
      show ?case using f77 [OF \<open>w \<noteq> []\<close>] by simp
    next
      case 8
      hence "w \<noteq> []" by fastforce
      show ?case using f78 [simplified, OF \<open>w \<noteq> []\<close> 8(1)] by simp
    next
      case 9
      hence "w \<noteq> []" by fastforce
      show ?case using f79 [simplified, OF \<open>w \<noteq> []\<close> 9(1)] by simp
    }
  next
    case (Suc n)
    {
      case 1
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        apply simp
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        using Suc(9) [OF 1 \<open>n < length w\<close>] by blast
    next
      case 2
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (simp add: "2.prems"(2) TM.next_actions_simps(2))
         apply (simp add: "2.prems"(2) TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
          apply fact+
        apply (subst (1 2) nth_map)
         apply auto
         apply fact
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        using 2 apply auto
        apply (subst M'_def)
         apply simp
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def
         apply (subst nth_map)
          apply auto
          apply (simp add: TM.run_tapes_len)
        using Suc(2) [of i] apply simp
        apply (subst (3) M'_def)
        apply simp
        apply (subst nth_map)
         apply auto
         apply (simp add: TM.run_tapes_len)
        using Suc(2) [of i] by simp
    next
      case 3
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) ! 0 \<noteq> None"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(9) [OF 3(2) \<open>n < length w\<close>] by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len diff_less)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        using M'_tc diff_less apply blast
        using M'_tc diff_less apply blast
        apply (subst (1 2) nth_map)
         apply auto
        using M'_tc diff_less apply blast
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        using 3 apply auto
        apply (subst M'_def)
        apply auto
        unfolding TM_abbrevs.tape_write_def
        apply (cases "left (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                      (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f))")
         apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
           apply (simp_all add: Suc.IH(3))
          apply (metis drop_Suc list.sel(3) tl_drop)
         apply (metis \<open>w \<noteq> []\<close> diff_less length_greater_0_conv length_map nth_map
            nth_via_drop rev_nth zero_less_Suc)
        apply (subst nth_map)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len diff_less)
        unfolding Suc(3) [OF 3(1) \<open>n < length w\<close>] apply simp
        by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc Suc_diff_Suc \<open>n < length w\<close>
            add_gr_0 diff_less length_map less_imp_add_positive nth_map zero_less_Suc)
    next
      case 4
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) ! 0 \<noteq> None"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(9) [OF 4(3) \<open>n < length w\<close>] by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len diff_less)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        using M'_tc diff_less apply blast
        using M'_tc diff_less apply blast
        apply (subst (1 2) nth_map)
        apply auto
        using M'_tc diff_less apply blast
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        using 4 apply auto
          apply (metis diff_diff_cancel less_or_eq_imp_le tc_ge_tcf tc_ge_tcg)
        using linorder_not_less tc_ge_tcg apply blast
        apply (subst M'_def)
        apply simp
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        apply simp
        by (rule Suc(4) [OF 4(1, 2) \<open>n < length w\<close>])
    next
      case 5
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) ! 0 \<noteq> None"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(9) [OF 5(2) \<open>n < length w\<close>] by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len diff_less)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        using M'_tc diff_less apply blast
        using M'_tc diff_less apply blast
        apply (subst (1 2) nth_map)
         apply auto
        using M'_tc diff_less apply blast
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        using 5 apply auto
        apply (subst M'_def)
        apply auto
        unfolding TM_abbrevs.tape_write_def
        apply (cases "left (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                      (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g))")
         apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
           apply (simp add: Suc.IH(5))
          apply (metis Suc.IH(5) \<open>n < length w\<close> drop_Suc list.sel(3) tape.sel(1) tl_drop)
         apply (metis (no_types, lifting) Suc.IH(5) \<open>n < length w\<close> diff_Suc_less
            le_add_same_cancel1 le_numeral_extra(4) length_map nth_map nth_via_drop
            order.strict_trans1 rev_nth tape.sel(1) trans_le_add1)
        apply (subst nth_map)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len diff_less)
        unfolding Suc(5) [OF 5(1) \<open>n < length w\<close>] apply simp
        by (smt (verit, del_insts) Cons_nth_drop_Suc Suc_diff_Suc \<open>n < length w\<close>
            add_gr_0 diff_less length_map less_imp_add_positive nth_map zero_less_Suc)
    next
      case 6
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) ! 0 \<noteq> None"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(9) [OF 6(3) \<open>n < length w\<close>] by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
         apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len diff_less)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        using M'_tc diff_less apply blast
        using M'_tc diff_less apply blast
        apply (subst (1 2) nth_map)
         apply auto
        using M'_tc diff_less apply blast
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        using 6 apply auto
          apply (metis diff_diff_cancel le_eq_less_or_eq tc_ge_tcf tc_ge_tcg)
        using linorder_not_less tc_ge_tcf apply blast
        apply (subst M'_def)
        apply simp
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_write_def TM_abbrevs.tape_shift.simps apply simp
        by (rule Suc(6) [OF 6(1, 2) \<open>n < length w\<close>])
    next
      case 7
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) ! 0 \<noteq> None"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(9) [OF 7(1) \<open>n < length w\<close>] by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        unfolding tc_def apply auto
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        apply auto
        unfolding Suc(7) [OF \<open>n < length w\<close>] apply simp
        using 7 apply simp
        apply (rule nth_equalityI')
         apply auto
        apply (subst nth_tl)
         apply auto
        unfolding nth_append apply auto
        by (smt (verit, best) Nat.add_diff_assoc2 Nat.diff_diff_right add.commute
            add.right_neutral add_Suc_right add_diff_inverse_nat diff_is_0_eq
            less_eq_Suc_le linorder_not_less not_add_less1 not_less_eq)
    next
      case 8
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) ! 0 \<noteq> None"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(9) [OF 8(2) \<open>n < length w\<close>] by simp
      have [simp]: "(TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w) =
                    (TM.step M\<^sub>L ^^ (T1' w)) (TM.initial_config M\<^sub>L w)" for w :: "'a list"
        using 3 [of w] T1'_final [of w]
        by (metis (no_types, opaque_lifting) T1'_le_T1 TM.final_le_steps TM.run_def)
      have 1: "\<And>x. x \<in> set (left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)) \<Longrightarrow> x = None"
        using 2 [simplified, unfolded trim_tapes_def, THEN arg_cong, of left w] apply simp
        apply (subst (asm) hd_map)
         apply auto
         apply (metis TM.run_def TM.run_tapes_non_empty)
        apply (subst (asm) (3) TM.initial_config_def)
        unfolding TM_abbrevs.input_tape_def apply (auto simp add: \<open>w \<noteq> []\<close>)
        apply (subst (asm) zeroth_is_head [symmetric])
         apply (metis TM.run_def TM.run_tapes_non_empty)
        unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, THEN arg_cong,
            of "\<lambda>l. l ! 0" w, simplified] by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        unfolding tc_def apply auto
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        apply auto
         apply (subst M'_def)
         apply simp
        unfolding TM_abbrevs.tape_write_def
        apply (cases "left (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                      (TM.initial_config (Abs_TM M') w)) ! 0)")
          apply auto
         apply (subst Shift_Left_is_left_not_empty)
          apply auto
        using 1 unfolding Suc(7) [OF \<open>n < length w\<close>] apply (simp add: "8.prems"(1))
        using 8 apply simp
        apply (subst (3) M'_def)
        apply simp
        apply (cases "left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
                      (TM.initial_config (Abs_TM M') w)) ! 0)")
         apply auto
        apply (subst Shift_Left_is_left_not_empty)
         apply auto
        using 1 unfolding Suc(7) [OF \<open>n < length w\<close>] by (simp add: "8.prems"(1))
    next
      case 9
      hence "w \<noteq> []" and "n < length w" by auto
      have [simp]: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) \<notin> final_states"
        unfolding Suc(1) [OF \<open>n < length w\<close>] final_states_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def by simp
      have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                    (TM.initial_config (Abs_TM M') w)) ! 0 \<noteq> None"
        apply (subst nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(9) [OF 9(2) \<open>n < length w\<close>] by simp
      have [simp]: "(TM.step M\<^sub>L ^^ (T1 (length w) + length w)) (TM.initial_config M\<^sub>L w) =
                    (TM.step M\<^sub>L ^^ (T1' w)) (TM.initial_config M\<^sub>L w)" for w :: "'a list"
        using 3 [of w] T1'_final [of w]
        by (metis (no_types, opaque_lifting) T1'_le_T1 TM.final_le_steps TM.run_def)
      have 1: "\<And>x. x \<in> set (left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
               (TM.initial_config (Abs_TM M') w)) ! 0)) \<Longrightarrow> x = None"
        using 2 [simplified, unfolded trim_tapes_def, THEN arg_cong, of left w] apply simp
        apply (subst (asm) hd_map)
         apply auto
         apply (metis TM.run_def TM.run_tapes_non_empty)
        apply (subst (asm) (3) TM.initial_config_def)
        unfolding TM_abbrevs.input_tape_def apply (auto simp add: \<open>w \<noteq> []\<close>)
        apply (subst (asm) zeroth_is_head [symmetric])
         apply (metis TM.run_def TM.run_tapes_non_empty)
        unfolding f12 [OF Nat.le_refl, unfolded ML_tapes_def, THEN arg_cong,
            of "\<lambda>l. l ! 0" w, simplified] by simp
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2) nth_zip)
          apply auto
        unfolding tc_def apply auto
        unfolding Suc(1) [OF \<open>n < length w\<close>] apply (subst M'_def)
        apply auto
         apply (subst M'_def)
         apply simp
        unfolding TM_abbrevs.tape_write_def
        apply (cases "left (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + n))
                      (TM.initial_config (Abs_TM M') w)) ! 0)")
          apply auto
        unfolding Suc(7) [OF \<open>n < length w\<close>] using 9 apply simp
         apply (subst Shift_Left_is_left_not_empty)
          apply auto
        using 9 apply auto
         apply (smt (verit) append_eq_Cons_conv diff_Suc_less drop_eq_Nil
            length_greater_0_conv length_map length_rev linorder_not_less nth_map
            nth_via_drop rev_nth)
        apply (subst (3) M'_def)
        apply auto
        apply (cases "drop (Suc (Suc n)) (rev (map Some w)) @
          left (tapes ((TM.step (Abs_TM M') ^^ T1' w)
          (TM.initial_config (Abs_TM M') w)) ! 0)")
         apply auto
        apply (subst Shift_Left_is_left_not_empty)
         apply auto
        apply (cases "drop (Suc (Suc n)) (rev (map Some w))")
         apply auto
        by (metis length_rev nth_map nth_via_drop rev_map rev_nth)
    }
  qed
    (* TODO: maybe change step count a little *)
  have f91': "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) =
              (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
              TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
              TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
              w ! (length w - 1))" and
       f92': "\<And>i. 0 < i \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.TM.tape_count M\<^sub>f \<Longrightarrow>
              i \<noteq> tc - TM.TM.tape_count M\<^sub>g \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! i =
              tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! i" and
       f93': "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
              Tape [] (Some (w ! 0)) (tl (map Some w))" and
       f94': "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
              Tape [] None []" and
       f95': "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
              Tape [] (Some (w ! 0)) (tl (map Some w))" and
       f96': "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
              Tape [] None []" and
       f97': "head (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! 0) = None"
       if "w \<noteq> []" for w :: "'a list"
  proof -
    have *: "length w - 1 < length w" using that by simp
    have **: "T1' w + 3 + length w + (length w - 1) = T1' w + 2 + 2 * length w"
      using that by simp
    show "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) = (4, state ((TM.step M\<^sub>L ^^ T1' w)
          (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
          TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
          w ! (length w - 1))"
      unfolding f91 [OF *, unfolded **] ..
    show "\<And>i. 0 < i \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.TM.tape_count M\<^sub>f \<Longrightarrow>
          i \<noteq> tc - TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! i =
          tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
      by (drule f92 [OF *, unfolded **])
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
          Tape [] (Some (w ! 0)) (tl (map Some w))"
      apply (drule f93 [OF *, unfolded **])
      using that apply simp
      by (metis drop_0 drop_Suc)
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
          Tape [] None []"
      by (drule f94 [OF *, unfolded **])
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
          Tape [] (Some (w ! 0)) (tl (map Some w))"
      apply (drule f95 [OF *, unfolded **])
      using that apply simp
      by (metis drop_0 drop_Suc)
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
          Tape [] None []"
      by (drule f96 [OF *, unfolded **])
    show "head (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! 0) = None"
      using f98 [OF *, unfolded **] that by simp
  qed
  have f101: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) =
              (2, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
              TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
              TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
              w ! (length w - 1))" and
       f102: "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) =
              (3, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
              TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
              TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
              w ! (length w - 1))" and
       f103: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
              Tape [] (Some (w ! 0)) (tl (map Some w))" and
       f104: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
              Tape [] None []" and
       f105: "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
              Tape [] (Some (w ! 0)) (tl (map Some w))" and
       f106: "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
              TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
              Tape [] None []" and
       f107: "\<And>i. 0 < i \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.TM.tape_count M\<^sub>f \<Longrightarrow>
              i \<noteq> tc - TM.TM.tape_count M\<^sub>g \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
              (TM.initial_config (Abs_TM M') w)) ! i =
              tapes ((TM.step (Abs_TM M') ^^ T1' w)
              (TM.initial_config (Abs_TM M') w)) ! i"
       if "w \<noteq> []" for w :: "'a list"
  proof -
    have *: "length w - 1 < length w" using that by simp
    have **: "TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w) =
              TM.step (Abs_TM M') \<circ>
              (TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w))"
      by (simp add: numeral_3_eq_3)
    have [simp]: "state (TM.step (Abs_TM M') (TM.step (Abs_TM M')
                  ((TM.step (Abs_TM M') ^^ (T1' w + 2 * length w))
                  (TM.initial_config (Abs_TM M') w)))) \<notin> final_states"
      using f91' [OF that] by (simp add: final_states_def)
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) =
          (2, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
          TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
          TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
          w ! (length w - 1))" unfolding ** apply simp
      apply (subst TM.step_def)
      apply auto
      unfolding f91' [OF that, simplified] apply (subst M'_def)
      apply simp
      apply (subst nth_map)
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      using f97' [OF that] by simp
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) = (3, state ((TM.step M\<^sub>L ^^ T1' w)
          (TM.initial_config M\<^sub>L w)), TM.TM.initial_state M\<^sub>f,
          TM.TM.initial_state M\<^sub>g, 4, TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
          (TM.initial_config M\<^sub>L w))), w ! (length w - 1))"
      unfolding ** apply simp
      apply (subst TM.step_def)
      apply auto
      unfolding f91' [OF that, simplified] apply (subst M'_def)
      apply simp
      apply (subst nth_map)
       apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      using f97' [OF that] by simp
    have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>f) = tc - TM.TM.tape_count M\<^sub>f"
      unfolding tc_def by simp
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
          Tape [] (Some (w ! 0)) (tl (map Some w))"
      unfolding ** apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply auto
      using M'_tc diff_less apply blast
      using M'_tc diff_less apply blast
      apply (subst (1 2) nth_map)
       apply auto
      using M'_tc diff_less apply blast
      unfolding f91' [OF that, simplified] apply (subst M'_def)
      apply auto
       apply (subst (asm) nth_map)
      apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      unfolding f97' [OF that, simplified]
       apply simp
      apply (subst M'_def)
      apply simp
      apply (subst nth_map)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply simp
      using f93' [OF that] by simp
    have [simp]: "[0..<tc] ! (tc - TM.TM.tape_count M\<^sub>g) = tc - TM.TM.tape_count M\<^sub>g"
      unfolding tc_def by simp
    show "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) = Tape [] None []"
      unfolding ** apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
      apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply auto
      using M'_tc diff_less apply blast
      using M'_tc diff_less apply blast
      apply (subst (1 2) nth_map)
      apply auto
      using M'_tc diff_less apply blast
      unfolding f91' [OF that, simplified] apply (subst M'_def)
      apply auto
         apply (subst (asm) nth_map)
          apply (metis diff_diff_cancel nless_le tc_ge_tcf tc_ge_tcg)
      unfolding f97' [OF that, simplified] apply simp
      using linorder_not_less tc_ge_tcg apply blast
      apply (subst M'_def)
       apply simp
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      using f94' [OF that] apply auto
       apply (subst nth_map)
        apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding f94' [OF that, simplified] apply simp
      apply simp
      apply (subst M'_def)
      apply simp
      apply (subst nth_map)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      using f94' [OF that] by simp
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>g) =
          Tape [] (Some (w ! 0)) (tl (map Some w))"
      unfolding ** apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply auto
      using M'_tc diff_less apply blast
      using M'_tc diff_less apply blast
      apply (subst (1 2) nth_map)
       apply auto
      using M'_tc diff_less apply blast
      unfolding f91' [OF that, simplified] apply (subst M'_def)
      apply auto
       apply (subst (asm) nth_map)
        apply (metis TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps)
      unfolding f97' [OF that, simplified] apply simp
      apply (subst M'_def)
      apply simp
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      using f95' [OF that, simplified] apply auto
      apply (subst nth_map)
       apply auto
      by (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
    show "\<not> TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<Longrightarrow>
          TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! (tc - TM.TM.tape_count M\<^sub>f) =
          Tape [] None []"
      unfolding ** apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.at_least_one_tape TM.next_actions_simps(2) diff_less)
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (subst (1 2) nth_zip)
        apply auto
      using M'_tc diff_less apply blast
      using M'_tc diff_less apply blast
      apply (subst (1 2) nth_map)
      apply auto
      using M'_tc diff_less apply blast
      unfolding f91' [OF that, simplified] apply (subst M'_def)
      apply auto
      using tc_ge_tcg apply linarith
      using leD tc_ge_tcf apply blast
      apply (subst M'_def)
       apply auto
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      using f96' [OF that, simplified] apply auto
       apply (subst nth_map)
        apply auto
       apply (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
      apply (subst M'_def)
      apply simp
      apply (subst nth_map)
       apply auto
      by (metis M'_tc TM.at_least_one_tape TM.run_tapes_len TM.step_l_tps diff_less)
    show "\<And>i. 0 < i \<Longrightarrow> i < tc \<Longrightarrow> i \<noteq> tc - TM.TM.tape_count M\<^sub>f \<Longrightarrow>
          i \<noteq> tc - TM.TM.tape_count M\<^sub>g \<Longrightarrow>
          tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
          (TM.initial_config (Abs_TM M') w)) ! i =
          tapes ((TM.step (Abs_TM M') ^^ T1' w) (TM.initial_config (Abs_TM M') w)) ! i"
      unfolding ** apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst nth_map2)
        apply (metis M'_tc TM.next_actions_simps(2))
       apply (simp add: TM.run_tapes_len TM.step_l_tps)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
        TM.next_moves_def apply simp
      unfolding f91' [OF that, simplified] apply (subst M'_def)
      apply auto
       apply (subst M'_def)
      apply simp
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply (subst nth_map)
        apply (simp add: TM.run_tapes_len TM.step_l_tps)
       apply simp
      using f92' [OF that] apply simp
      apply (subst (5) M'_def)
      apply simp
      apply (subst nth_map)
       apply auto
       apply (simp add: TM.run_tapes_len TM.step_l_tps)
      using f92' [OF that] by simp
  qed
  have [simp]: "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))) \<longleftrightarrow>
                P w" for w :: "'a list"
    using a1 [of w] a4 [of w] T1'_final [of w] unfolding TM_decider.decides_def apply auto
    apply (metis TM.final_run_compute TM.run_def TM_decider.rejI TM_decider.rejects_def
        is_finalD)
    by (simp add: TM.compute_run_eqI TM.is_final_def TM.run_def TM_decider.accI
        TM_decider.accepts_def)
  have f111: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w)) =
              (2, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
              state ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)),
              TM.TM.initial_state M\<^sub>g, 4, TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))), w ! (length w - 1))" and
       f112: "\<And>i. i < TM.tape_count M\<^sub>f \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w)) ! (i + tc - TM.tape_count M\<^sub>f) =
              tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)) ! i"
    if "w \<noteq> []" and
      "TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
    for w :: "'a list" and n :: nat
  proof (induction n)
    case 0
    {
      case 1
      show ?case using f101 [OF that] apply simp
        unfolding TM.initial_config_def by simp
    next
      case 2
      show ?case
      proof (cases "i = 0")
        case True
        then show ?thesis apply simp
          unfolding f103 [OF that]
          unfolding TM.initial_config_def TM_abbrevs.input_tape_def
          apply (auto simp add: that(1))
          using that zeroth_is_head apply blast
          using that list.map_sel(2) by blast
      next
        case False
        have 1: "i + tc - TM.tape_count M\<^sub>f < tc" unfolding tc_def using 2 by simp
        have 2: "i + tc - TM.tape_count M\<^sub>f > 0" unfolding tc_def using False by simp
        have 3: "i + tc - TM.TM.tape_count M\<^sub>f \<noteq> tc - TM.TM.tape_count M\<^sub>f"
          unfolding tc_def using False by simp
        show ?thesis apply simp
        proof (cases "i + tc - TM.TM.tape_count M\<^sub>f = tc - TM.TM.tape_count M\<^sub>g")
          case True
          hence 1: "TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g"
            using False 2 by simp
          show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
                (TM.initial_config (Abs_TM M') w)) ! (i + tc - TM.TM.tape_count M\<^sub>f) =
                tapes (TM.initial_config M\<^sub>f w) ! i"
            unfolding f104 [OF that 1, folded True]
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def
            apply (auto simp add: that(1))
            using False 2 "2.prems" by fastforce
        next
          case False
          have 4: "TM.TM.tape_count M\<^sub>L \<le> i + tc - TM.TM.tape_count M\<^sub>f"
            by (simp add: add_le_imp_le_diff tc_def)
          show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
                (TM.initial_config (Abs_TM M') w)) ! (i + tc - TM.TM.tape_count M\<^sub>f) =
                tapes (TM.initial_config M\<^sub>f w) ! i"
            unfolding f107 [OF that(1) 2 1 3 False] f13 [OF Nat.le_refl,
                of "i + tc - TM.TM.tape_count M\<^sub>f" w, OF 4 1]
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def
            using \<open>i \<noteq> 0\<close> apply (auto simp add: that)
            by (simp add: "2.prems" diff_less_mono)
        qed
      qed
    }
  next
    case (Suc n)
    {
      case 1
      have [simp]: "state ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)) \<in> TM.TM.states M\<^sub>f"
      proof (induction n)
        case 0
        show ?case by (simp add: TM.initial_config_def)
      next
        case (Suc n)
        then show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          by (simp add: TM.run_tapes_len a7)
      qed
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        unfolding Suc(1) final_states_def apply auto
          apply (simp add: TM.step_def)
        unfolding states_def apply auto
          apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
         apply (subst M'_def)
         apply simp
        apply (subst TM.step_def)
        apply auto
        apply (rule arg_cong [where f="TM.TM.next_state M\<^sub>f (state ((TM.step M\<^sub>f ^^ n)
          (TM.initial_config M\<^sub>f w)))"])
        unfolding Mf_heads_def apply (rule nth_equalityI')
         apply auto
         apply (simp add: TM.init_conf_len TM.steps_l_tps tc_ge_tcf)
      proof -
        fix i :: nat
        assume a1: "min (length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                    (TM.TM.tape_count M\<^sub>f) =
                    length (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)))" and
               a2: "i < length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w)))" and
               a3: "i < TM.TM.tape_count M\<^sub>f"
        have [simp]: "min (length (tapes ((TM.step (Abs_TM M') ^^
                      (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                      (TM.TM.tape_count M\<^sub>f) = TM.tape_count M\<^sub>f"
          using TM.run_tapes_len a1 by auto
        show "rev (take (TM.TM.tape_count M\<^sub>f) (rev (heads
              ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w))))) ! i =
              head (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)) ! i)"
          apply (subst rev_nth)
           apply auto
            apply fact+
          apply (subst rev_nth)
           apply auto
           apply (simp add: TM.run_tapes_len less_imp_diff_less tc_ge_tcf)
          apply (subst nth_map)
           apply (metis TM.at_least_one_tape TM.run_tapes_len diff_Suc_less)
          by (smt (verit, best) M'_tc Nat.diff_cancel Suc.IH(2) Suc_diff_Suc
              TM.run_tapes_len a3 add.commute max.absorb3 nat_minus_add_max)
      qed
    next
      case 2
      have [simp]: "state ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)) \<in> TM.TM.states M\<^sub>f"
      proof (induction n)
        case 0
        show ?case by (simp add: TM.initial_config_def)
      next
        case (Suc n)
        then show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          by (simp add: TM.run_tapes_len a7)
      qed
      have [simp]: "[0..<tc] ! (i + tc - TM.TM.tape_count M\<^sub>f) + TM.TM.tape_count M\<^sub>f - tc =
                    (i + tc - TM.TM.tape_count M\<^sub>f) + TM.TM.tape_count M\<^sub>f - tc"
        unfolding tc_def by (simp add: 2 max_nat)
      have [simp]: "[0..<tc] ! (i + tc - TM.TM.tape_count M\<^sub>f) =
                    i + tc - TM.TM.tape_count M\<^sub>f"
        unfolding tc_def using 2 by force
      have [simp]: "[0..<TM.TM.tape_count M\<^sub>f] ! i = i" by (simp add: 2)
      have [simp]: "Mf_heads (heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
                    (TM.initial_config (Abs_TM M') w))) =
                    heads ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w))"
        unfolding Mf_heads_def apply (rule nth_equalityI')
         apply auto
         apply (simp add: TM.run_tapes_len tc_ge_tcf)
      proof -
        fix i :: nat
        assume a1: "min (length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                    (TM.TM.tape_count M\<^sub>f) =
                    length (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)))" and
               a2: "i < length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w)))" and
               a3: "i < TM.TM.tape_count M\<^sub>f"
        have [simp]: "min (length (tapes ((TM.step (Abs_TM M') ^^
                      (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                      (TM.TM.tape_count M\<^sub>f) = TM.TM.tape_count M\<^sub>f"
          using TM.run_tapes_len a1 by auto
        show "rev (take (TM.TM.tape_count M\<^sub>f) (rev (heads
              ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w))))) ! i =
              head (tapes ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)) ! i)"
          apply (subst rev_nth)
           apply auto
            apply fact+
          apply (subst rev_nth)
           apply auto
           apply (simp add: TM.run_tapes_len less_imp_diff_less tc_ge_tcf)
          apply (subst nth_map)
           apply (metis TM.at_least_one_tape TM.run_tapes_len diff_Suc_less)
          using Suc(2)
          by (smt (verit, best) M'_tc Nat.diff_cancel Suc_diff_Suc TM.run_tapes_len a3
              add.commute max.absorb3 nat_minus_add_max)
      qed
      have [simp]: "i + tc - TM.TM.tape_count M\<^sub>f + TM.TM.tape_count M\<^sub>f - tc = i"
        using tc_ge_tcf by force
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        unfolding Suc(2) [OF 2] Suc(1) final_states_def apply auto
          apply (simp add: TM.step_def)
        unfolding states_def apply auto
         apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
        apply (subst nth_map2)
        apply (metis 2 M'_tc TM.next_actions_simps(2) diff_add_inverse diff_less_mono2
            dual_order.strict_trans tc_ge_tcf trans_less_add2)
        apply (metis 2 M'_tc TM.at_least_one_tape TM.run_tapes_len add.commute diff_is_0_eq
            less_diff_conv2 linorder_not_less nat_add_left_cancel_less nat_less_le)
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (simp add: 2 TM.next_actions_simps(2))
         apply (simp add: 2 TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2 3 4) nth_zip)
            apply auto
        using 2 apply blast+
        using 2 tc_ge_tcf apply force+
        apply (subst (1 2 3 4) nth_map)
          apply auto
        using 2 apply blast
        using 2 tc_ge_tcf apply force
        apply (subst M'_def)
        apply auto
        apply (rule arg_cong [where f="TM_abbrevs.tape_shift
          (TM.TM.next_move M\<^sub>f (state ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w)))
          (heads ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w))) i)"])
        apply (subst M'_def)
        apply auto
        unfolding Suc(2) [OF 2] ..
    }
  qed
  have f121: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w)) =
              (3, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
              TM.initial_state M\<^sub>f, state ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)), 4,
              TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w)
              (TM.initial_config M\<^sub>L w))), w ! (length w - 1))" and
       f122: "\<And>i. i < TM.tape_count M\<^sub>g \<Longrightarrow>
              tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w)) ! (i + tc - TM.tape_count M\<^sub>g) =
              tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)) ! i"
    if "w \<noteq> []" and
      "\<not>TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)))"
    for w :: "'a list" and n :: nat
  proof (induction n)
    case 0
    {
      case 1
      show ?case using f102 [OF that] apply simp
        unfolding TM.initial_config_def by simp
    next
      case 2
      show ?case
      proof (cases "i = 0")
        case True
        then show ?thesis apply simp
          unfolding f105 [OF that]
          unfolding TM.initial_config_def TM_abbrevs.input_tape_def
          apply (auto simp add: that(1))
          using that zeroth_is_head apply blast
          using that list.map_sel(2) by blast
      next
        case False
        have 1: "i + tc - TM.tape_count M\<^sub>g < tc" unfolding tc_def using 2 by simp
        have 2: "i + tc - TM.tape_count M\<^sub>g > 0" unfolding tc_def using False by simp
        have 3: "i + tc - TM.TM.tape_count M\<^sub>g \<noteq> tc - TM.TM.tape_count M\<^sub>g"
          unfolding tc_def using False by simp
        show ?thesis apply simp
        proof (cases "i + tc - TM.TM.tape_count M\<^sub>g = tc - TM.TM.tape_count M\<^sub>f")
          case True
          hence 1: "TM.TM.tape_count M\<^sub>f \<noteq> TM.TM.tape_count M\<^sub>g"
            using False 2 by simp
          show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
                (TM.initial_config (Abs_TM M') w)) ! (i + tc - TM.TM.tape_count M\<^sub>g) =
                tapes (TM.initial_config M\<^sub>g w) ! i"
            unfolding f106 [OF that 1, folded True]
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def
            apply (auto simp add: that(1))
            using False 2
            by (metis "2.prems" Suc_less_eq Suc_pred TM.at_least_one_tape
                bot_nat_0.not_eq_extremum nth_Cons_Suc nth_replicate)
        next
          case False
          have 4: "TM.TM.tape_count M\<^sub>L \<le> i + tc - TM.TM.tape_count M\<^sub>g"
            by (simp add: add_le_imp_le_diff tc_def)
          show "tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w))
                (TM.initial_config (Abs_TM M') w)) ! (i + tc - TM.TM.tape_count M\<^sub>g) =
                tapes (TM.initial_config M\<^sub>g w) ! i"
            unfolding f107 [OF that(1) 2 1 False 3] f13 [OF Nat.le_refl,
                of "i + tc - TM.TM.tape_count M\<^sub>g" w, OF 4 1]
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def
            using \<open>i \<noteq> 0\<close> apply (auto simp add: that)
            by (simp add: "2.prems" diff_less_mono)
        qed
      qed
    }
  next
    case (Suc n)
    {
      case 1
      have [simp]: "state ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)) \<in> TM.TM.states M\<^sub>g"
      proof (induction n)
        case 0
        show ?case by (simp add: TM.initial_config_def)
      next
        case (Suc n)
        then show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          by (simp add: TM.run_tapes_len a10)
      qed
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        unfolding Suc(1) final_states_def apply auto
          apply (simp add: TM.step_def)
        unfolding states_def apply auto
          apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
         apply (subst M'_def)
         apply simp
        apply (subst TM.step_def)
        apply auto
        apply (rule arg_cong [where f="TM.TM.next_state M\<^sub>g (state ((TM.step M\<^sub>g ^^ n)
          (TM.initial_config M\<^sub>g w)))"])
        unfolding Mg_heads_def apply (rule nth_equalityI')
         apply auto
         apply (simp add: TM.init_conf_len TM.steps_l_tps tc_ge_tcg)
      proof -
        fix i :: nat
        assume a1: "min (length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                    (TM.TM.tape_count M\<^sub>g) =
                    length (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)))" and
               a2: "i < length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w)))" and
               a3: "i < TM.TM.tape_count M\<^sub>g"
        have [simp]: "min (length (tapes ((TM.step (Abs_TM M') ^^
                      (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                      (TM.TM.tape_count M\<^sub>g) = TM.tape_count M\<^sub>g"
          using TM.run_tapes_len a1 by auto
        show "rev (take (TM.TM.tape_count M\<^sub>g) (rev (heads
              ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w))))) ! i =
              head (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)) ! i)"
          apply (subst rev_nth)
           apply auto
            apply fact+
          apply (subst rev_nth)
           apply auto
           apply (simp add: TM.run_tapes_len less_imp_diff_less tc_ge_tcg)
          apply (subst nth_map)
           apply (metis TM.at_least_one_tape TM.run_tapes_len diff_Suc_less)
          by (smt (verit, best) M'_tc Nat.diff_cancel Suc.IH(2) Suc_diff_Suc
              TM.run_tapes_len a3 add.commute max.absorb3 nat_minus_add_max)
      qed
    next
      case 2
      have [simp]: "state ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)) \<in> TM.TM.states M\<^sub>g"
      proof (induction n)
        case 0
        show ?case by (simp add: TM.initial_config_def)
      next
        case (Suc n)
        then show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          by (simp add: TM.run_tapes_len a10)
      qed
      have [simp]: "[0..<tc] ! (i + tc - TM.TM.tape_count M\<^sub>g) + TM.TM.tape_count M\<^sub>g - tc =
                    (i + tc - TM.TM.tape_count M\<^sub>g) + TM.TM.tape_count M\<^sub>g - tc"
        unfolding tc_def apply simp
        using 2 add_diff_cancel_right' by fastforce
      have [simp]: "[0..<tc] ! (i + tc - TM.TM.tape_count M\<^sub>g) =
                    i + tc - TM.TM.tape_count M\<^sub>g"
        unfolding tc_def using 2 by force
      have [simp]: "[0..<TM.TM.tape_count M\<^sub>g] ! i = i" by (simp add: 2)
      have [simp]: "Mg_heads (heads ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
                    (TM.initial_config (Abs_TM M') w))) =
                    heads ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w))"
        unfolding Mg_heads_def apply (rule nth_equalityI')
         apply auto
         apply (simp add: TM.run_tapes_len tc_ge_tcg)
      proof -
        fix i :: nat
        assume a1: "min (length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                    (TM.TM.tape_count M\<^sub>g) =
                    length (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)))" and
               a2: "i < length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w)))" and
               a3: "i < TM.TM.tape_count M\<^sub>g"
        have [simp]: "min (length (tapes ((TM.step (Abs_TM M') ^^
                      (T1' w + 3 + 2 * length w + n)) (TM.initial_config (Abs_TM M') w))))
                      (TM.TM.tape_count M\<^sub>g) = TM.TM.tape_count M\<^sub>g"
          using TM.run_tapes_len a1 by auto
        show "rev (take (TM.TM.tape_count M\<^sub>g) (rev (heads
              ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + n))
              (TM.initial_config (Abs_TM M') w))))) ! i =
              head (tapes ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)) ! i)"
          apply (subst rev_nth)
           apply auto
            apply fact+
          apply (subst rev_nth)
           apply auto
           apply (simp add: TM.run_tapes_len less_imp_diff_less tc_ge_tcg)
          apply (subst nth_map)
           apply (metis TM.at_least_one_tape TM.run_tapes_len diff_Suc_less)
          using Suc(2)
          by (smt (verit, best) M'_tc Nat.diff_cancel Suc_diff_Suc TM.run_tapes_len a3
              add.commute max.absorb3 nat_minus_add_max)
      qed
      have [simp]: "i + tc - TM.TM.tape_count M\<^sub>g + TM.TM.tape_count M\<^sub>g - tc = i"
        using tc_ge_tcg by force
      show ?case unfolding add_Suc_right funpow_Suc_right unfolding comp_def
          funpow_swap1 [symmetric] apply (subst TM.step_def)
        apply auto
        unfolding Suc(2) [OF 2] Suc(1) final_states_def apply auto
          apply (simp add: TM.step_def)
        unfolding states_def apply auto
         apply (metis T1'_final TM.final_states_valid TM.is_final_def TM.run_def)
        apply (subst nth_map2)
        apply (metis 2 M'_tc TM.next_actions_simps(2) diff_add_inverse diff_less_mono2
            dual_order.strict_trans tc_ge_tcg trans_less_add2)
        apply (metis 2 M'_tc TM.at_least_one_tape TM.run_tapes_len add.commute diff_is_0_eq
            less_diff_conv2 linorder_not_less nat_add_left_cancel_less nat_less_le)
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply (simp add: 2 TM.next_actions_simps(2))
         apply (simp add: 2 TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def apply simp
        apply (subst (1 2 3 4) nth_zip)
            apply auto
        using 2 apply blast+
        using 2 tc_ge_tcf apply force+
        apply (subst (1 2 3 4) nth_map)
          apply auto
        using 2 apply blast
        using 2 tc_ge_tcf apply force
        apply (subst M'_def)
        apply auto
        apply (rule arg_cong [where f="TM_abbrevs.tape_shift
          (TM.TM.next_move M\<^sub>g (state ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w)))
          (heads ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w))) i)"])
        apply (subst M'_def)
        apply auto
        unfolding Suc(2) [OF 2] ..
    }
  qed
  have time_bounded_Cons: "TM.time_bounded_word (Abs_TM M')
                          (\<lambda>n. T1 n + max (T2 n) (T3 n) + 3 * n + 3) w"
    if "w \<noteq> []" for w :: "'a list"
  proof -
    have "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w +
          max (T2 (length w)) (T3 (length w))))
          (TM.initial_config (Abs_TM M') w)) \<in> TM.final_states (Abs_TM M')"
      apply simp
      apply (cases "P w")
      using f111 [OF that, simplified, of "max (T2 (length w)) (T3 (length w))"] apply simp
      unfolding final_states_def states_def apply auto
            apply (rule TM_steps_valid_stateI)
      using a3 apply blast
           apply (rule TM_steps_valid_stateI)
      using a7 apply blast
      using a6 [of w, unfolded TM.time_bounded_word_def TM.run_def TM.is_final_def]
          apply (meson TM.final_mono is_finalD is_finalI max.cobounded1)
      unfolding f121 [OF that, simplified] apply auto
        apply (rule TM_steps_valid_stateI)
      using a3 apply blast
       apply (rule TM_steps_valid_stateI)
      using a10 apply blast
      using a9 [of w, unfolded TM.time_bounded_word_def TM.run_def TM.is_final_def]
      by (meson TM.final_mono is_finalD is_finalI max.cobounded2)
    moreover have "T1' w + 3 + 2 * length w + max (T2 (length w)) (T3 (length w)) \<le>
                   T1 (length w) + max (T2 (length w)) (T3 (length w)) + 3 * length w + 3"
      using T1'_le_T1 [of w] by simp
    ultimately show  "TM.time_bounded_word (Abs_TM M')
                      (\<lambda>n. T1 n + max (T2 n) (T3 n) + 3 * n + 3) w"
      unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def
      using TM.final_mono is_finalI by blast
  qed
  have function_Cons: "TM.computes_word (Abs_TM M') w (if P w then f w else g w)"
    if "w \<noteq> []" for w :: "'a list"
    unfolding TM.computes_word_def
  proof
    show "TM.halts (Abs_TM M') w"
      using time_bounded_Cons [OF that] TM.time_bounded_wordD by blast
    hence "TM.is_final (Abs_TM M') ((TM.steps (Abs_TM M')
           (LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
           (TM.initial_config (Abs_TM M') w))) (TM.initial_config (Abs_TM M') w)))"
      by (metis TM.compute_config_def TM.compute_def halts_compD)
    moreover have "P w \<Longrightarrow> TM.is_final (Abs_TM M') ((TM.steps (Abs_TM M')
                   (T1' w + 3 + 2 * length w + T2' w) (TM.initial_config (Abs_TM M') w)))"
      using f111 [OF that, of "T2' w"] T2'_final [of w]
      unfolding TM.is_final_def TM.run_def apply auto
      unfolding final_states_def states_def apply auto
      apply (rule set_mp [where A="TM.TM.final_states M\<^sub>L"])
       apply auto
      by (metis T1'_final TM.is_final_def TM.run_def)
    ultimately have 1: "P w \<Longrightarrow> (TM.step (Abs_TM M') ^^ (LEAST n. TM.is_final (Abs_TM M')
                        ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))))
                        (TM.initial_config (Abs_TM M') w) =
                        TM.steps (Abs_TM M') (T1' w + 3 + 2 * length w + T2' w)
                        (TM.initial_config (Abs_TM M') w)"
      using TM.final_steps_rev by blast
    have 2: "P w \<Longrightarrow> last (tapes (TM.steps (Abs_TM M') (T1' w + 3 + 2 * length w + T2' w)
             (TM.initial_config (Abs_TM M') w))) =
             last (tapes (TM.steps M\<^sub>f (T2' w) (TM.initial_config M\<^sub>f w)))"
      using f112 [OF that, simplified, of "TM.tape_count M\<^sub>f - 1" "T2' w"]
      by (smt (verit, del_insts) M'_tc Suc_pred TM.at_least_one_tape
          TM.run_tapes_len add.commute diff_add_inverse diff_diff_left diff_less
          last_conv_nth less_numeral_extra(3) less_one list.size(3)
          plus_1_eq_Suc)
    have 3: "\<not>P w \<Longrightarrow> last (tapes (TM.steps (Abs_TM M') (T1' w + 3 + 2 * length w + T3' w)
             (TM.initial_config (Abs_TM M') w))) =
             last (tapes (TM.steps M\<^sub>g (T3' w) (TM.initial_config M\<^sub>g w)))"
      using f122 [OF that, simplified, of "TM.tape_count M\<^sub>g - 1" "T3' w"]
      by (smt (verit, best) M'_tc Nat.diff_diff_right TM.at_least_one_tape
          TM.at_least_one_tape' TM.run_tapes_len add.commute diff_diff_cancel
          diff_less last_conv_nth less_one list.size(3) nat_less_le)
    show "TM.has_output (TM.compute (Abs_TM M') w) (if P w then f w else g w)"
      unfolding TM.has_output_def TM.clean_output_of_def TM.output_of_def Let_def
        TM.clean_output_def apply (cases "head (last (tapes (TM.compute (Abs_TM M') w)))")
       apply auto
      unfolding TM.compute_def TM.compute_config_def 1 TM_abbrevs.input_tape_def
    proof -
      fix w' :: "'a list"
      assume a1: "head (if w' = [] then Tape [] None [] else
                  Tape [] (Some (hd w')) (map Some (tl w'))) = None" and
             a2: "P w" and
             a3: "last (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + T2' w))
                  (TM.initial_config (Abs_TM M') w))) =
                  (if w' = [] then Tape [] None []
                  else Tape [] (Some (hd w')) (map Some (tl w')))"
      have 1: "w' = []"
        apply (rule ccontr)
        using a1 by simp
      have 2: "last (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + T2' w))
               (TM.initial_config (Abs_TM M') w))) = Tape [] None []"
        using a3 1 by simp
      have *: "\<And>l. l \<noteq> [] \<Longrightarrow> last l = l ! (length l - 1)"
        using last_conv_nth by blast
      have [simp]: "length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + T2' w))
                    (TM.initial_config (Abs_TM M') w))) = tc"
        by (simp add: TM.run_tapes_len)
      have 3: "last (tapes (TM.steps M\<^sub>f (T2' w) (TM.initial_config M\<^sub>f w))) =
               Tape [] None []" using 2 f112 [OF that, simplified, OF a2,
        of "TM.tape_count M\<^sub>f - 1" "T2' w"] apply auto
        apply (subst (asm) *)
         apply auto
         apply (metis TM.run_def TM.run_tapes_non_empty)
        by (metis One_nat_def Suc_pred[of "TM.TM.tape_count M\<^sub>f"] TM.at_least_one_tape[of M\<^sub>f]
            TM.run_tapes_len[of "T2' w" M\<^sub>f w] add.commute[of tc
              "TM.TM.tape_count M\<^sub>f - Suc 0"] add_diff_cancel_right
            [of tc "TM.TM.tape_count M\<^sub>f - 1" "1"]
            last_conv_nth[of "tapes ((TM.step M\<^sub>f ^^ T2' w) (TM.initial_config M\<^sub>f w))"]
            less_numeral_extra(3) list.size(3) plus_1_eq_Suc)
      have 4: "TM.clean_output ((TM.step M\<^sub>f ^^
               (LEAST n. TM.is_final M\<^sub>f ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w))))
               (TM.initial_config M\<^sub>f w))"
        unfolding TM.clean_output_def using a5 [unfolded TM.computes_def, THEN spec,
        of w, unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
        TM.compute_def TM.compute_config_def TM.clean_output_of_def]
        by (meson TM.clean_output_def option.distinct(1))
      show "[] = f w" using a5 [unfolded TM.computes_def, THEN spec, of w,
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.compute_def TM.compute_config_def TM.clean_output_of_def]
        using 4 3 unfolding TM.output_of_def Let_def apply simp
        by (metis (no_types, lifting) LeastI T2'_final T2'_min TM.run_def
            TM_abbrevs.input_tape.simps(1) TM_abbrevs.input_tape_empty_hd_iff
            linorder_less_linear not_less_Least option.simps(4))
    next
      assume a1: "head (last (tapes ((TM.step (Abs_TM M') ^^
                  (T1' w + 3 + 2 * length w + T2' w))
                  (TM.initial_config (Abs_TM M') w)))) = None" and
             a2: "P w"
      have [simp]: "(LEAST n. TM.is_final M\<^sub>f ((TM.step M\<^sub>f ^^ n) (TM.initial_config M\<^sub>f w))) =
                    T2' w" using T2'_min [of _ w] T2'_final [of w] unfolding TM.run_def
        by blast
      show "\<exists>wa. last (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + T2' w))
            (TM.initial_config (Abs_TM M') w))) =
            (if wa = [] then Tape [] None [] else
            Tape [] (Some (hd wa)) (map Some (tl wa)))"
        unfolding 2 [OF a2]
        apply (rule exI [where x="[]"])
        apply auto
        apply (rule tape.expand)
        apply auto
          apply (rule TM_computes_word_left_is_empty [where wo="f w"])
        using a5 unfolding TM.computes_def apply blast
        using T2'_final unfolding TM.run_def apply this
        using a1 2 [OF a2] apply argo
        using a1 [unfolded 2 [OF a2]] a5 [unfolded TM.computes_def, THEN spec, of w,
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.compute_def
            TM.compute_config_def, simplified, unfolded TM.has_output_def
            TM.clean_output_of_def TM.output_of_def Let_def a1 [unfolded 2 [OF a2]]]
        by (metis TM.clean_output_altdef TM.output_of_def TM_abbrevs.input_tape.simps(1)
            option.distinct(1) option.simps(4) tape.sel(3))
    next
      fix w' :: "'a list"
      assume a1: "head (if w' = [] then Tape [] None [] else
                  Tape [] (Some (hd w')) (map Some (tl w'))) = None" and
             a2: "\<not>P w" and
             a3: "last (tapes ((TM.step (Abs_TM M') ^^ (LEAST n.
                  TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                  (TM.initial_config (Abs_TM M') w))))
                  (TM.initial_config (Abs_TM M') w))) =
                  (if w' = [] then Tape [] None []
                  else Tape [] (Some (hd w')) (map Some (tl w')))"
      have 1: "w' = []"
        apply (rule ccontr)
        using a1 by simp
      have [simp]: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                    (TM.initial_config (Abs_TM M') w))) =
                    T1' w + 3 + 2 * length w + T3' w"
        apply standard
        unfolding TM.is_final_def f121 [OF that, simplified, OF a2, of "T3' w"]
         apply simp
        unfolding final_states_def apply auto
        unfolding states_def apply auto
           apply (rule TM_steps_valid_stateI)
        using \<open>UNIV \<subseteq> TM.symbols M\<^sub>L\<close> apply blast
          apply (rule TM_steps_valid_stateI)
        using a10 apply simp
        using T3'_final [of w] unfolding TM.run_def TM.is_final_def apply this
      proof (cases "T3' w = 0")
        case True
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + (length w - 1)))
                 (TM.initial_config (Abs_TM M') w)) =
                 (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
                 TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
                 TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
                 w ! (length w - 1))" using f91 [of "length w - 1" w] that by simp
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 2: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        show False using 2 1 that unfolding final_states_def
          using True f91' by auto
      next
        case False
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        then show False using f121 [OF that, simplified, OF a2, of "T3' w - 1"]
          False [simplified] unfolding final_states_def apply auto
          apply (metis (no_types, lifting) Pair_inject group_cancel.add1 numeral_eq_iff
              semiring_norm(89))+
          unfolding states_def apply auto
           apply (subst (asm) add.assoc)
           apply simp
           apply (metis T3'_min TM.run_def diff_less is_finalI less_Suc0)
          apply (subst (asm) add.assoc)
          apply simp
          by (metis T3'_min TM.is_final_def TM.run_def diff_less less_Suc0)
      qed
      have 2: "last (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + T3' w))
               (TM.initial_config (Abs_TM M') w))) = Tape [] None []"
        using a3 1 by simp
      have *: "\<And>l. l \<noteq> [] \<Longrightarrow> last l = l ! (length l - 1)"
        using last_conv_nth by blast
      have [simp]: "length (tapes ((TM.step (Abs_TM M') ^^
                    (T1' w + 3 + 2 * length w + T3' w))
                    (TM.initial_config (Abs_TM M') w))) = tc"
        by (simp add: TM.run_tapes_len)
      have 3: "last (tapes (TM.steps M\<^sub>g (T3' w) (TM.initial_config M\<^sub>g w))) =
               Tape [] None []" using 2 f122 [OF that, simplified, OF a2,
        of "TM.tape_count M\<^sub>g - 1" "T3' w"] apply auto
        apply (subst (asm) *)
         apply auto
         apply (metis TM.run_def TM.run_tapes_non_empty)
        using 2 3 a2 by argo
      have 4: "TM.clean_output ((TM.step M\<^sub>g ^^
               (LEAST n. TM.is_final M\<^sub>g ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w))))
               (TM.initial_config M\<^sub>g w))"
        unfolding TM.clean_output_def using a8 [unfolded TM.computes_def, THEN spec,
        of w, unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
        TM.compute_def TM.compute_config_def TM.clean_output_of_def]
        by (meson TM.clean_output_def option.distinct(1))
      show "[] = g w" using a8 [unfolded TM.computes_def, THEN spec, of w,
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.compute_def TM.compute_config_def TM.clean_output_of_def]
        using 4 3 unfolding TM.output_of_def Let_def apply simp
        by (metis (no_types, lifting) LeastI T3'_final T3'_min TM.run_def
            TM_abbrevs.input_tape.simps(1) TM_abbrevs.input_tape_empty_hd_iff
            linorder_less_linear not_less_Least option.simps(4))
    next
      assume a1: "head (last (tapes ((TM.step (Abs_TM M') ^^
                  (LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                  (TM.initial_config (Abs_TM M') w))))
                  (TM.initial_config (Abs_TM M') w)))) = None" and
             a2: "\<not> P w"
      
      have [simp]: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                    (TM.initial_config (Abs_TM M') w))) =
                    T1' w + 3 + 2 * length w + T3' w"
        apply standard
        unfolding TM.is_final_def f121 [OF that, simplified, OF a2, of "T3' w"]
         apply simp
        unfolding final_states_def apply auto
        unfolding states_def apply auto
           apply (rule TM_steps_valid_stateI)
        using \<open>UNIV \<subseteq> TM.symbols M\<^sub>L\<close> apply blast
          apply (rule TM_steps_valid_stateI)
        using a10 apply simp
        using T3'_final [of w] unfolding TM.run_def TM.is_final_def apply this
      proof (cases "T3' w = 0")
        case True
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + (length w - 1)))
                 (TM.initial_config (Abs_TM M') w)) =
                 (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
                 TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
                 TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
                 w ! (length w - 1))" using f91 [of "length w - 1" w] that by simp
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 2: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        show False using 2 1 that unfolding final_states_def
          using True f91' by auto
      next
        case False
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        then show False using f121 [OF that, simplified, OF a2, of "T3' w - 1"]
          False [simplified] unfolding final_states_def apply auto
          apply (metis (no_types, lifting) Pair_inject group_cancel.add1 numeral_eq_iff
              semiring_norm(89))+
          unfolding states_def apply auto
           apply (subst (asm) add.assoc)
           apply simp
           apply (metis T3'_min TM.run_def diff_less is_finalI less_Suc0)
          apply (subst (asm) add.assoc)
          apply simp
          by (metis T3'_min TM.is_final_def TM.run_def diff_less less_Suc0)
      qed
      have [simp]: "(LEAST n. TM.is_final M\<^sub>g ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w))) =
                    T3' w" apply standard
        using T3'_final unfolding TM.run_def apply this
        using T3'_min unfolding TM.run_def .
      show "\<exists>w'. last (tapes ((TM.step (Abs_TM M') ^^ (LEAST n.
            TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
            (TM.initial_config (Abs_TM M') w)))) (TM.initial_config (Abs_TM M') w))) =
            (if w' = [] then Tape [] None [] else
            Tape [] (Some (hd w')) (map Some (tl w')))" apply simp
        apply (rule exI [where x="[]"])
        apply auto
        apply (rule tape.expand)
        apply auto
        unfolding 3 [OF a2] apply (rule TM_computes_word_left_is_empty [where wo="g w"])
        using a8 unfolding TM.computes_def apply blast
        using T3'_final [of w] unfolding TM.run_def apply this
        using a1 apply simp
        unfolding 3 [OF a2] apply assumption
        using a1 [simplified, unfolded 3 [OF a2]] a8 [unfolded TM.computes_def, THEN spec,
            of w, unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.compute_def TM.compute_config_def, simplified,
            unfolded TM.clean_output_of_def]
        by (metis TM.clean_outputD TM_abbrevs.input_tape.simps(1)
            TM_abbrevs.input_tape_empty_hd_iff option.discI tape.sel(3))
    next
      fix a :: 'a and w' :: "'a list"
      assume a1: "head (if w' = [] then Tape [] None [] else
                  Tape [] (Some (hd w')) (map Some (tl w'))) = Some a" and
             a2: "P w" and
             a3: "last (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + T2' w))
                  (TM.initial_config (Abs_TM M') w))) =
                  (if w' = [] then Tape [] None [] else
                  Tape [] (Some (hd w')) (map Some (tl w')))"
      have 1: "w' \<noteq> []"
        apply standard
        using a1 by simp
      have [simp]: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some (tl w')) = map Some (tl w')"
        by simp
      have *[simp]: "(LEAST n. TM.is_final M\<^sub>f ((TM.step M\<^sub>f ^^ n)
                     (TM.initial_config M\<^sub>f w))) = T2' w"
        using T2'_min [of _ w] T2'_final [of w] unfolding TM.run_def by blast
      show "a # the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y)
            (right (if w' = [] then Tape [] None []
            else Tape [] (Some (hd w')) (map Some (tl w')))))) = f w"
        using 1 a1 a3 apply simp
        unfolding 2 [OF a2] using a5 [unfolded TM.computes_def, THEN spec, of w,
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.compute_def TM.clean_output_of_def TM.compute_config_def, simplified,
            unfolded TM.output_of_def Let_def *]
        by (simp add: TM.clean_output_altdef TM.output_of_def
            TM_abbrevs.input_tape.simps(2))
    next
      fix a :: 'a
      assume a1: "head (last (tapes ((TM.step (Abs_TM M') ^^
                  (T1' w + 3 + 2 * length w + T2' w))
                  (TM.initial_config (Abs_TM M') w)))) = Some a" and
             a2: "P w"
      have *: "(LEAST n. TM.is_final M\<^sub>f ((TM.step M\<^sub>f ^^ n)
               (TM.initial_config M\<^sub>f w))) = T2' w"
        using T2'_min [of _ w] T2'_final [of w] unfolding TM.run_def by blast
      show "\<exists>w'. last (tapes ((TM.step (Abs_TM M') ^^ (T1' w + 3 + 2 * length w + T2' w))
            (TM.initial_config (Abs_TM M') w))) = (if w' = [] then Tape [] None [] else
            Tape [] (Some (hd w')) (map Some (tl w')))"
        unfolding 2 [OF a2] using a5 [unfolded TM.computes_def, THEN spec, of w,
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.clean_output_of_def TM.compute_def TM.output_of_def Let_def
            TM.compute_config_def *]
        by (metis TM.clean_output_altdef TM_abbrevs.input_tape_def option.distinct(1))
    next
      fix a :: 'a and w' :: "'a list"
      assume a1: "head (if w' = [] then Tape [] None [] else
                  Tape [] (Some (hd w')) (map Some (tl w'))) = Some a" and
             a2: "\<not> P w" and
             a3: "last (tapes ((TM.step (Abs_TM M') ^^
                  (LEAST n. TM.is_final (Abs_TM M')
                  ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))))
                  (TM.initial_config (Abs_TM M') w))) =
                  (if w' = [] then Tape [] None [] else
                  Tape [] (Some (hd w')) (map Some (tl w')))"
      have 1: "w' \<noteq> []"
        apply standard
        using a1 by simp
      have *: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some (tl w')) = map Some (tl w')"
        by simp
      have [simp]: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                    (TM.initial_config (Abs_TM M') w))) =
                    T1' w + 3 + 2 * length w + T3' w"
        apply standard
        unfolding TM.is_final_def f121 [OF that, simplified, OF a2, of "T3' w"]
         apply simp
        unfolding final_states_def apply auto
        unfolding states_def apply auto
           apply (rule TM_steps_valid_stateI)
        using \<open>UNIV \<subseteq> TM.symbols M\<^sub>L\<close> apply blast
          apply (rule TM_steps_valid_stateI)
        using a10 apply simp
        using T3'_final [of w] unfolding TM.run_def TM.is_final_def apply this
      proof (cases "T3' w = 0")
        case True
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + (length w - 1)))
                 (TM.initial_config (Abs_TM M') w)) =
                 (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
                 TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
                 TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
                 w ! (length w - 1))" using f91 [of "length w - 1" w] that by simp
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 2: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        show False using 2 1 that unfolding final_states_def
          using True f91' by auto
      next
        case False
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        then show False using f121 [OF that, simplified, OF a2, of "T3' w - 1"]
          False [simplified] unfolding final_states_def apply auto
          apply (metis (no_types, lifting) Pair_inject group_cancel.add1 numeral_eq_iff
              semiring_norm(89))+
          unfolding states_def apply auto
           apply (subst (asm) add.assoc)
           apply simp
           apply (metis T3'_min TM.run_def diff_less is_finalI less_Suc0)
          apply (subst (asm) add.assoc)
          apply simp
          by (metis T3'_min TM.is_final_def TM.run_def diff_less less_Suc0)
      qed
      have **: "(LEAST n. TM.is_final M\<^sub>g ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w))) =
                T3' w" apply standard
        using T3'_final unfolding TM.run_def apply this
        using T3'_min unfolding TM.run_def .
      show "a # the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right
            (if w' = [] then Tape [] None []
            else Tape [] (Some (hd w')) (map Some (tl w')))))) = g w"
        using 1 a1 a3 apply (simp add: *)
        unfolding 3 [OF a2] using a8 [unfolded TM.computes_def, THEN spec, of w,
            unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
            TM.compute_def TM.compute_config_def TM.clean_output_of_def ** TM.output_of_def
            Let_def] using a1 1 apply simp
        by (metis TM.clean_output_altdef TM.out_config_simps TM.output_of_def
            TM_abbrevs.input_tape.simps(2) option.simps(5))
    next
      fix a :: 'a
      assume a1: "head (last (tapes ((TM.step (Abs_TM M') ^^
                  (LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                  (TM.initial_config (Abs_TM M') w))))
                  (TM.initial_config (Abs_TM M') w)))) = Some a" and
             a2: "\<not> P w"
      have [simp]: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                    (TM.initial_config (Abs_TM M') w))) =
                    T1' w + 3 + 2 * length w + T3' w"
        apply standard
        unfolding TM.is_final_def f121 [OF that, simplified, OF a2, of "T3' w"]
         apply simp
        unfolding final_states_def apply auto
        unfolding states_def apply auto
           apply (rule TM_steps_valid_stateI)
        using \<open>UNIV \<subseteq> TM.symbols M\<^sub>L\<close> apply blast
          apply (rule TM_steps_valid_stateI)
        using a10 apply simp
        using T3'_final [of w] unfolding TM.run_def TM.is_final_def apply this
      proof (cases "T3' w = 0")
        case True
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 3 + length w + (length w - 1)))
                 (TM.initial_config (Abs_TM M') w)) =
                 (4, state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w)),
                 TM.TM.initial_state M\<^sub>f, TM.TM.initial_state M\<^sub>g, 4,
                 TM.TM.label M\<^sub>L (state ((TM.step M\<^sub>L ^^ T1' w) (TM.initial_config M\<^sub>L w))),
                 w ! (length w - 1))" using f91 [of "length w - 1" w] that by simp
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 2: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        show False using 2 1 that unfolding final_states_def
          using True f91' by auto
      next
        case False
        fix n :: nat
        assume a4: "n < T1' w + 3 + 2 * length w + T3' w" and
               a5: "state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))
                    \<in> final_states"
        have "n \<le> T1' w + 2 + 2 * length w + T3' w" using a4 by simp
        hence 1: "state ((TM.step (Abs_TM M') ^^ (T1' w + 2 + 2 * length w + T3' w))
                 (TM.initial_config (Abs_TM M') w)) \<in> final_states"
          using a5 M'_final_states TM.final_mono is_finalI by blast
        then show False using f121 [OF that, simplified, OF a2, of "T3' w - 1"]
          False [simplified] unfolding final_states_def apply auto
          apply (metis (no_types, lifting) Pair_inject group_cancel.add1 numeral_eq_iff
              semiring_norm(89))+
          unfolding states_def apply auto
           apply (subst (asm) add.assoc)
           apply simp
           apply (metis T3'_min TM.run_def diff_less is_finalI less_Suc0)
          apply (subst (asm) add.assoc)
          apply simp
          by (metis T3'_min TM.is_final_def TM.run_def diff_less less_Suc0)
      qed
      show "\<exists>w'. last (tapes ((TM.step (Abs_TM M') ^^
            (LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
            (TM.initial_config (Abs_TM M') w)))) (TM.initial_config (Abs_TM M') w))) =
            (if w' = [] then Tape [] None [] else
            Tape [] (Some (hd w')) (map Some (tl w')))"
        using a1 apply simp
        unfolding 3 [OF a2]
      proof
        assume a1: "head (last (tapes ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w)))) =
                    Some a"
        have *: "(LEAST n. TM.is_final M\<^sub>g ((TM.step M\<^sub>g ^^ n) (TM.initial_config M\<^sub>g w))) =
                 T3' w" apply standard
        using T3'_final unfolding TM.run_def apply this
        using T3'_min unfolding TM.run_def .
      have 4: "(case Some a of None \<Rightarrow> [] | Some h \<Rightarrow> h #
               the (those (takeWhile (\<lambda>s. s \<noteq> None) (right (last
               (tapes ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w)))))))) =
               a # the (those (takeWhile (\<lambda>s. s \<noteq> None) (right (last
               (tapes ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w)))))))"
        by simp
        show "(g w = [] \<longrightarrow> last (tapes ((TM.step M\<^sub>g ^^ T3' w)
              (TM.initial_config M\<^sub>g w))) = Tape [] None []) \<and>
              (g w \<noteq> [] \<longrightarrow> last (tapes ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w))) =
              Tape [] (Some (hd (g w))) (map Some (tl (g w))))"
          using a1 apply auto
          using a8 [unfolded TM.computes_def, THEN spec, of w,
              unfolded TM.computes_word_def, THEN conjunct2, unfolded TM.has_output_def
              TM.compute_def TM.clean_output_of_def TM.compute_config_def TM.output_of_def
              Let_def *] unfolding a1 apply auto
          unfolding 4
        proof -
          assume a1: "(if TM.clean_output ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w))
                      then Some (a # the (those (takeWhile (\<lambda>s. s \<noteq> None)
                      (right (last (tapes ((TM.step M\<^sub>g ^^ T3' w)
                      (TM.initial_config M\<^sub>g w)))))))) else None) = Some (g w)"
          have 1: "TM.clean_output ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w))"
            using a1 by (rule if_Some_P)
          show "last (tapes ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w))) =
                Tape [] (Some (hd (g w))) (map Some (tl (g w)))"
            using a1 1 apply simp
            by (metis (no_types, lifting) ext TM.clean_output_altdef TM.output_of_def
                TM_abbrevs.input_tape.simps(2) a8 [unfolded TM.computes_def, THEN spec,
                  of w, unfolded TM.computes_word_def, THEN conjunct2,
                  unfolded TM.has_output_def TM.compute_def TM.clean_output_of_def
                  TM.compute_config_def TM.output_of_def Let_def *] list.sel(1,3)
                option.inject)
        next
          assume a1: "(if TM.clean_output ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w))
                      then Some (a # the (those (takeWhile (\<lambda>s. s \<noteq> None)
                      (right (last (tapes ((TM.step M\<^sub>g ^^ T3' w)
                      (TM.initial_config M\<^sub>g w)))))))) else None) = Some []"
          have 1: "TM.clean_output ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w))"
            using a1 by (rule if_Some_P)
          show "last (tapes ((TM.step M\<^sub>g ^^ T3' w) (TM.initial_config M\<^sub>g w))) =
                Tape [] None []"
            using a1 1 by simp
        qed
      qed
    qed
  qed
  show "typed_computable_in_time TYPE(nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'a) TYPE(unit)
        (\<lambda>n. T1 n + max (T2 n) (T3 n) + 3 * n + 3) (\<lambda>w. if P w then f w else g w)"
    unfolding typed_computable_in_time_def apply (rule exI [where x="Abs_TM M'"])
  proof auto
    show "TM.computes (Abs_TM M') (\<lambda>w. if P w then f w else g w)"
      unfolding TM.computes_def
    proof
      fix w :: "'a list"
      show "TM.computes_word (Abs_TM M') w (if P w then f w else g w)"
        apply (cases "w = []")
         apply (erule ssubst)
        by fact+
    qed
    show "TM.time_bounded_word (Abs_TM M')
          (\<lambda>n. T1 n + max (T2 n) (T3 n) + 3 * n + 3) w" for w :: "'a list"
      apply (cases "w = []")
       apply (erule ssubst)
      using time_bounded_Nil apply (subst (2) numeral_3_eq_3)
       apply simp
       apply (subst TM.time_bounded_word_def)
       apply (subst (asm) TM.time_bounded_word_def)
       apply (subst TM.run_def)
       apply (subst (asm) TM.run_def)
      apply (meson TM.final_steps_ex_eq le_Suc_eq)
      by fact
    show "\<And>s. s \<in> TM.TM.symbols (Abs_TM M')"
      unfolding valid_tm_symbols [OF valid_M'] unfolding M'_def by simp
  qed
qed

subsection\<open>Reductions\<close>

lemma reduce_DTIME':
  fixes L\<^sub>1 L\<^sub>2
    and f\<^sub>R \<comment> \<open>the reduction\<close>
    and T :: "nat \<Rightarrow> nat"
    and l\<^sub>R :: "nat \<Rightarrow> nat" \<comment> \<open>length bound of the reduction\<close>
    and P :: "'s \<Rightarrow> bool"
  assumes "L\<^sub>1 \<in> DTIME(T)"
    and finite_P: "finite {s. P s}"
    and alphabet_L1: "alphabet L\<^sub>1 \<subseteq> {s. P s}"
    and alphabet_L2: "alphabet L\<^sub>2 \<subseteq> {s. P s}"
    and f\<^sub>R_MOST: "\<forall>\<^sub>\<infinity>w. (\<forall>s\<in>set w. P s) \<longrightarrow> (f\<^sub>R w \<in>\<^sub>L L\<^sub>1 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>2) \<and> (length (f\<^sub>R w) \<le> l\<^sub>R (length w))"
    and "computable_in_time T f\<^sub>R"
    and "superlinear T"
    and T_l\<^sub>R_mono: "\<forall>\<^sub>\<infinity>n. T (l\<^sub>R n) \<ge> T(n)" \<comment> \<open>allows reasoning about \<^term>\<open>T\<close> and \<^term>\<open>l\<^sub>R\<close> as if both were \<^const>\<open>mono\<close>.\<close>
  shows "L\<^sub>2 \<in> DTIME (tcomp (\<lambda>n. T(l\<^sub>R n)))" \<comment> \<open>Reducing \<^term>\<open>L\<^sub>2\<close> to \<^term>\<open>L\<^sub>1\<close>\<close>
proof (rule DTIME_ae_tcomp, standard, auto)
  obtain M\<^sub>1 :: "(nat, 's) TM_decider" where M\<^sub>1_symbols: "alphabet L\<^sub>1 \<subseteq> TM.TM.symbols M\<^sub>1" and
    M\<^sub>1_decides: "\<And>w. set w \<subseteq> alphabet L\<^sub>1 \<Longrightarrow> TM_decider.decides_word M\<^sub>1 L\<^sub>1 w" and
    M\<^sub>1_tb: "\<And>w. set w \<subseteq> TM.symbols M\<^sub>1 \<Longrightarrow> TM.time_bounded_word M\<^sub>1 T w"
    using assms(1) by auto
  define M :: "(nat, 's, bool) TM_record" where "M \<equiv> undefined"
  show "s \<in> TM.symbols (Abs_TM M)" if "s \<in> alphabet L\<^sub>2" for s :: 's sorry
  show "\<forall>\<^sub>\<infinity>w. set w \<subseteq> alphabet L\<^sub>2 \<longrightarrow> TM_decider.decides_word (Abs_TM M) L\<^sub>2 w \<and>
        TM.time_bounded_word (Abs_TM M) (\<lambda>x. T (l\<^sub>R x)) w" sorry
qed

lemma reduce_DTIME:
  fixes L\<^sub>1 L\<^sub>2
    and f\<^sub>R
    and T :: "nat \<Rightarrow> nat"
    and P :: "'s \<Rightarrow> bool"
  assumes "L\<^sub>1 \<in> DTIME T"
    and "finite {s. P s}"
    and "alphabet L\<^sub>1 \<subseteq> {s. P s}"
    and "alphabet L\<^sub>2 \<subseteq> {s. P s}"
    and "\<forall>\<^sub>\<infinity>w. (\<forall>s\<in>set w. P s) \<longrightarrow> (f\<^sub>R w \<in>\<^sub>L L\<^sub>1 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>2) \<and> length (f\<^sub>R w) \<le> length w"
    and "computable_in_time T f\<^sub>R"
    and "superlinear T"
  shows "L\<^sub>2 \<in> DTIME (tcomp T)"
  using \<open>L\<^sub>1 \<in> DTIME T\<close>
  by (elim reduce_DTIME'[where l\<^sub>R="\<lambda>x. x"]) (fact+, simp)

(* Probably also works without the assumption finite (alphabet L) *)
lemma poly_reducible_refl: "finite (alphabet L) \<Longrightarrow> L \<le>\<^sub>p L"
proof (rule poly_reducibleI')
  assume a1: "finite (alphabet L)"
  define M :: "(nat, 'a, unit) TM_record" where "M \<equiv> halting_TM_rec 0 ((alphabet L) \<union> {undefined}) undefined"
  have valid_M [simp, intro]: "valid_TM M"
    unfolding M_def apply (rule halting_TM_valid)
    using a1 by auto
  show "0 \<le> n^0" for n :: nat by simp
  show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M)"
    unfolding valid_tm_symbols [OF valid_M] unfolding M_def halting_TM_rec_def by auto
  thus "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M)" .
  fix w :: "'a list"
  assume a2: "set w \<subseteq> alphabet L"
  show "(w \<in>\<^sub>L L) = ((\<lambda>w. w) w \<in>\<^sub>L L)" ..
  show tb: "TM.time_bounded_word (Abs_TM M) (\<lambda>_. 0) w"
    unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def apply simp
    unfolding valid_tm_final_states [OF valid_M] TM.initial_config_def apply simp
    unfolding valid_tm_initial_state [OF valid_M] unfolding M_def halting_TM_rec_def by simp
  show "TM.computes_word (Abs_TM M) w w"
    unfolding TM.computes_word_def apply (rule conjI)
    using tb unfolding TM.time_bounded_word_def TM.halts_def TM.halts_config_def TM.run_def apply (rule exI)
  proof -
    have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) = 0"
      apply (rule Least_nat_monoI)
        apply simp_all
      using tb unfolding TM.time_bounded_word_def TM.run_def by simp
    have 2: "TM.clean_output (TM.initial_config (Abs_TM M) w)"
      unfolding TM.clean_output_def TM.initial_config_def apply auto
      apply (rule exI [where x="[]"])
      unfolding TM_abbrevs.input_tape_def by simp
    have 3: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some (tl w)) = map Some (tl w)" by fastforce
    show "TM.has_output (TM.compute (Abs_TM M) w) w"
      unfolding TM.has_output_def TM.compute_def TM.compute_config_def 1 apply simp
      unfolding TM.clean_output_of_def apply (auto simp add: 2)
      unfolding TM.output_of_def Let_def TM.initial_config_def apply auto
      unfolding TM_abbrevs.input_tape_def apply auto
      unfolding 3 apply simp
      unfolding valid_tm_tape_count [OF valid_M] unfolding M_def halting_TM_rec_def by simp
  qed
qed
end
