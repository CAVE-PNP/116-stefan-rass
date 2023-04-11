subsection\<open>TM Transformations\<close>

theory Transformations
  imports TM Complexity
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
      unfolding take_replicate by argo

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


subsection\<open>Reductions\<close>

lemma reduce_DTIME':
  fixes L\<^sub>1 L\<^sub>2
    and f\<^sub>R \<comment> \<open>the reduction\<close>
    and T :: "nat \<Rightarrow> nat"
    and l\<^sub>R :: "nat \<Rightarrow> nat" \<comment> \<open>length bound of the reduction\<close>
  assumes "L\<^sub>1 \<in> DTIME(T)"
    and f\<^sub>R_MOST: "\<forall>\<^sub>\<infinity>w. (f\<^sub>R w \<in>\<^sub>L L\<^sub>1 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>2) \<and> (length (f\<^sub>R w) \<le> l\<^sub>R (length w))"
    and "computable_in_time T f\<^sub>R"
    and "superlinear T"
    and T_l\<^sub>R_mono: "\<forall>\<^sub>\<infinity>n. T (l\<^sub>R n) \<ge> T(n)" \<comment> \<open>allows reasoning about \<^term>\<open>T\<close> and \<^term>\<open>l\<^sub>R\<close> as if both were \<^const>\<open>mono\<close>.\<close>
  shows "L\<^sub>2 \<in> DTIME(\<lambda>n. T(l\<^sub>R n))" \<comment> \<open>Reducing \<^term>\<open>L\<^sub>2\<close> to \<^term>\<open>L\<^sub>1\<close>\<close>
  sorry (* TODO (!) *)

lemma reduce_DTIME:
  fixes L\<^sub>1 L\<^sub>2
    and f\<^sub>R
    and T :: "nat \<Rightarrow> nat"
  assumes "L\<^sub>1 \<in> DTIME T"
    and "\<forall>\<^sub>\<infinity>w. (f\<^sub>R w \<in>\<^sub>L L\<^sub>1 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>2) \<and> length (f\<^sub>R w) \<le> length w"
    and "computable_in_time T f\<^sub>R"
    and "superlinear T"
  shows "L\<^sub>2 \<in> DTIME T"
  using \<open>L\<^sub>1 \<in> DTIME T\<close>
  by (elim reduce_DTIME'[where l\<^sub>R="\<lambda>x. x"]) (fact+, simp)

end
