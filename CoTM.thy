theory CoTM
  imports "Supplementary/Lists" "Supplementary/Option_S" Computability
begin
codatatype cnat = CSuc cnat

lemma CSuc_cn_is_cn [simp]: "CSuc cn = cn"
  using cnat.coinduct by simp

lemma cnats_unique: "(cn1 :: cnat) = cn2"
  using cnat.coinduct [of "\<lambda>_ _. True"] by simp

codatatype 'a clist = CCons (chd: 'a) (ctl: "'a clist")

primcorec replicated_clist :: "'a \<Rightarrow> 'a clist" where
  "replicated_clist a = CCons a (replicated_clist a)"

fun nth_clist :: "'a clist \<Rightarrow> nat \<Rightarrow> 'a" where
  "nth_clist (CCons h _) 0 = h" |
  "nth_clist (CCons _ t) (Suc n) = nth_clist t n"

lemma set_clist_range_nth: "set_clist cl = range (nth_clist cl)"
proof auto
  fix x :: 'a
  assume a1: "x \<in> set_clist cl"
  show "x \<in> range (nth_clist cl)" using a1
    apply (induction rule: clist.set_induct)
    unfolding image_def apply auto
     apply (rule exI [where x=0])
     apply simp
    by (metis nth_clist.simps(2))
next
  fix n :: nat
  show "nth_clist cl n \<in> set_clist cl"
    apply (cases cl)
    apply (erule ssubst)
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case
      by (metis Suc nth_clist.simps(2) clist.set_intros(2) clist.exhaust)
  qed
qed

lemma set_clist_replicated_singleton [iff]: "set_clist (replicated_clist a) = {a}"
  unfolding set_clist_range_nth
proof auto
  fix n :: nat
  show "nth_clist (replicated_clist a) n = a"
  proof (induction n)
    case 0
    then show ?case apply (subst replicated_clist.code)
      by simp
  next
    case (Suc n)
    then show ?case apply (subst replicated_clist.code)
      by simp
  qed
next
  show "a \<in> range (nth_clist (replicated_clist a))"
    unfolding image_def apply auto
    apply (rule exI [where x=0])
    apply (cases "replicated_clist a")
    apply (subst replicated_clist.code)
    by simp
qed

lemma zeroth_clist_is_chd [simp]: "nth_clist cl 0 = chd cl"
  by (cases cl) simp

lemma Sucth_clist_from_ctl: "nth_clist cl (Suc n) = nth_clist (ctl cl) n"
  by (cases cl) simp

lemma nth_clist_unique_spec: "(\<And>n. nth_clist cl1 n = nth_clist cl2 n) \<Longrightarrow> cl1 = cl2"
  apply (coinduct rule: clist.coinduct [where R="\<lambda>cl1 cl2. \<forall>n. nth_clist cl1 n = nth_clist cl2 n"])
   apply auto
   apply (drule spec [where x=0])
   apply simp
  unfolding Sucth_clist_from_ctl [symmetric] by simp

lemma nth_clist_replicate [simp]: "nth_clist (replicated_clist a) n = a"
proof (induction n)
  case 0
  then show ?case apply (subst replicated_clist.code)
    by simp
next
  case (Suc n)
  then show ?case by (simp add: Sucth_clist_from_ctl)
qed

lemma replicated_clist_ctl_eq: "cl = replicated_clist a \<Longrightarrow> cl = ctl (replicated_clist a)"
  by simp

lemma map_clist_nth [simp]: "nth_clist (map_clist f cl) n = f (nth_clist cl n)"
proof (induction n arbitrary: cl)
  case 0
  then show ?case by (simp add: clist.map_sel(1))
next
  case (Suc n)
  show ?case apply (cases cl)
    apply simp
    by (rule Suc)
qed

primcorec clist_from_f :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a clist" where
  "clist_from_f f n = CCons (f n) (clist_from_f f (Suc n))"

lemma nth_clist_from_sum: "nth_clist (clist_from_f f n) m = nth_clist (clist_from_f f 0) (n + m)"
proof (induction n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case using Suc [where m="Suc m"] by (simp add: Sucth_clist_from_ctl)
qed

lemma ex1_from_f: "\<exists>!cl. (\<forall>n. nth_clist cl n = f n)"
proof (rule ex1I')
  show "\<exists>cl. \<forall>n. nth_clist cl n = f n"
  proof
    show "\<forall>n. nth_clist (clist_from_f f 0) n = f n"
    proof
      fix n :: nat
      show "nth_clist (clist_from_f f 0) n = f n"
        using nth_clist_from_sum [of f n 0, simplified, symmetric] .
    qed
  qed
  show "\<exists>\<^sub>\<le>\<^sub>1 cl. \<forall>n. nth_clist cl n = f n"
    apply standard
    apply (rule nth_clist_unique_spec)
    by simp
qed

lemma replicated_clist_eq_iff: "cl = replicated_clist a \<longleftrightarrow> (\<forall>i. nth_clist cl i = a)"
  by (auto intro: nth_clist_unique_spec)

definition prepend_list :: "'a list \<Rightarrow> 'a clist \<Rightarrow> 'a clist" where
  "prepend_list l cl \<equiv> THE pcl. (\<forall>n. nth_clist pcl n = (if n < length l then l ! n else
                        nth_clist cl (n - length l)))"

lemmas implicit_clist_def = theI' [OF ex1_from_f, THEN spec]

lemma prepend_list_characteristic: "nth_clist (prepend_list l cl) n =
                                    (if n < length l then l ! n else nth_clist cl (n - length l))"
  unfolding prepend_list_def by (rule implicit_clist_def)

lemma prepend_list_nth_less: "n < length l \<Longrightarrow> nth_clist (prepend_list l cl) n = l ! n"
  unfolding prepend_list_characteristic by simp

lemma prepend_list_nth_ge: "n \<ge> length l \<Longrightarrow> nth_clist (prepend_list l cl) n =
                            nth_clist cl (n - length l)"
  unfolding prepend_list_characteristic by simp

lemma set_clist_prepend_list: "set_clist (prepend_list l cl) = set l \<union> set_clist cl"
  apply (auto iff: set_clist_range_nth)
    apply (metis in_set_conv_nth prepend_list_characteristic rangeI)
   apply (metis prepend_list_characteristic in_set_conv_nth image_eqI UNIV_I)
  unfolding image_def apply auto
proof
  fix n :: nat
  show "nth_clist cl n = nth_clist (prepend_list l cl) (length l + n)"
    by (subst prepend_list_nth_ge) simp_all
qed

lemma prepend_list_empty [simp]: "prepend_list [] cl = cl"
proof (rule nth_clist_unique_spec)
  fix n :: nat
  show "nth_clist (prepend_list [] cl) n = nth_clist cl n"
  proof (cases "n < length []")
    case True
    then show ?thesis by simp
  next
    case False
    hence 1: "n \<ge> length []" by simp
    show ?thesis unfolding prepend_list_nth_ge [OF 1] by simp
  qed
qed

lemma prepend_list_Cons [simp]: "prepend_list (h#t) cl = CCons h (prepend_list t cl)"
proof (rule nth_clist_unique_spec)
  fix n :: nat
  show "nth_clist (prepend_list (h # t) cl) n = nth_clist (CCons h (prepend_list t cl)) n"
  proof (cases "n < length (h#t)")
    case True
    then show ?thesis apply (subst prepend_list_nth_less)
       apply simp_all
      apply (cases n)
       apply simp_all
      apply (subst prepend_list_nth_less)
      by simp_all
  next
    case False
    then show ?thesis apply (subst prepend_list_nth_ge)
       apply auto
      apply (cases n)
       apply auto
      apply (subst prepend_list_nth_ge)
      by simp_all
  qed
qed

lemma ctl_prepend_list: "xs \<noteq> [] \<Longrightarrow> ctl (prepend_list xs cl) = prepend_list (tl xs) cl"
proof (rule nth_clist_unique_spec)
  fix n :: nat
  show "xs \<noteq> [] \<Longrightarrow> nth_clist (ctl (prepend_list xs cl)) n = nth_clist (prepend_list (tl xs) cl) n"
    apply (cases "n < length (tl xs)")
     apply auto
     apply (subst prepend_list_nth_less)
      apply simp
    unfolding Sucth_clist_from_ctl [symmetric] apply (subst prepend_list_nth_less)
      apply simp
     apply (simp add: nth_tl)
    apply (subst (1 2) prepend_list_nth_ge)
    by simp_all
qed

datatype 's ctape = CTape (cleft: "'s option clist") (chead: "'s option") (cright: "'s option clist")

definition empty_ctape :: "'s ctape" where
  "empty_ctape \<equiv> CTape (replicated_clist None) None (replicated_clist None)"

datatype ('q, 's) CTM_config = CTM_config
  (cstate: 'q) \<comment> \<open>the current state\<close>
  (ctapes: "'s ctape list") \<comment> \<open>current contents of all tapes\<close>

fun CPred :: "cnat \<Rightarrow> cnat" where
  "CPred (CSuc n) = n"

lemma CSuc_CPred_id: "CSuc (CPred n) = n" 
  by (rule cnats_unique)

definition transpose_list_clists :: "'s clist list \<Rightarrow> 's list clist" where
  "transpose_list_clists l \<equiv> THE cl. (\<forall>n. nth_clist cl n = map (\<lambda>i. nth_clist (l ! i) n) [0..<length l])"

lemma transpose_list_clists_characteristic: "nth_clist (transpose_list_clists l) n =
                                             map (\<lambda>i. nth_clist (l ! i) n) [0..<length l]"
  unfolding transpose_list_clists_def by (rule implicit_clist_def)

lemma transpose_list_clists_length_nth [simp]: "length (nth_clist (transpose_list_clists l) n) = length l"
  unfolding transpose_list_clists_characteristic by simp

lemma transpose_list_clists_length_hd [simp]: "length (chd (transpose_list_clists l)) = length l"
  unfolding transpose_list_clists_length_nth [of _ 0, simplified] ..

lemma tranpose_list_clists_nth: "i < length l \<Longrightarrow> (nth_clist (transpose_list_clists l) n) ! i =
                                 nth_clist (l ! i) n"
  unfolding transpose_list_clists_characteristic by simp

lemma nat_functions_clists_equal: "\<exists>f::(nat \<Rightarrow> 'a) \<Rightarrow> 'a clist. bij f"
proof -
  have 1: "\<And>f f'::nat \<Rightarrow> 'a. (THE cl. \<forall>n. nth_clist cl n = f n) = (THE cl. \<forall>n. nth_clist cl n = f' n) \<Longrightarrow> f = f'"
  proof
    fix f f' :: "nat \<Rightarrow> 'a" and n :: nat
    assume a1: "(THE cl. \<forall>n. nth_clist cl n = f n) = (THE cl. \<forall>n. nth_clist cl n = f' n)"
    have 1: "\<forall>n. nth_clist (THE cl. \<forall>n. nth_clist cl n = f n) n = f n"
      by (rule theI') (rule ex1_from_f)
    have 2: "\<forall>n. nth_clist (THE cl. \<forall>n. nth_clist cl n = f' n) n = f' n"
      by (rule theI') (rule ex1_from_f)
    show "f n = f' n" apply (subst 1 [THEN spec, symmetric])
      apply (subst 2 [THEN spec, symmetric])
      unfolding a1 ..
  qed
  have "inj (\<lambda>f::nat \<Rightarrow> 'a. (THE cl. \<forall>n. nth_clist cl n = f n))"
    by (rule injI) (erule 1)
  moreover have "inj nth_clist"
    apply (rule injI)
    apply (rule nth_clist_unique_spec)
    by simp
  ultimately show "\<exists>f::(nat \<Rightarrow> 'a) \<Rightarrow> 'a clist. bij f"
    by (rule inj_inj_implies_bij_exists)
qed

lemma inj_on_to_list_exists: "finite (S :: 'a set) \<Longrightarrow> \<exists>f::'a \<Rightarrow> 'b list. inj_on f S"
proof -
  fix s :: 'b
  assume a1: "finite S"
  then obtain pre_f :: "'a \<Rightarrow> nat" where pre_f_inj: "inj_on pre_f S"
    by (metis a1 finite_imp_inj_to_nat_fix_one)
  define f :: "'a \<Rightarrow> 'b list" where "\<And>a. f a \<equiv> replicate (pre_f a) s"
  show "\<exists>f::'a \<Rightarrow> 'b list. inj_on f S"
  proof
    show "inj_on f S" apply (rule inj_onI)
      unfolding f_def apply simp
      using pre_f_inj by (rule inj_onD)
  qed
qed

primcorec czip :: "'a clist \<Rightarrow> 'a clist \<Rightarrow> ('a \<times> 'a) clist" where
  "czip cl1 cl2 = CCons (chd cl1, chd cl2) (czip (ctl cl1) (ctl cl2))"

lemma nth_clist_czip: "nth_clist (czip cl1 cl2) n = (nth_clist cl1 n, nth_clist cl2 n)"
proof (induction n arbitrary: cl1 cl2)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases cl1)
    case (CCons h1 t1)
    show "nth_clist (czip cl1 cl2) (Suc n) = (nth_clist cl1 (Suc n), nth_clist cl2 (Suc n))" unfolding CCons
    proof (cases cl2)
      case (CCons h2 t2)
      then show "nth_clist (czip (CCons h1 t1) cl2) (Suc n) =
                 (nth_clist (CCons h1 t1) (Suc n), nth_clist cl2 (Suc n))" unfolding CCons apply simp
        unfolding Suc [symmetric] by (simp add: Sucth_clist_from_ctl)
    qed
  qed
qed

fun ctake :: "nat \<Rightarrow> 'a clist \<Rightarrow> 'a list" where
  "ctake 0 cl = []" |
  "ctake (Suc n) cl = (chd cl)#(ctake n (ctl cl))"

fun cdrop :: "nat \<Rightarrow> 'a clist \<Rightarrow> 'a clist" where
  "cdrop 0 cl = cl" |
  "cdrop (Suc n) cl = cdrop n (ctl cl)"

lemma ctake_length [simp]: "length (ctake n cl) = n"
proof (induction n arbitrary: cl)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma ctake_cdrop_id: "prepend_list (ctake n cl) (cdrop n cl) = cl"
proof (induction n arbitrary: cl)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma ctake_nth: "i < n \<Longrightarrow> (ctake n cl) ! i = nth_clist cl i"
proof (induction n arbitrary: i cl)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "i = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Suc(1) [of "i - 1"] Suc(2)
      by (metis ctake_cdrop_id ctake_length prepend_list_nth_less)
  qed
qed

lemma ctake_hd [simp]: "n > 0 \<Longrightarrow> hd (ctake n cl) = chd cl"
proof (induction n arbitrary: cl)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma cdrop_nth: "nth_clist (cdrop n cl) i = nth_clist cl (i + n)"
proof (induction n arbitrary: cl i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case apply simp
    unfolding Suc by (simp add: Sucth_clist_from_ctl)
qed

lemma cdrop_chd [simp]: "chd (cdrop n cl) = nth_clist cl n"
  by (rule cdrop_nth [of n cl 0, simplified])

lemma ctake_prepend_list1: "n \<le> length l \<Longrightarrow> ctake n (prepend_list l cl) = take n l"
proof (rule nth_equalityI)
  assume a1: "n \<le> length l"
  thus "length (ctake n (prepend_list l cl)) = length (take n l)" by simp
  fix i :: nat
  assume a2: "i < length (ctake n (prepend_list l cl))"
  note 1 = a2 [simplified]
  show "ctake n (prepend_list l cl) ! i = take n l ! i"
    using 1 apply simp
    unfolding ctake_nth by (meson a1 order_less_le_trans prepend_list_nth_less)
qed

lemma ctake_prepend_list2: "n > length l \<Longrightarrow> ctake n (prepend_list l cl) = l @ (ctake (n - length l) cl)"
proof (rule nth_equalityI)
  assume a1: "length l < n"
  thus "length (ctake n (prepend_list l cl)) = length (l @ ctake (n - length l) cl)" by simp
  fix i :: nat
  assume a2 [simplified]: "i < length (ctake n (prepend_list l cl))"
  show "ctake n (prepend_list l cl) ! i = (l @ ctake (n - length l) cl) ! i"
    unfolding ctake_nth [OF a2] nth_append using a1 a2 apply auto
    apply (simp add: prepend_list_nth_less)
    by (simp add: ctake_nth prepend_list_nth_ge)
qed

lemma cdrop_prepend_list1: "n \<le> length l \<Longrightarrow> cdrop n (prepend_list l cl) = prepend_list (drop n l) cl"
proof (rule nth_clist_unique_spec)
  fix i :: nat
  assume a1: "n \<le> length l"
  show "nth_clist (cdrop n (prepend_list l cl)) i = nth_clist (prepend_list (drop n l) cl) i"
    unfolding cdrop_nth
  proof (cases "i + n < length l")
    case True
    show "nth_clist (prepend_list l cl) (i + n) = nth_clist (prepend_list (drop n l) cl) i"
      unfolding prepend_list_nth_less [OF True] apply (subst prepend_list_nth_less)
      using True apply simp
      apply (subst nth_drop)
       apply fact
      apply (subst add.commute)
      ..
  next
    case False
    hence 1: "i + n \<ge> length l" by simp
    show "nth_clist (prepend_list l cl) (i + n) = nth_clist (prepend_list (drop n l) cl) i"
      unfolding prepend_list_nth_ge [OF 1] apply (subst prepend_list_nth_ge)
      using 1 apply auto
      by (simp add: a1)
  qed
qed

lemma cdrop_prepend_list2: "n > length l \<Longrightarrow> cdrop n (prepend_list l cl) = cdrop (n - length l) cl"
proof (rule nth_clist_unique_spec)
  fix i :: nat
  assume a1: "length l < n"
  show "nth_clist (cdrop n (prepend_list l cl)) i = nth_clist (cdrop (n - length l) cl) i"
    unfolding cdrop_nth using prepend_list_nth_ge [of l "i + n" cl] a1 by simp
qed

lemma ctl_cdrop: "ctl (cdrop n cl) = cdrop n (ctl cl)"
proof (induction n arbitrary: cl)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

fun (in TM_abbrevs) ctape_shift :: "head_move \<Rightarrow> 's ctape \<Rightarrow> 's ctape" where
  "ctape_shift Shift_Left (CTape (CCons lh lt) h r) = CTape lt lh (CCons h r)"
| "ctape_shift Shift_Right (CTape l h (CCons rh rt)) = CTape (CCons h l) rh rt"
| "ctape_shift No_Shift tp = tp"

lemma (in TM_abbrevs) left_ctape_shift_left: "cleft (ctape_shift Shift_Left ct) = ctl (cleft ct)"
proof (cases ct)
  case (CTape l h r)
  show ?thesis unfolding CTape
  proof (cases l)
    case (CCons h2 t)
    show "cleft (ctape_shift Shift_Left (CTape l h r)) = ctl (cleft (CTape l h r))"
      unfolding CCons by simp
  qed
qed

lemma (in TM_abbrevs) head_ctape_shift_left: "chead (ctape_shift Shift_Left ct) = chd (cleft ct)"
proof (cases ct)
  case (CTape l h r)
  show ?thesis unfolding CTape
  proof (cases l)
    case (CCons h2 t)
    show "chead (ctape_shift Shift_Left (CTape l h r)) = chd (cleft (CTape l h r))" unfolding CCons by simp
  qed
qed

lemma (in TM_abbrevs) right_ctape_shift_left: "cright (ctape_shift Shift_Left ct) = CCons (chead ct) (cright ct)"
proof (cases ct)
  case (CTape l h r)
  show ?thesis unfolding CTape
  proof (cases l)
    case (CCons h2 t)
    show "cright (ctape_shift Shift_Left (CTape l h r)) =
          CCons (chead (CTape l h r)) (cright (CTape l h r))" unfolding CCons by simp
  qed
qed

lemma (in TM_abbrevs) right_ctape_shift_right: "cright (ctape_shift Shift_Right ct) = ctl (cright ct)"
proof (cases ct)
  case (CTape l h r)
  show ?thesis unfolding CTape
  proof (cases r)
    case (CCons h2 t)
    show "cright (ctape_shift Shift_Right (CTape l h r)) = ctl (cright (CTape l h r))"
      unfolding CCons by simp
  qed
qed

lemma (in TM_abbrevs) head_ctape_shift_right: "chead (ctape_shift Shift_Right ct) = chd (cright ct)"
proof (cases ct)
  case (CTape l h r)
  show ?thesis unfolding CTape
  proof (cases r)
    case (CCons h2 t)
    show "chead (ctape_shift Shift_Right (CTape l h r)) = chd (cright (CTape l h r))" unfolding CCons by simp
  qed
qed

lemma (in TM_abbrevs) left_ctape_shift_right: "cleft (ctape_shift Shift_Right ct) = CCons (chead ct) (cleft ct)"
proof (cases ct)
  case (CTape l h r)
  show ?thesis unfolding CTape
  proof (cases r)
    case (CCons h2 t)
    show "cleft (ctape_shift Shift_Right (CTape l h r)) =
          CCons (chead (CTape l h r)) (cleft (CTape l h r))" unfolding CCons by simp
  qed
qed

definition (in TM_abbrevs) ctape_write :: "'s option \<Rightarrow> 's ctape \<Rightarrow> 's ctape"
  where "ctape_write s tp = CTape (cleft tp) s (cright tp)"

lemma left_ctape_write [simp]: "cleft (TM_abbrevs.ctape_write s tp) = cleft tp"
  unfolding TM_abbrevs.ctape_write_def by simp

lemma right_ctape_write [simp]: "cright (TM_abbrevs.ctape_write s tp) = cright tp"
  unfolding TM_abbrevs.ctape_write_def by simp

lemma head_ctape_write [simp]: "chead (TM_abbrevs.ctape_write s tp) = s"
  unfolding TM_abbrevs.ctape_write_def by simp

definition (in TM) ctape_action :: "('s option \<times> head_move) \<Rightarrow> 's ctape \<Rightarrow> 's ctape"
  where "ctape_action a tp = ctape_shift (snd a) (ctape_write (fst a) tp)"

abbreviation cheads :: "('q, 's) CTM_config \<Rightarrow> 's option list"
  where "cheads c \<equiv> map chead (ctapes c)"

definition (in TM) cstep_not_final :: "('q, 's) CTM_config \<Rightarrow> ('q, 's) CTM_config"
  where "cstep_not_final c = (let q=cstate c; hds=cheads c in CTM_config
         (next_state q hds) (map2 ctape_action (next_actions q hds) (ctapes c)))"

lemma (in TM) cstep_not_final_simps:
  shows "cstate (cstep_not_final c) = next_state (cstate c) (cheads c)"
    and "ctapes (cstep_not_final c) = map2 ctape_action (next_actions (cstate c) (cheads c)) (ctapes c)"
  unfolding cstep_not_final_def by (simp_all add: Let_def)

lemma (in TM) cstep_not_final_eqI:
  assumes l: "length tps = k"
    and l': "length tps' = k"
    and "\<And>i. i < k \<Longrightarrow>
         ctape_action (next_write q hds i, next_move q hds i) (tps ! i) = tps' ! i"
  shows "map2 ctape_action (next_actions q hds) tps = tps'"
proof (rule nth_equalityI, unfold length_map length_zip next_actions_simps l l' min.idem)
  fix i assume "i < k"
  then have [simp]: "[0..<k] ! i = i" by simp

  from \<open>i < k\<close> have "map2 ctape_action (next_actions q hds) tps ! i =
                     ctape_action (next_actions q hds ! i) (tps ! i)"
    by (intro nth_map2) (auto simp add: l)
  also from \<open>i < k\<close> have "... = ctape_action (next_write q hds i, next_move q hds i) (tps ! i)" by simp
  also from assms(3) and \<open>i < k\<close> have "... = tps' ! i" .
  finally show "map2 ctape_action (next_actions q hds) tps ! i = tps' ! i" .
qed (rule refl)

lemmas CTM_config_eq = CTM_config.expand[OF conjI]

lemma cstep_not_final_eqI1:
  fixes f\<^sub>q f\<^sub>t\<^sub>p\<^sub>s
  assumes f_def: "f = (\<lambda>c. case c of CTM_config q tps \<Rightarrow> CTM_config (f\<^sub>q q) (f\<^sub>t\<^sub>p\<^sub>s tps))"
  assumes q: "f\<^sub>q (TM.next_state M1 (cstate c) (cheads c)) =
              TM.next_state M2 (f\<^sub>q (cstate c)) (map chead (f\<^sub>t\<^sub>p\<^sub>s (ctapes c)))"
    and tps: "f\<^sub>t\<^sub>p\<^sub>s (ctapes (TM.cstep_not_final M1 c)) = ctapes (TM.cstep_not_final M2 (f c))"
  shows "f (TM.cstep_not_final M1 c) = TM.cstep_not_final M2 (f c)"
proof -
  have [simp]: "cstate (f c) = f\<^sub>q (cstate c)" "ctapes (f c) = f\<^sub>t\<^sub>p\<^sub>s (ctapes c)" for c
    by (induction c) (auto simp: f_def)
  from q tps show ?thesis apply (intro CTM_config_eq)
     apply auto
    by (simp add: TM.cstep_not_final_simps(1))
qed

definition (in TM) cstep :: "('q, 's) CTM_config \<Rightarrow> ('q, 's) CTM_config"
  where "cstep c = (if cstate c \<in> F then c else cstep_not_final c)"

abbreviation (in TM) "csteps n \<equiv> cstep ^^ n"

definition (in TM) cis_final :: "('q, 's) CTM_config \<Rightarrow> bool" where
  "cis_final c \<equiv> cstate c \<in> F"

abbreviation (in TM) "cis_not_final c \<equiv> \<not> cis_final c"

lemma cis_final_sub_imp: "TM.cis_final M ((TM.cstep M ^^ (k - l)) c) \<Longrightarrow>
                          TM.cis_final M ((TM.cstep M ^^ k) c)"
proof (induction l)
  case 0
  then show ?case by simp
next
  case (Suc l)
  show ?case apply (rule Suc(1))
    apply (cases "k - l = 0")
    using Suc(2) apply simp
  proof -
    assume a1: "k - l \<noteq> 0"
    have 1: "k - l = Suc (k - Suc l)" using a1 by simp
    show "TM.cis_final M ((TM.cstep M ^^ (k - l)) c)"
      unfolding 1 apply simp
      using Suc(2) by (metis Suc.prems TM.cstep_def TM.cis_final_def)
  qed
  qed

corollary (in TM) cstep_simps:
  shows cstep_final: "cis_final c \<Longrightarrow> cstep c = c"
    and cstep_not_final: "\<not> cis_final c \<Longrightarrow> cstep c = cstep_not_final c"
  unfolding cstep_def cis_final_def by auto

corollary (in TM) csteps_plus[simp]: "csteps n2 (csteps n1 c) = csteps (n1 + n2) c"
  unfolding add.commute[of n1 n2] funpow_add comp_def ..

lemma cstepI: "(TM.cis_final M c \<Longrightarrow> P c) \<Longrightarrow> (\<not>TM.cis_final M c \<Longrightarrow> P (TM.cstep_not_final M c)) \<Longrightarrow>
               P (TM.cstep M c)" unfolding TM.cstep_def apply auto
  by (metis TM.cis_final_def)+

fun (in TM_abbrevs) cinput_tape :: "'s list \<Rightarrow> 's ctape" ("<_>\<^sub>c\<^sub>t\<^sub>p") where
  "<[]>\<^sub>c\<^sub>t\<^sub>p = empty_ctape"
| "<x # xs>\<^sub>c\<^sub>t\<^sub>p = CTape (replicated_clist None) (Some x) (prepend_list (map Some xs) (replicated_clist None))"

lemma (in TM_abbrevs) cinput_tape_def: "<w>\<^sub>c\<^sub>t\<^sub>p = (if w = [] then empty_ctape else
                                        CTape (replicated_clist None) (Some (hd w))
                                        (prepend_list (map Some (tl w)) (replicated_clist None)))"
  by (induction w) auto

definition (in TM) cinitial_config :: "'s list \<Rightarrow> ('q, 's) CTM_config"
  where "cinitial_config w = CTM_config q\<^sub>0 (<w>\<^sub>c\<^sub>t\<^sub>p # empty_ctape \<up> (k - 1))"

lemma length_ctapes_csteps_eq_tc: "length (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w))) =
                                   TM.tape_count M"
proof (induction n)
  case 0
  then show ?case by (simp add: TM.cinitial_config_def)
next
  case (Suc n)
  show ?case apply simp
    apply (subst TM.cstep_def)
    apply auto
     apply (rule Suc)
    unfolding TM.cstep_not_final_def Let_def apply (simp add: Suc)
    by (simp add: TM.next_actions_simps(2))
qed

lemma length_ctapes_cstep [simp]: "TM.tape_count M \<ge> length (ctapes c) \<Longrightarrow>
                                   length (ctapes (TM.cstep M c)) = length (ctapes c)"
  unfolding TM.cstep_def apply auto
  unfolding TM.cstep_not_final_def Let_def apply simp
  unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def by simp

lemma length_ctapes_csteps [simp]: "TM.tape_count M \<ge> length (ctapes c) \<Longrightarrow>
                                    length (ctapes (TM.csteps M n c)) = length (ctapes c)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma length_ctapes_initial_config [simp]: "length (ctapes (TM.cinitial_config M w)) = TM.tape_count M"
  unfolding TM.cinitial_config_def by simp

lemma cinit_conf_state_init_conf: "cstate (TM.cinitial_config M w) = state (TM.initial_config M w)"
  unfolding TM.cinitial_config_def TM.initial_config_def by simp

lemma cinit_conf_heads_init_conf: "cheads (TM.cinitial_config M w) = heads (TM.initial_config M w)"
  unfolding TM.cinitial_config_def TM.initial_config_def TM_abbrevs.cinput_tape_def
    TM_abbrevs.input_tape_def apply auto
  unfolding empty_ctape_def by simp_all

lemma csteps_always_finite_sublist_left: "i < TM.tape_count M \<Longrightarrow>
                                          \<exists>lp. cleft (ctapes (TM.csteps M n (TM.cinitial_config M w)) ! i) =
                                          prepend_list lp (replicated_clist None)"
proof (induction n)
  case 0
  then show ?case apply simp
    unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
     apply (rule exI [where x="[]"])
     apply (simp add: empty_ctape_def)
     apply (metis ctape.sel(1) empty_ctape_def Suc_pred nth_replicate replicate_Suc not_gr_zero replicate_0)
    apply (rule exI [where x="[]"])
    by (simp add: empty_ctape_def nth_Cons')
next
  case (Suc n)
  hence *: "\<exists>lp. cleft (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! i) =
            prepend_list lp (replicated_clist None)" .
  then obtain lp :: "'b option list" where
   lp_def: "cleft (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! i) =
            prepend_list lp (replicated_clist None)" ..
  have [simp]: "[0..<TM.TM.tape_count M] ! i = i" using Suc(2) by simp
  show ?case apply simp
    apply (subst TM.cstep_def)
    apply auto
     apply (rule *)
    unfolding TM.cstep_not_final_def Let_def apply auto
    apply (subst nth_map2)
      apply auto
      apply (simp add: Suc.prems TM.next_actions_simps(2))
     apply (rule Suc(2))
    unfolding TM.next_actions_def TM.ctape_action_def TM.next_writes_def TM.next_moves_def
    apply (subst (1 2) nth_zip)
      apply auto
      apply (rule Suc(2))+
    apply (subst (1 2) nth_map)
     apply auto
     apply (rule Suc(2))
    apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
                  (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i")
      apply auto
      apply (rule exI [where x="tl lp"])
    unfolding TM_abbrevs.left_ctape_shift_left left_ctape_write lp_def
      apply (metis ctl_prepend_list list.sel(2) prepend_list_empty replicated_clist.simps(2))
    apply (rule exI [where x="(TM.TM.next_write M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
                              (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i)#lp"])
    unfolding TM_abbrevs.left_ctape_shift_right apply simp
    unfolding head_ctape_write left_ctape_write apply (simp add: lp_def)
    apply (rule exI [where x=lp])
    unfolding TM_abbrevs.ctape_shift.simps left_ctape_write by (rule lp_def)
qed

lemma cis_final_csteps_stay_eq: "k' \<le> k \<Longrightarrow> TM.cis_final M (TM.csteps M k' (TM.cinitial_config M w)) \<Longrightarrow>
                                 TM.csteps M k (TM.cinitial_config M w) = TM.csteps M k' (TM.cinitial_config M w)"
proof -
  assume a1: "k' \<le> k" and a2: "TM.cis_final M (TM.csteps M k' (TM.cinitial_config M w))"
  have 1: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = (TM.cstep M ^^ (k - k2)) (TM.cinitial_config M w)"
    if "k2 \<le> k - k'" for k2 :: nat using that
  proof (induction k2)
    case 0
    then show ?case by simp
  next
    case (Suc k2)
    have 1: "k2 \<le> k - k'" using Suc(2) by simp
    note 2 = Suc(1) [OF 1]
    have 3: "k - k2 = Suc (k - Suc k2)" using Suc(2) by force
    have 4: "k' \<le> k - Suc k2" using Suc.prems by linarith
    show ?case unfolding 2 3 apply simp
      apply (subst TM.cstep_def)
      apply auto
      using a2 4 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_diff_cancel)
  qed
  show "(TM.cstep M ^^ k) (TM.cinitial_config M w) = (TM.cstep M ^^ k') (TM.cinitial_config M w)"
    using 1 [OF le_refl] a1 by simp
qed

function (domintros) extract_finite_sublist :: "'s option clist \<Rightarrow> 's option list" where
  "t = replicated_clist h \<Longrightarrow> extract_finite_sublist (CCons h t) = []" |
  "t \<noteq> replicated_clist h \<Longrightarrow> extract_finite_sublist (CCons h t) = h#(extract_finite_sublist t)"
     apply auto
  by (metis clist.exhaust)

definition ctape_to_tape :: "'s ctape \<Rightarrow> 's tape" where
  "ctape_to_tape ct \<equiv> Tape (extract_finite_sublist (cleft ct)) (chead ct) (extract_finite_sublist (cright ct))"

lemma extract_finite_sublist_prepend_option:
  "extract_finite_sublist (prepend_list (map Some w) (replicated_clist None)) = map Some w" and
  "extract_finite_sublist_dom (prepend_list (map Some w) (replicated_clist None))"
proof (induction w)
  case Nil
  {
    case 1
    then show ?case apply simp
      by (metis extract_finite_sublist.psimps(1) replicated_clist.code extract_finite_sublist.domintros(1))
  next
    case 2
    then show ?case apply simp
      by (metis extract_finite_sublist.domintros(1) replicated_clist.code)
  }
next
  case (Cons a w)
  {
    case 1
    then show ?case apply simp
      by (metis Cons.IH(1,2) extract_finite_sublist.domintros(2) extract_finite_sublist.psimps(1,2)
          option.distinct(1) prepend_list_empty replicated_clist.code replicated_clist.simps(1))
  next
    case 2
    then show ?case apply simp
      by (metis Cons.IH(2) extract_finite_sublist.domintros(1) extract_finite_sublist.domintros(2))
  }
qed

lemma cotm_steps_congruences:
  shows "cstate (TM.csteps M k (TM.cinitial_config M w)) =
         TM_config.state (TM.steps M k (TM.initial_config M w))" and
        "ctapes (TM.csteps M k (TM.cinitial_config M w)) =
         map (\<lambda>t. CTape (prepend_list (tape.left t) (replicated_clist None)) (tape.head t)
         (prepend_list (tape.right t) (replicated_clist None)))
         (tapes (TM.steps M k (TM.initial_config M w)))"
proof (induction k)
  case 0
  {
    case 1
    then show ?case apply simp
      unfolding TM.cinitial_config_def TM.initial_config_def by simp
  next
    case 2
    then show ?case apply simp
      unfolding TM.initial_config_def TM.cinitial_config_def TM_abbrevs.cinput_tape_def
        TM_abbrevs.input_tape_def apply auto
      unfolding empty_ctape_def by simp_all
  }
next
  case (Suc k)
  {
    case 1
    then show ?case apply simp
      apply (subst TM.cstep_def)
      apply (subst TM.step_def)
      apply (auto simp add: Suc)
      unfolding TM.cstep_not_final_def Let_def apply simp
      unfolding Suc apply simp
      by (metis ctape.sel(2) comp_apply)
  next
    case 2
    have 1: "cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) =
             heads ((TM.step M ^^ k) (TM.initial_config M w))" unfolding Suc(2) by simp
    show ?case apply simp
      apply (subst TM.cstep_def)
      apply (subst TM.step_def)
      apply (auto simp add: Suc)
      unfolding TM.cstep_not_final_def Let_def apply auto
      apply (rule nth_equalityI)
       apply auto
       apply (simp add: TM.next_actions_simps(2) TM.run_tapes_len)
      unfolding TM.ctape_action_def TM.next_actions_def apply auto
      apply (subst nth_map)
       apply auto
      apply (simp_all add: TM.next_writes_simps(2))
        apply (simp_all add: TM.next_moves_simps(2))
       apply (simp add: TM.run_tapes_len)
      apply (subst (1 2 3) nth_zip)
        apply auto
         apply (simp_all add: TM.next_writes_simps(2))
        apply (simp_all add: TM.next_moves_simps(2))
       apply (simp add: TM.run_tapes_len)
      apply (subst (1 2 3) nth_zip)
        apply (simp_all add: TM.next_writes_simps(2))
       apply (simp_all add: TM.next_moves_simps(2))
      unfolding TM_abbrevs.tape_action_def apply simp
      unfolding 1 Suc(1) TM.next_moves_def TM.next_writes_def apply simp
    proof -
      fix i :: nat
      assume a: "i < TM.TM.tape_count M"
      thus "TM_abbrevs.ctape_shift (TM.TM.next_move M (TM_config.state
            ((TM.step M ^^ k) (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (TM_abbrevs.ctape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
            (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)) =
            CTape (prepend_list (tape.left (TM_abbrevs.tape_shift
            (TM.TM.next_move M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
            (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (TM_abbrevs.tape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
            (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)))) (replicated_clist None))
            (tape.head (TM_abbrevs.tape_shift (TM.TM.next_move M (TM_config.state ((TM.step M ^^ k)
            (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (TM_abbrevs.tape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
            (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))))
            (prepend_list (tape.right (TM_abbrevs.tape_shift
            (TM.TM.next_move M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
            (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (TM_abbrevs.tape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
            (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
            (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))))
            (replicated_clist None))"
        apply (cases "TM.TM.next_move M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
                      (heads ((TM.step M ^^ k) (TM.initial_config M w))) i")
          apply auto
      proof (cases "TM_abbrevs.ctape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
                    (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
                    (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)")
        case (CTape l h r)
        then show "TM_abbrevs.ctape_shift Shift_Left (TM_abbrevs.ctape_write
                   (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
                   (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
                   (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)) =
                   CTape (prepend_list (tl (tape.left (tapes ((TM.step M ^^ k)
                   (TM.initial_config M w)) ! i))) (replicated_clist None))
                   (tape.head (TM_abbrevs.tape_shift Shift_Left
                   (TM_abbrevs.tape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
                   (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
                   (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))))
                   (CCons (tape.head (TM_abbrevs.tape_write
                   (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
                   (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
                   (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)))
                   (prepend_list (tape.right (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))
                   (replicated_clist None)))" apply simp
          apply (cases l)
          apply (auto simp add: TM_abbrevs.ctape_shift.simps)
          unfolding TM_abbrevs.ctape_write_def apply auto
          unfolding Suc(2) apply (subst (asm) (1 2) nth_map)
              apply auto
               apply (metis a TM.run_tapes_len)
              apply (metis a TM.run_tapes_len)
             apply (metis clist.inject list.collapse prepend_list_Cons prepend_list_empty replicated_clist.code
              tl_Nil)
            apply (subst (asm) (1 2) nth_map)
              apply auto
              apply (metis a TM.run_tapes_len)
             apply (metis a TM.run_tapes_len)
          unfolding TM_abbrevs.tape_write_def apply auto
           apply (cases "tape.left (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)")
            apply auto
            apply (metis clist.inject replicated_clist.code)
           apply (simp add: TM_abbrevs.tape_shift.simps(2))
          apply (subst nth_map)
           apply auto
          by (metis a TM.run_tapes_len)
      next
        assume a1: "i < TM.TM.tape_count M"
        show "TM_abbrevs.ctape_shift Shift_Right (TM_abbrevs.ctape_write
              (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
              (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
              (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)) =
              CTape (CCons (tape.head (TM_abbrevs.tape_write
              (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
              (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
              (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)))
              (prepend_list (tape.left (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))
              (replicated_clist None))) (tape.head (TM_abbrevs.tape_shift Shift_Right
              (TM_abbrevs.tape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
              (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
              (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))))
              (prepend_list (tl (tape.right (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)))
              (replicated_clist None))" unfolding TM_abbrevs.ctape_write_def
        TM_abbrevs.tape_write_def apply simp
          apply (cases "cright (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)")
          apply (auto simp add: TM_abbrevs.ctape_shift.simps)
          unfolding Suc apply (subst (asm) nth_map)
             apply (simp add: TM.run_tapes_len a1)
            apply (subst nth_map)
             apply auto
            apply (simp add: TM.run_tapes_len a1)
           apply (subst (asm) nth_map)
            apply auto
          apply (simp add: TM.run_tapes_len a1)
           apply (cases "tape.right (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)")
            apply auto
            apply (metis clist.inject replicated_clist.code)
          unfolding TM_abbrevs.tape_shift.simps apply simp
          apply (subst (asm) nth_map)
           apply auto
           apply (simp add: TM.run_tapes_len a1)
          by (smt (verit, ccfv_threshold) clist.inject list.collapse prepend_list_Cons prepend_list_empty
              replicated_clist.code tl_Nil)
      next
        assume a1: "i < TM.TM.tape_count M"
        show "TM_abbrevs.ctape_shift No_Shift (TM_abbrevs.ctape_write
              (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
              (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
              (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)) =
              CTape (prepend_list (tape.left (TM_abbrevs.tape_shift No_Shift
              (TM_abbrevs.tape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
              (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
              (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)))) (replicated_clist None))
              (tape.head (TM_abbrevs.tape_shift No_Shift (TM_abbrevs.tape_write
              (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k) (TM.initial_config M w)))
              (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
              (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))))
              (prepend_list (tape.right (TM_abbrevs.tape_shift No_Shift
              (TM_abbrevs.tape_write (TM.TM.next_write M (TM_config.state ((TM.step M ^^ k)
              (TM.initial_config M w))) (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
              (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i))))
              (replicated_clist None))" unfolding TM_abbrevs.ctape_shift.simps
                TM_abbrevs.tape_shift.simps apply simp
          unfolding TM_abbrevs.ctape_write_def TM_abbrevs.tape_write_def apply auto
          unfolding Suc(2) apply (subst nth_map)
            apply auto
           apply (simp add: TM.run_tapes_len a1)
          apply (subst nth_map)
           apply auto
          by (simp add: TM.run_tapes_len a1)
      qed
    qed
  }
qed

lemma cotm_heads_steps_congruence: "cheads (TM.csteps M k (TM.cinitial_config M w)) =
                                    heads (TM.steps M k (TM.initial_config M w))"
  unfolding cotm_steps_congruences(2) by simp

lemma set_ctape_shift: "set_ctape (TM_abbrevs.ctape_shift shift t) = set_ctape t"
  apply (cases shift)
    apply simp_all
  unfolding TM_abbrevs.ctape_shift.simps apply simp_all
proof (cases t)
  case (CTape l h r)
  show "set_ctape (TM_abbrevs.ctape_shift Shift_Left t) = set_ctape t"
    unfolding CTape apply (cases l)
    apply simp
    unfolding TM_abbrevs.ctape_shift.simps by auto
next
  show "set_ctape (TM_abbrevs.ctape_shift Shift_Right t) = set_ctape t"
  proof (cases t)
    case (CTape l h r)
    show ?thesis unfolding CTape apply (cases r)
      apply simp
      unfolding TM_abbrevs.ctape_shift.simps by auto
  qed
qed

lemma ctapes_subset_symbols: "set w \<subseteq> TM.symbols M \<Longrightarrow>
                              \<Union>(set (map set_ctape (ctapes (TM.csteps M n (TM.cinitial_config M w))))) \<subseteq>
                              TM.symbols M"
proof (induction n)
  case 0
  then show ?case apply auto
    unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
     apply (cases "w = []")
      apply auto
    unfolding empty_ctape_def apply auto
    unfolding set_clist_prepend_list apply auto
    by (metis list.set_sel(2) subset_code(1))
next
  case (Suc n)
  then show ?case apply auto
    apply (subst (asm) TM.cstep_def)
    apply (cases "cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
     apply auto
    unfolding TM.cstep_not_final_def Let_def apply auto
    unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
  proof -
    fix x :: 'a and nw :: "'a option" and ns :: head_move and ct :: "'a ctape"
    assume a1: "\<Union> (set_ctape ` set (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)))) \<subseteq> TM.TM.symbols M" and
           a2: "x \<in> set_ctape (TM.ctape_action (nw, ns) ct)" and
           a3: "((nw, ns), ct) \<in> set (zip (zip (map (TM.TM.next_write M (cstate ((TM.cstep M ^^ n)
                (TM.cinitial_config M w))) (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))))
                [0..<TM.TM.tape_count M]) (map (TM.TM.next_move M (cstate ((TM.cstep M ^^ n)
                (TM.cinitial_config M w))) (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))))
                [0..<TM.TM.tape_count M])) (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w))))"
    have 1: "\<exists>i<TM.tape_count M. TM.TM.next_write M (cstate ((TM.cstep M ^^ n)
             (TM.cinitial_config M w))) (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i = nw"
      using a3 [THEN set_zip_leftD, THEN set_zip_leftD] by auto
    have 2: "\<exists>j<TM.tape_count M. TM.TM.next_move M (cstate ((TM.cstep M ^^ n)
             (TM.cinitial_config M w))) (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) j = ns"
      using a3 [THEN set_zip_leftD, THEN set_zip_rightD] by auto
    have 3: "\<exists>k<TM.tape_count M. ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! k = ct"
      using a3 [THEN set_zip_rightD] by (simp add: in_set_conv_nth)
    obtain i j k :: nat where i_bound: "i < TM.tape_count M" and j_bound: "j < TM.tape_count M" and
      k_bound: "k < TM.tape_count M" and i_index: "TM.TM.next_write M (cstate ((TM.cstep M ^^ n)
             (TM.cinitial_config M w))) (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i = nw" and
      j_index: "TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
                (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) j = ns" and
      k_index: "ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! k = ct" using 1 2 3 by auto
    note a2 [unfolded TM.ctape_action_def, folded i_index j_index k_index, simplified,
        unfolded set_ctape_shift TM_abbrevs.ctape_write_def, simplified]
    thus "x \<in> TM.TM.symbols M" apply auto
        apply (rule a1 [THEN subsetD])
        apply auto
        apply (metis a3 ctape.set_sel(1) k_index option.set_intros set_zip_rightD)
      using TM.next_write_valid [of "cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w))" M
          "cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))" i, OF _ _ _ i_bound]
      unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence
       apply (smt (verit, best) Some_options_iff Suc.prems TM.run_tapes_len TM.set_tape_valid TM_steps_valid_stateI
          in_set_conv_nth length_map nth_map set_tape_in_symbols subsetI)
      apply (rule a1 [THEN subsetD])
      apply auto
      by (metis a3 ctape.set_sel(3) k_index option.set_intros set_zip_rightD)
  qed
qed

lemma set_ctape_eq_set_tape: "i < TM.tape_count M \<Longrightarrow>
       set_ctape (ctapes (TM.csteps M n (TM.cinitial_config M w)) ! i) =
       set_tape (tapes (TM.steps M n (TM.initial_config M w)) ! i)"
  unfolding cotm_steps_congruences(2) apply (subst nth_map)
   apply auto
      apply (simp add: TM.run_tapes_len)
  unfolding set_clist_prepend_list apply auto
     apply (simp_all add: tape.set_sel)
  apply (cases "tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i")
  by simp

lemma csteps_untouched_cells_right:
  assumes "i < TM.tape_count M" and
          "\<not>TM.cis_final M (TM.csteps M (k - 1) (TM.cinitial_config M w))" and
          "j \<ge> k - cell_index M w i k"
        shows "cell_index M w i k \<ge> 0 \<Longrightarrow>
               nth_clist (cright (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i)) j =
               nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) (j + (nat (cell_index M w i k)))" and
              "cell_index M w i k < 0 \<Longrightarrow>
               nth_clist (cright (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i))
               (j + (nat (-cell_index M w i k))) = nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) j"
  using assms
proof (induction k arbitrary: j)
  case 0
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  }
next
  case (Suc k)
  {
    case 1
    have 2: "\<not> TM.cis_final M ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w))" using 1(3)
      unfolding TM.cis_final_def apply (simp add: TM.cstep_def)
      apply (rule ccontr)
      apply simp
      apply (cases k)
       apply auto
      by (simp add: TM.cis_final_def TM.cstep_final)
    note 3 = Suc(1) [OF _ 1(2) 2]
    have 4: "0 \<le> cell_index M w i k + 1 \<Longrightarrow> \<not> 0 \<le> cell_index M w i k \<Longrightarrow> cell_index M w i k = -1"
      by simp
    show ?case using 1 apply simp
      apply (subst TM.cstep_def)
      apply auto
      using 2 unfolding TM.cis_final_def apply simp
      unfolding TM.cstep_not_final_def Let_def apply simp
      unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
      apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
        apply auto
      unfolding TM_abbrevs.right_ctape_shift_left apply simp
        apply (cases j)
         apply auto
         apply (smt (verit, ccfv_threshold) cell_index.simps(2) cell_index_abs_bound cotm_heads_steps_congruence
          cotm_steps_congruences(1))
        apply (subst cell_index.simps(2))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (subst (asm) cell_index.simps(2))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply auto
        apply (smt (verit, best) 2 Suc.IH(1) Suc_nat_eq_nat_zadd1 add_Suc_right cell_index.simps(2)
          cotm_heads_steps_congruence cotm_steps_congruences(1))
      unfolding TM_abbrevs.right_ctape_shift_right apply simp
      unfolding Sucth_clist_from_ctl [symmetric] apply (subst cell_index.simps(3))
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (subst (asm) (1 2) cell_index.simps(3))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (cases "0 \<le> cell_index M w i k")
        apply auto
      using Suc(1) [of "Suc j", OF _ 1(2) 2] apply simp
        apply (metis (no_types, lifting) Suc_nat_eq_nat_zadd1 add.commute add_Suc_right)
       apply (drule 4)
        apply assumption
      using Suc(2) [OF _ 1(2) 2] apply simp
      unfolding TM_abbrevs.ctape_shift.simps apply simp
      apply (subst cell_index.simps(4))
       apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
      apply (subst (asm) (1 2) cell_index.simps(4))
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
      by (simp add: 3)
  next
    case 2
    have 1: "\<not> TM.cis_final M ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w))" using 2(3)
      unfolding TM.cis_final_def apply (simp add: TM.cstep_def)
      apply (rule ccontr)
      apply simp
      apply (cases k)
       apply auto
      by (simp add: TM.cis_final_def TM.cstep_final)
    note 3 = Suc(2) [OF _ 2(2) 1]
    have 4: "0 \<le> cell_index M w i k + 1 \<Longrightarrow> \<not> 0 \<le> cell_index M w i k \<Longrightarrow> cell_index M w i k = -1"
      by simp
    show ?case using 2 apply simp
      apply (subst TM.cstep_def)
      apply auto
      using 1 unfolding TM.cis_final_def apply simp
      unfolding TM.cstep_not_final_def Let_def apply simp
      unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
      apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
        apply auto
      unfolding TM_abbrevs.right_ctape_shift_left apply simp
        apply (cases "j + nat (- cell_index M w i (Suc k))")
         apply auto
        apply (subst (asm) (1 2 3) cell_index.simps(2))
           apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply simp
        apply (cases "cell_index M w i k = 0")
         apply auto
      using 1 Suc.IH(1) apply auto[1]
        apply (subst Suc(2) [of j, symmetric])
            apply auto
      using 1 apply fastforce
        apply (smt (verit, best) Suc_nat_eq_nat_zadd1 add_Suc_right diff_Suc_1')
      unfolding TM_abbrevs.right_ctape_shift_right apply simp
       apply (subst cell_index.simps(3))
        apply auto
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (smt (verit, best) 1 Suc.IH(2) Suc_nat_eq_nat_zadd1 Sucth_clist_from_ctl add_Suc_right
          cell_index.simps(3) cotm_heads_steps_congruence cotm_steps_congruences(1))
      unfolding TM_abbrevs.ctape_shift.simps apply simp
      apply (subst (asm) (1 2) cell_index.simps(4))
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
      apply (subst cell_index.simps(4))
       apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
      using 1 Suc.IH(2) by fastforce
  }
qed

lemma csteps_untouched_cells_head:
  assumes "i < TM.tape_count M" and
          "\<not>TM.cis_final M (TM.csteps M (k - 1) (TM.cinitial_config M w))" and
          "k = cell_index M w i k" and
          "k > 0"
        shows "chead (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i) =
               nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) (k - 1)"
proof -
  note cell_index_eq_steps_all_lower_eq [OF assms(3) [symmetric], of "k - 1"]
  hence 1: "cell_index M w i (k - 1) = int (k - 1)" using assms(4) by simp
  have 2: "\<not> TM.cis_final M ((TM.cstep M ^^ ((k - 1) - 1)) (TM.cinitial_config M w))"
    using assms(2) unfolding TM.cis_final_def apply auto
    apply (cases k)
     apply auto
  proof -
    fix k' :: nat
    show "cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M \<Longrightarrow>
          cstate ((TM.cstep M ^^ (k' - Suc 0)) (TM.cinitial_config M w)) \<in> TM.TM.final_states M \<Longrightarrow>
          k = Suc k' \<Longrightarrow> False" apply (cases k')
       apply auto
      by (simp add: TM.cstep_def)
  qed
  note 3 = csteps_untouched_cells_right(1) [OF assms(1) 2, of 0, simplified, unfolded 1 [simplified], simplified]
  have 4: "k = Suc (k - Suc 0)" using assms(4) by simp
  have 5: "cell_index M w i k = cell_index M w i (k - 1) + 1" using 1 assms(3,4) by simp
  have 6: "TM.TM.next_move M (cstate ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w)))
           (cheads ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w))) i =
           Shift_Right" using 5 apply (subst (asm) 4)
    apply simp
    apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w)))
                  (cheads ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w))) i")
      apply auto
     apply (subst (asm) cell_index.simps(2))
      apply auto
     apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
    apply (subst (asm) cell_index.simps(4))
     apply auto
    by (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
  show "chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i) =
        nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) (k - 1)" apply simp
    apply (subst 3 [symmetric])
    apply (subst 4)
    apply simp
    apply (subst TM.cstep_def)
    apply auto
    using 2 unfolding TM.cis_final_def apply simp
    unfolding TM.cstep_not_final_def Let_def apply auto
    unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
    using assms(1) apply (metis One_nat_def TM.cis_final_def assms(2))
    unfolding 6 TM_abbrevs.head_ctape_shift_right using assms(1) apply simp
    by (simp add: 6 TM_abbrevs.head_ctape_shift_right)
qed

lemma cell_index_eq_cstep_count_always_Shift_Right: "i < TM.tape_count M \<Longrightarrow> cell_index M w i k = k \<Longrightarrow> n < k \<Longrightarrow>
       TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
       (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i = Shift_Right"
  apply (frule cell_index_eq_steps_all_lower_eq [where n=n])
   apply simp
  apply (frule cell_index_eq_steps_all_lower_eq [where n="Suc n"])
   apply simp
  apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
                (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i")
    apply auto
proof -
  assume a1: "i < TM.TM.tape_count M" and a2: "cell_index M w i k = int k" and
         a3: "n < k" and
         a4: "cell_index M w i n = int n" and
         a5: "cell_index M w i (Suc n) = 1 + int n"
  show "TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
        (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i = Shift_Left \<Longrightarrow> False"
    using a4 a5 apply (subst (asm) cell_index.simps(2))
     apply auto
    by (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
  show "TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
        (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i = No_Shift \<Longrightarrow> False"
    using a4 a5 apply (subst (asm) cell_index.simps(4))
     apply auto
    by (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
qed

lemma csteps_untouched_cells_right2:
  assumes "i < TM.tape_count M" and
          "\<not>TM.cis_final M (TM.csteps M (k - 1) (TM.cinitial_config M w))" and
          "j \<ge> max_cell_index M w i k - cell_index M w i k"
        shows "cell_index M w i k \<ge> 0 \<Longrightarrow>
               nth_clist (cright (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i)) j =
               nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) (j + (nat (cell_index M w i k)))" and
              "cell_index M w i k < 0 \<Longrightarrow>
               nth_clist (cright (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i)) j =
               nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) (nat (j + cell_index M w i k))"
  using assms
proof (induction k arbitrary: j)
  case 0
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  }
next
  case (Suc k)
  {
    case 1
    have 2: "\<not> TM.cis_final M ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w))" using 1(3)
      unfolding TM.cis_final_def apply (simp add: TM.cstep_def)
      apply (rule ccontr)
      apply simp
      apply (cases k)
       apply auto
      by (simp add: TM.cis_final_def TM.cstep_final)
    note 3 = Suc(1) [OF _ 1(2) 2]
    have 4: "0 \<le> cell_index M w i k + 1 \<Longrightarrow> \<not> 0 \<le> cell_index M w i k \<Longrightarrow> cell_index M w i k = -1"
      by simp
    have 5: "max_cell_index M w i (Suc k) \<le> cell_index M w i (Suc k) \<Longrightarrow>
             max_cell_index M w i (Suc k) = cell_index M w i (Suc k)"
      using max_cell_index_ge_cell_index verit_la_disequality by blast
    have 6: "max_cell_index M w i (Suc k) \<le> int j \<Longrightarrow> \<not> max_cell_index M w i k + 1 \<le> int j \<Longrightarrow>
             max_cell_index M w i k = j \<and> max_cell_index M w i (Suc k) = max_cell_index M w i k"
      using max_cell_index_mono [of k "Suc k" M w i] by simp
    show ?case using 1 apply simp
      apply (subst TM.cstep_def)
      apply auto
      using 2 unfolding TM.cis_final_def apply simp
      unfolding TM.cstep_not_final_def Let_def apply simp
      unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
      apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
        apply auto
      unfolding TM_abbrevs.right_ctape_shift_left apply simp
        apply (cases j)
         apply auto 
         apply (drule 5)
         apply (subst (asm) (2) cell_index.simps(2))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
      using max_cell_index_max [of k "Suc k" M w i, simplified] apply linarith
        apply (subst cell_index.simps(2))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (subst (asm) cell_index.simps(2))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply auto
        apply (subst 3)
          apply simp
         apply (subst (asm) cell_index.simps(2))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply simp
      using max_cell_index_mono [of k "Suc k" M w i, simplified] apply linarith
        apply (smt (verit, best) 2 Suc.IH(1) Suc_nat_eq_nat_zadd1 add_Suc_right cell_index.simps(2)
          cotm_heads_steps_congruence cotm_steps_congruences(1))
      unfolding TM_abbrevs.right_ctape_shift_right apply simp
      unfolding Sucth_clist_from_ctl [symmetric] apply (subst cell_index.simps(3))
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (subst (asm) (1 2) cell_index.simps(3))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (cases "0 \<le> cell_index M w i k")
        apply auto
      using Suc(1) [of "Suc j", OF _ 1(2) 2] max_cell_index_mono [of k "Suc k" M w i, simplified] apply simp
        apply (metis (no_types, lifting) Suc_nat_eq_nat_zadd1 add.commute add_Suc_right)
       apply (drule 4)
        apply assumption
      using Suc(2) [OF _ 1(2) 2, of "Suc j"] max_cell_index_mono [of k "Suc k" M w i, simplified] apply simp
      unfolding TM_abbrevs.ctape_shift.simps apply simp
      apply (subst cell_index.simps(4))
       apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
      apply (subst (asm) (1 2) cell_index.simps(4))
        apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
      using 3 max_cell_index_mono [of k "Suc k" M w i, simplified] by force
  next
    case 2
    have 1: "\<not> TM.cis_final M ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w))" using 2(3)
      unfolding TM.cis_final_def apply (simp add: TM.cstep_def)
      apply (rule ccontr)
      apply simp
      apply (cases k)
       apply auto
      by (simp add: TM.cis_final_def TM.cstep_final)
    note 3 = Suc(2) [OF _ 2(2) 1]
    have 4: "0 \<le> cell_index M w i k + 1 \<Longrightarrow> \<not> 0 \<le> cell_index M w i k \<Longrightarrow> cell_index M w i k = -1"
      by simp
    show ?case using 2 apply simp
      apply (subst TM.cstep_def)
      apply auto
      using 1 unfolding TM.cis_final_def apply simp
      unfolding TM.cstep_not_final_def Let_def apply simp
      unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
      apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
        apply auto
      unfolding TM_abbrevs.right_ctape_shift_left apply simp
        apply (cases "j + nat (- cell_index M w i (Suc k))")
         apply auto
        apply (subst (asm) (1 2 3) cell_index.simps(2))
           apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply simp
        apply (cases "cell_index M w i k = 0")
         apply auto
         apply (cases j)
          apply auto
          apply (smt (verit) max_cell_index_ge_0)
         apply (subst Suc(1))
            apply auto
           apply (metis 1 One_nat_def)
          apply (meson max_cell_index_mono order_trans suc_is_ge)
         apply (subst cell_index.simps(2))
          apply auto
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (cases j)
         apply auto
         apply (metis "2.prems"(1,4) le_iff_diff_le_0 linorder_not_less max_cell_index_ge_0
          max_cell_index_ge_cell_index of_nat_0 verit_la_disequality)
        apply (subst cell_index.simps(2))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply simp
        apply (subst Suc(2))
            apply auto
      using 1 apply fastforce
      using max_cell_index_mono [of k "Suc k" M w i] apply simp
      unfolding TM_abbrevs.right_ctape_shift_right apply simp
      unfolding Sucth_clist_from_ctl [symmetric] apply (subst (asm) (1 2) cell_index.simps(3))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (subst Suc(2))
           apply auto
         apply (metis 1 One_nat_def)
      using max_cell_index_mono [of k "Suc k" M w i] apply simp
       apply (smt (verit, best) cell_index.simps(3) cotm_heads_steps_congruence cotm_steps_congruences(1))
      unfolding TM_abbrevs.ctape_shift.simps apply simp
      apply (subst Suc(2))
      using max_cell_index_mono [of k "Suc k" M w i] apply auto
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (metis 1 One_nat_def)
       apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
      apply (subst (asm) (1 2) cell_index.simps(4))
      by (simp_all add: cotm_heads_steps_congruence cotm_steps_congruences(1))
  }
qed

lemma csteps_untouched_cells_left2:
  assumes "i < TM.tape_count M" and
          "\<not>TM.cis_final M (TM.csteps M (k - 1) (TM.cinitial_config M w))" and
          "j \<ge> -min_cell_index M w i k + cell_index M w i k"
        shows "cell_index M w i k \<ge> 0 \<Longrightarrow>
               nth_clist (cleft (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i)) j =
               nth_clist (cleft (ctapes (TM.cinitial_config M w) ! i)) (nat (j - cell_index M w i k))" and
              "cell_index M w i k < 0 \<Longrightarrow>
               nth_clist (cleft (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i)) j =
               nth_clist (cleft (ctapes (TM.cinitial_config M w) ! i)) (nat (j - cell_index M w i k))"
  using assms
proof (induction k arbitrary: j)
  case 0
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  }
next
  case (Suc k)
  {
    case 1
    have 2: "\<not> TM.cis_final M ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w))" using 1(3)
      unfolding TM.cis_final_def apply (simp add: TM.cstep_def)
      apply (rule ccontr)
      apply simp
      apply (cases k)
       apply auto
      by (simp add: TM.cis_final_def TM.cstep_final)
    note 3 = Suc(1) [OF _ 1(2) 2]
    have 4: "0 \<le> cell_index M w i k + 1 \<Longrightarrow> \<not> 0 \<le> cell_index M w i k \<Longrightarrow> cell_index M w i k = -1"
      by simp
    have 5: "min_cell_index M w i (Suc k) \<ge> cell_index M w i (Suc k) \<Longrightarrow>
             min_cell_index M w i (Suc k) = cell_index M w i (Suc k)"
      using min_cell_index_le_cell_index verit_la_disequality by blast
    have 6: "min_cell_index M w i (Suc k) \<ge> int j \<Longrightarrow> \<not> min_cell_index M w i k - 1 \<ge> int j \<Longrightarrow>
             min_cell_index M w i k = j \<and> min_cell_index M w i (Suc k) = min_cell_index M w i k"
      using min_cell_index_revmono [of k "Suc k" M w i] by simp
    have 7: "min_cell_index M w i (Suc k) = cell_index M w i k - 1 \<Longrightarrow>
             0 < cell_index M w i k \<Longrightarrow> min_cell_index M w i (Suc k) = 0"
      by (metis verit_la_disequality zle_diff1_eq min_cell_index_le_0)
    have 8: "min_cell_index M w i (Suc k) = cell_index M w i k - 1 \<Longrightarrow>
             0 < cell_index M w i k \<Longrightarrow> min_cell_index M w i k = 0"
      using 7 by (metis "1.prems"(1) min_cell_index_Suc1 min_cell_index_le_0 order_trans)
    show ?case using 1 apply simp
      apply (subst TM.cstep_def)
      apply auto
      using 2 unfolding TM.cis_final_def apply simp
      unfolding TM.cstep_not_final_def Let_def apply simp
      unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
      apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
        apply auto
      unfolding TM_abbrevs.left_ctape_shift_left apply simp
        apply (cases j)
         apply auto 
         apply (drule 5)
         apply (subst (asm) (2) cell_index.simps(2))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (subst (asm)  cell_index.simps(2))
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply auto
         apply (frule 7)
          apply assumption
         apply (frule 8)
          apply assumption
         apply simp
      using Suc(1) [of 1, OF _ _ 2] apply simp
         apply (simp add: Sucth_clist_from_ctl)
        apply (subst cell_index.simps(2))
         apply auto
         apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
      unfolding Sucth_clist_from_ctl [symmetric] apply (subst (asm) (1 2) cell_index.simps(2))
          apply auto
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (subst (asm) min_cell_index_Suc1)
      using "1.prems"(1) min_cell_index_le_0 order_trans apply blast
      using Suc(1) [of "Suc j", OF _ _ 2] apply simp
        apply (simp add: add_diff_eq)
      unfolding TM_abbrevs.left_ctape_shift_right apply simp
       apply (cases j)
        apply auto
        apply (smt (verit) cell_index.simps(3) cotm_heads_steps_congruence cotm_steps_congruences(1)
          min_cell_index_Suc1 min_cell_index_le_cell_index)
       apply (subst (asm) (1 2) cell_index.simps(3))
         apply auto
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (subst cell_index.simps(3))
        apply auto
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (smt (verit, best) "1.prems"(1) 2 3 Suc.IH(2) min_cell_index_Suc1 min_cell_index_le_0)
      unfolding TM_abbrevs.ctape_shift.simps apply simp
      apply (subst (asm) (1 2) cell_index.simps(4))
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
      apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
      apply (subst cell_index.simps(4))
       apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
      by (smt (verit, ccfv_SIG) "1.prems"(1) 3 min_cell_index_Suc1 min_cell_index_le_0)
  next
    case 2
    have 1: "\<not> TM.cis_final M ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w))" using 2(3)
      unfolding TM.cis_final_def apply (simp add: TM.cstep_def)
      apply (rule ccontr)
      apply simp
      apply (cases k)
       apply auto
      by (simp add: TM.cis_final_def TM.cstep_final)
    note 3 = Suc(2) [OF _ 2(2) 1]
    have 4: "0 \<le> cell_index M w i k + 1 \<Longrightarrow> \<not> 0 \<le> cell_index M w i k \<Longrightarrow> cell_index M w i k = -1"
      by simp
    show ?case using 2 apply simp
      apply (subst TM.cstep_def)
      apply auto
      using 1 unfolding TM.cis_final_def apply simp
      unfolding TM.cstep_not_final_def Let_def apply simp
      unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
      apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
        apply auto
      unfolding TM_abbrevs.left_ctape_shift_left apply simp
      unfolding Sucth_clist_from_ctl [symmetric] apply (subst (asm) (1 2) cell_index.simps(2))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (subst cell_index.simps(2))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (cases "cell_index M w i (Suc k) \<ge> min_cell_index M w i k")
      unfolding min_cell_index_Suc1 apply auto
         apply (cases "cell_index M w i k = 0")
          apply auto
          apply (smt (verit, ccfv_SIG) 1 Suc.IH(1) of_nat_Suc)
         apply (smt (verit) 1 Suc.IH(2) of_nat_Suc)
        apply (cases "cell_index M w i k = 0")
         apply auto
         apply (smt (verit, ccfv_threshold) 1 Suc.IH(1) min_cell_index_le_cell_index of_nat_Suc)
        apply (smt (verit, best) 1 Suc.IH(2) min_cell_index_le_cell_index of_nat_Suc)
      unfolding TM_abbrevs.left_ctape_shift_right apply simp
       apply (cases j)
        apply auto
        apply (subst (asm) (1 2) cell_index.simps(3))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (subst cell_index.simps(3))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (smt (verit, best) min_cell_index_Suc1 min_cell_index_le_cell_index)
       apply (subst (asm) (1 2) cell_index.simps(3))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (subst cell_index.simps(3))
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (smt (verit, best) 1 Suc.IH(2) min_cell_index_Suc1 min_cell_index_le_cell_index)
      unfolding TM_abbrevs.ctape_shift.simps apply simp
      apply (subst (asm) (1 2) cell_index.simps(4))
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
       apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
      apply (subst cell_index.simps(4))
       apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
      by (smt (verit, del_insts) 1 Suc.IH(2) min_cell_index_Suc1 min_cell_index_le_cell_index)
  }
qed

lemma csteps_untouched_cells_head2_right:
  assumes "i < TM.tape_count M" and
          "\<not>TM.cis_final M (TM.csteps M (k - 1) (TM.cinitial_config M w))" and
          "max_cell_index M w i (k - 1) < cell_index M w i k" and
          "k > 0"
        shows "chead (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i) =
               nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) (nat (cell_index M w i k) - 1)"
proof -
  have 1: "max_cell_index M w i k = max_cell_index M w i (k - 1) + 1"
    by (smt (verit, best) Suc_diff_1 assms(3,4) max_cell_index_Suc2)
  have 2: "cell_index M w i k = max_cell_index M w i k" using 1
    by (smt (verit, ccfv_SIG) assms(3) max_cell_index_ge_cell_index)
  have 3: "cell_index M w i (k - 1) = max_cell_index M w i (k - 1)" using 1
    by (smt (verit, best) Suc_diff_1 assms(4) max_cell_index_Suc_gt_impl_eq_cell_index)
  have 4: "k = Suc (k - 1)" using assms(4) by simp
  have 5: "cell_index M w i k = cell_index M w i (k - 1) + 1" using 1 2 3 by argo
  show "chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i) =
        nth_clist (cright (ctapes (TM.cinitial_config M w) ! i)) (nat (cell_index M w i k) - 1)"
    apply (subst 4)
    apply simp
    apply (subst TM.cstep_def)
    apply auto
     apply (metis One_nat_def assms(2) TM.cis_final_def)
    unfolding TM.cstep_not_final_def Let_def apply simp
    unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
    using assms(1) apply simp
    apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w)))
                  (cheads ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w))) i")
      apply auto
    unfolding TM_abbrevs.head_ctape_shift_left apply simp
      apply (insert 5)
      apply (subst (asm) (4) 4)
      apply simp
      apply (subst (asm) cell_index.simps(2))
       apply auto
      apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
    unfolding TM_abbrevs.head_ctape_shift_right apply simp
     apply (subst csteps_untouched_cells_right2(1) [OF assms(1), of "k - 1" w 0, simplified])
    unfolding TM.cis_final_def apply (cases "k - Suc 0")
         apply auto
        apply (metis 4 TM.cstep_def diff_Suc_1' diff_Suc_Suc)
       apply (metis 3 One_nat_def max_cell_index_ge_cell_index)
      apply (metis 3 One_nat_def max_cell_index_ge_0)
     apply (smt (verit, best) 3 One_nat_def max_cell_index_ge_0 nat_1 nat_diff_distrib')
    apply (subst (asm) (4) 4)
    apply simp
    apply (subst (asm) cell_index.simps(4))
     apply auto
    by (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
qed

lemma csteps_untouched_cells_head2_left:
  assumes "i < TM.tape_count M" and
          "\<not>TM.cis_final M (TM.csteps M (k - 1) (TM.cinitial_config M w))" and
          "min_cell_index M w i (k - 1) > cell_index M w i k" and
          "k > 0"
        shows "chead (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i) =
               nth_clist (cleft (ctapes (TM.cinitial_config M w) ! i)) (nat (-cell_index M w i k) - 1)"
proof -
  have 1: "min_cell_index M w i k = min_cell_index M w i (k - 1) - 1"
    by (smt (verit, best) Suc_diff_1 assms(3,4) min_cell_index_Suc2)
  have 2: "cell_index M w i k = min_cell_index M w i k" using 1
    by (smt (verit, ccfv_SIG) assms(3) min_cell_index_le_cell_index)
  have 3: "cell_index M w i (k - 1) = min_cell_index M w i (k - 1)" using 1
    by (smt (verit, best) Suc_diff_1 assms(4) min_cell_index_Suc_lt_impl_eq_cell_index)
  have 4: "k = Suc (k - 1)" using assms(4) by simp
  have 5: "cell_index M w i k = cell_index M w i (k - 1) - 1" using 1 2 3 by argo
  show "chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i) =
        nth_clist (cleft (ctapes (TM.cinitial_config M w) ! i)) (nat (-cell_index M w i k) - 1)"
    apply (subst 4)
    apply simp
    apply (subst TM.cstep_def)
    apply auto
     apply (metis One_nat_def assms(2) TM.cis_final_def)
    unfolding TM.cstep_not_final_def Let_def apply simp
    unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
    using assms(1) apply simp
    apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w)))
                  (cheads ((TM.cstep M ^^ (k - Suc 0)) (TM.cinitial_config M w))) i")
      apply auto
    unfolding TM_abbrevs.head_ctape_shift_left apply simp
      apply (cases "cell_index M w i (k - Suc 0) < 0")
      apply (subst csteps_untouched_cells_left2(2) [OF assms(1), of "k - 1" w 0, simplified])
    unfolding TM.cis_final_def apply (cases "k - Suc 0")
         apply auto
        apply (metis 4 TM.cstep_def diff_Suc_1' diff_Suc_Suc)
        apply (metis 3 One_nat_def min_cell_index_le_cell_index)
       apply (subst 5)
       apply simp
       apply (smt (verit, best) Suc_nat_eq_nat_zadd1 diff_Suc_1')
      apply (subst csteps_untouched_cells_left2(1) [OF assms(1), of "k - 1" w 0, simplified])
         apply auto
    unfolding TM.cis_final_def apply (cases "k - Suc 0")
         apply auto
        apply (metis diff_Suc_1' TM.cstep_def diff_Suc_Suc 4)
       apply (metis One_nat_def 3 min_cell_index_le_cell_index)
      apply (simp add: 5)
     apply (insert 5)
     apply (subst (asm) (4) 4)
     apply simp
     apply (subst (asm) cell_index.simps(3))
      apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
     apply simp
    apply (insert 5)
    apply (subst (asm) (4) 4)
    apply simp
    apply (subst (asm) cell_index.simps(4))
     apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
    by simp
qed

definition nth_ctape :: "'s ctape \<Rightarrow> int \<Rightarrow> 's option" where
  "nth_ctape ct i \<equiv> (if i = 0 then chead ct else if i > 0 then nth_clist (cright ct) (nat (i - 1)) else
                      nth_clist (cleft ct) (nat (-i - 1)))"

lemma nth_ctape_0: "nth_ctape ct 0 = chead ct"
  unfolding nth_ctape_def by simp

lemma nth_ctape_pos: "i > 0 \<Longrightarrow> nth_ctape ct i = nth_clist (cright ct) (nat (i - 1))"
  unfolding nth_ctape_def by simp

lemma nth_ctape_neg: "i < 0 \<Longrightarrow> nth_ctape ct i = nth_clist (cleft ct) (nat (-i - 1))"
  unfolding nth_ctape_def by simp

lemma nth_ctape_inject: "(\<And>i::int. nth_ctape ct1 i = nth_ctape ct2 i) \<Longrightarrow> ct1 = ct2"
proof -
  assume a1: "\<And>i::int. nth_ctape ct1 i = nth_ctape ct2 i"
  have 1: "(\<And>n. nth_clist (cleft ct1) n = nth_clist (cleft ct2) n) \<Longrightarrow> cleft ct1 = cleft ct2"
    by (rule nth_clist_unique_spec)
  have 2: "(\<And>n. nth_clist (cright ct1) n = nth_clist (cright ct2) n) \<Longrightarrow> cright ct1 = cright ct2"
    by (rule nth_clist_unique_spec)
  show "ct1 = ct2" apply (rule ctape.expand)
    apply auto
  proof (rule 1)
    fix n :: nat
    have 3: "n = (nat (-(-(int n) - 1) - 1))" by simp
    show "nth_clist (cleft ct1) n = nth_clist (cleft ct2) n"
      apply (subst (1 2) 3)
      apply (subst (1 2) nth_ctape_neg [symmetric])
       apply simp
      by (rule a1)
  next
    show "chead ct1 = chead ct2"
      using a1 [of 0, unfolded nth_ctape_0] .
  next
    show "cright ct1 = cright ct2"
    proof (rule 2)
      fix n :: nat
      have 3: "n = (nat ((int n + 1) - 1))" by linarith
      show "nth_clist (cright ct1) n = nth_clist (cright ct2) n"
        apply (subst (1 2) 3)
        apply (subst (1 2) nth_ctape_pos [symmetric])
         apply simp
        by (rule a1)
    qed
  qed
qed

lemma map_ctape_nth [simp]: "nth_ctape (map_ctape f ct) i = map_option f (nth_ctape ct i)"
  unfolding nth_ctape_def by (simp add: ctape.map_sel)

lemma map_ctape_nth_None: "nth_ctape ct i = None \<Longrightarrow> nth_ctape (map_ctape f ct) i = None"
  by simp

lemma map_ctape_nth_Some: "nth_ctape ct i = Some x \<Longrightarrow>
                           nth_ctape (map_ctape f ct) i = Some (f x)"
  by simp

lemma nth_ctape_shift_left [simp]: "nth_ctape (TM_abbrevs.ctape_shift Shift_Left ct) i =
                                    nth_ctape ct (i - 1)"
  apply (cases "i = 0")
   apply (simp add: nth_ctape_0)
   apply (cases ct)
   apply simp
   apply (smt (verit, best) TM_abbrevs.head_ctape_shift_left nat_zero_as_int nth_ctape_def
      zeroth_clist_is_chd)
  apply (cases ct)
  apply simp
  apply (cases "i > 0")
   apply (simp add: nth_ctape_pos)
   apply (cases "i - 1 = 0")
    apply auto
    apply (simp add: TM_abbrevs.right_ctape_shift_left nth_ctape_def)
   apply (subst nth_ctape_pos)
    apply auto
proof -
  fix x1 x3 :: "'a option clist" and x2 :: "'a option"
  assume a1: "ct = CTape x1 x2 x3" and a2: "0 < i" and a3: "i \<noteq> 1"
  show "nth_clist (cright (TM_abbrevs.ctape_shift Shift_Left (CTape x1 x2 x3)))
        (nat (i - 1)) = nth_clist x3 (nat (i - 2))"
    apply (cases x1)
    apply simp
    unfolding TM_abbrevs.ctape_shift.simps(1) apply simp
    apply (cases "nat (i - 1)")
    apply auto
    using a2 a3 apply linarith
    by (metis Suc_eq_plus1 add_less_same_cancel2 diff_Suc_1 diff_diff_eq linorder_not_le
        nat_diff_distrib nat_one_as_int not_less_zero one_add_one zero_le_one zero_less_one
        zless_nat_conj)
next
  fix x1 x3 :: "'a option clist" and x2 :: "'a option"
  assume a1: "i \<noteq> 0" and a2: "ct = CTape x1 x2 x3" and a3: "\<not> 0 < i"
  have 1: "i < 0" using a1 a3 by auto
  show "nth_ctape (TM_abbrevs.ctape_shift Shift_Left (CTape x1 x2 x3)) i =
        nth_ctape (CTape x1 x2 x3) (i - 1)"
    apply (cases x1)
    apply simp
    unfolding TM_abbrevs.ctape_shift.simps(1) apply (subst nth_ctape_neg)
     apply (rule 1)
    apply simp
    apply (subst nth_ctape_neg)
    using 1 apply simp
    apply simp
    by (smt (verit, best) One_nat_def Suc_pred a1 a3 nat_diff_distrib' nat_one_as_int
        nat_zero_as_int nth_clist.simps(2) zless_nat_conj)
qed

lemma nth_ctape_no_shift [simp]: "nth_ctape (TM_abbrevs.ctape_shift No_Shift ct) i =
                                  nth_ctape ct i"
  unfolding TM_abbrevs.ctape_shift.simps ..

lemma nth_ctape_shift_right [simp]: "nth_ctape (TM_abbrevs.ctape_shift Shift_Right ct) i =
                                     nth_ctape ct (i + 1)"
  apply (cases "i = 0")
   apply (simp add: nth_ctape_0)
   apply (cases ct)
   apply simp
   apply (smt (verit, best) TM_abbrevs.head_ctape_shift_right nat_zero_as_int nth_ctape_def
      zeroth_clist_is_chd)
  apply (cases ct)
  apply simp
  apply (cases "i > 0")
   apply (simp add: nth_ctape_pos)
   apply (cases "i - 1 = 0")
    apply auto
    apply (simp_all add: Sucth_clist_from_ctl TM_abbrevs.right_ctape_shift_right)
   apply (metis Suc_diff_1 Sucth_clist_from_ctl linorder_not_le nat_0_iff nat_eq_iff2
      nat_minus_as_int of_nat_1 pos_int_cases)
  by (smt (verit, best) TM_abbrevs.ctape_shift.elims TM_abbrevs.ctape_shift.simps(1)
      head_move.simps(2,6) nth_ctape_shift_left)

lemma nth_ctape_tape_write_0 [simp]: "nth_ctape (TM_abbrevs.ctape_write s ct) 0 = s"
  unfolding TM_abbrevs.ctape_write_def nth_ctape_0 by simp

lemma nth_ctape_tape_write_non0 [simp]: "i \<noteq> 0 \<Longrightarrow>
                                         nth_ctape (TM_abbrevs.ctape_write s ct) i =
                                         nth_ctape ct i"
  unfolding TM_abbrevs.ctape_write_def nth_ctape_def by simp

lemma nth_ctape_empty_ctape [simp]: "nth_ctape empty_ctape i = None"
  unfolding empty_ctape_def nth_ctape_def by simp

lemma nth_ctape_cstep_Shift_Left1: "TM.next_move M (cstate c) (cheads c) i = Shift_Left \<Longrightarrow>
                                    cstate c \<notin> TM.final_states M \<Longrightarrow> i < length (ctapes c) \<Longrightarrow>
                                    i < TM.tape_count M \<Longrightarrow> j \<noteq> 1 \<Longrightarrow>
                                    nth_ctape (ctapes (TM.cstep M c) ! i) j = nth_ctape (ctapes c ! i) (j - 1)"
  unfolding TM.cstep_def TM.cstep_not_final_def Let_def apply simp
  apply (subst nth_map2)
    apply auto
  unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def TM.ctape_action_def by simp_all

lemma nth_ctape_cstep_Shift_Left2: "TM.next_move M (cstate c) (cheads c) i = Shift_Left \<Longrightarrow>
                                    cstate c \<notin> TM.final_states M \<Longrightarrow> i < length (ctapes c) \<Longrightarrow>
                                    i < TM.tape_count M \<Longrightarrow>
                                    nth_ctape (ctapes (TM.cstep M c) ! i) 1 =
                                    TM.next_write M (cstate c) (cheads c) i"
  unfolding TM.cstep_def TM.cstep_not_final_def Let_def apply simp
  apply (subst nth_map2)
    apply auto
  unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def TM.ctape_action_def by simp_all

lemma nth_ctape_cstep_Shift_Right1: "TM.next_move M (cstate c) (cheads c) i = Shift_Right \<Longrightarrow>
                                     cstate c \<notin> TM.final_states M \<Longrightarrow> i < length (ctapes c) \<Longrightarrow>
                                     i < TM.tape_count M \<Longrightarrow> j \<noteq> -1 \<Longrightarrow>
                                     nth_ctape (ctapes (TM.cstep M c) ! i) j = nth_ctape (ctapes c ! i) (j + 1)"
  unfolding TM.cstep_def TM.cstep_not_final_def Let_def apply simp
  apply (subst nth_map2)
    apply auto
  unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def TM.ctape_action_def by simp_all

lemma nth_ctape_cstep_Shift_Right2: "TM.next_move M (cstate c) (cheads c) i = Shift_Right \<Longrightarrow>
                                     cstate c \<notin> TM.final_states M \<Longrightarrow> i < length (ctapes c) \<Longrightarrow>
                                     i < TM.tape_count M \<Longrightarrow>
                                     nth_ctape (ctapes (TM.cstep M c) ! i) (-1) =
                                     TM.next_write M (cstate c) (cheads c) i"
  unfolding TM.cstep_def TM.cstep_not_final_def Let_def apply simp
  apply (subst nth_map2)
    apply auto
  unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def TM.ctape_action_def by simp_all

lemma nth_ctape_cstep_No_Shift1: "TM.next_move M (cstate c) (cheads c) i = No_Shift \<Longrightarrow>
                                  cstate c \<notin> TM.final_states M \<Longrightarrow> i < length (ctapes c) \<Longrightarrow>
                                  i < TM.tape_count M \<Longrightarrow> j \<noteq> 0 \<Longrightarrow>
                                  nth_ctape (ctapes (TM.cstep M c) ! i) j = nth_ctape (ctapes c ! i) j"
  unfolding TM.cstep_def TM.cstep_not_final_def Let_def apply simp
  apply (subst nth_map2)
    apply auto
  unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def TM.ctape_action_def by simp_all

lemma nth_ctape_cstep_No_Shift2: "TM.next_move M (cstate c) (cheads c) i = No_Shift \<Longrightarrow>
                                  cstate c \<notin> TM.final_states M \<Longrightarrow> i < length (ctapes c) \<Longrightarrow>
                                  i < TM.tape_count M \<Longrightarrow>
                                  nth_ctape (ctapes (TM.cstep M c) ! i) 0 =
                                  TM.next_write M (cstate c) (cheads c) i"
  unfolding TM.cstep_def TM.cstep_not_final_def Let_def apply simp
  apply (subst nth_map2)
    apply auto
  unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def TM.ctape_action_def by simp_all

lemma nth_ctape_cinit_conf_neg: "i < 0 \<Longrightarrow> nth_ctape (ctapes (TM.cinitial_config M w) ! 0) i = None"
  unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
  unfolding nth_ctape_neg by simp

lemma nth_ctape_cinit_conf_w: "(i::int) \<ge> 0 \<Longrightarrow> i < length w \<Longrightarrow>
                               nth_ctape (ctapes (TM.cinitial_config M w) ! 0) i = Some (w ! (nat i))"
  unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
  apply (cases "i = 0")
   apply auto
  unfolding nth_ctape_0 apply simp
  using hd_conv_nth apply blast
  apply (subst nth_ctape_pos)
   apply simp_all
  apply (subst prepend_list_nth_less)
   apply simp_all
  by (simp add: Suc_nat_eq_nat_zadd1 nth_tl)

lemma nth_ctape_cinit_conf_ge: "(i::int) \<ge> length w \<Longrightarrow>
                                nth_ctape (ctapes (TM.cinitial_config M w) ! 0) i = None"
  unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
  apply (subst nth_ctape_pos)
   apply simp_all
  using nless_le apply fastforce
  apply (subst prepend_list_nth_ge)
  by simp_all

lemma nth_ctape_cinit_non_input: "j < TM.tape_count M \<Longrightarrow> j > 0 \<Longrightarrow>
                                  nth_ctape (ctapes (TM.cinitial_config M w) ! j) i = None"
  unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def by simp

lemma chead_is_last_next_write: "k1 < k2 \<Longrightarrow> cell_index M w i k1 = cell_index M w i k2 \<Longrightarrow>
                                 i < TM.tape_count M \<Longrightarrow>
                                 \<not>TM.cis_final M (TM.csteps M k2 (TM.cinitial_config M w)) \<Longrightarrow>
                                 \<exists>!k. k < k2 \<and> (\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 \<longrightarrow> k' \<le> k) \<and>
                                 cell_index M w i k = cell_index M w i k2 \<and>
                                 cheads (TM.csteps M k2 (TM.cinitial_config M w)) ! i =
                                 TM.next_write M (cstate (TM.csteps M k (TM.cinitial_config M w)))
                                 (cheads (TM.csteps M k (TM.cinitial_config M w))) i"
proof (rule ex1I')
  assume a1: "k1 < k2" and a2: "cell_index M w i k1 = cell_index M w i k2" and
         a3: "i < TM.TM.tape_count M"
  show "\<exists>\<^sub>\<le>\<^sub>1 k. k < k2 \<and> (\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 \<longrightarrow> k' \<le> k) \<and>
        cell_index M w i k = cell_index M w i k2 \<and>
        cheads ((TM.cstep M ^^ k2) (TM.cinitial_config M w)) ! i =
        TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
  proof (rule Uniq_I, auto)
    fix k0 k0' :: nat
    assume a4: "k0 < k2" and a5: "k0' < k2" and
           a6: "\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 \<longrightarrow> k' \<le> k0" and
           a7: "\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 \<longrightarrow> k' \<le> k0'" and
           a8: "cell_index M w i k0 = cell_index M w i k2" and
           a9: "cell_index M w i k0' = cell_index M w i k2"
    show "k0 = k0'"
    proof (rule ccontr, cases "k0 < k0'")
      case True
      show False using a6 [THEN spec, THEN mp, THEN mp, OF a5 a9] True by simp
    next
      case False
      assume a10: "k0 \<noteq> k0'"
      have *: "k0' < k0" using False a10 by simp
      show False using a7 [THEN spec, THEN mp, THEN mp, OF a4 a8] * by simp
    qed
  qed
  assume a4: "\<not> TM.cis_final M ((TM.cstep M ^^ k2) (TM.cinitial_config M w))"
  define k :: nat where "k \<equiv> (GREATEST k. k < k2 \<and> cell_index M w i k = cell_index M w i k2)"
  show "\<exists>k<k2. (\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 \<longrightarrow> k' \<le> k) \<and>
        cell_index M w i k = cell_index M w i k2 \<and>
        cheads ((TM.cstep M ^^ k2) (TM.cinitial_config M w)) ! i =
        TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
  proof (rule exI, safe)
    have *: "{k. k < k2 \<and> cell_index M w i k = cell_index M w i k2} \<noteq> {}"
      using a1 a2 by auto
    have **: "\<And>n. n \<in> {k. k < k2 \<and> cell_index M w i k = cell_index M w i k2} \<Longrightarrow> n \<le> k2"
      by simp
    note *** = natset_bounded_Max_bounded [of "{k. k < k2 \<and> cell_index M w i k = cell_index M w i k2}" k2,
        OF * **, simplified]
    have ****: "Max {k. k < k2 \<and> cell_index M w i k = cell_index M w i k2} \<noteq> k2"
      apply auto
      using * ** by (metis (no_types, lifting) Max_in finite_nat_set_iff_bounded_le less_not_refl
          mem_Collect_eq)
    have 0: "k = Max {k. k < k2 \<and> cell_index M w i k = cell_index M w i k2}"
      unfolding k_def apply (rule Greatest_equality)
       apply auto
      using *** **** apply (rule le_neq_implies_less)
      using * by (metis (mono_tags, lifting) ** Max_in finite_nat_set_iff_bounded_le mem_Collect_eq)
    show 1: "k < k2"
      unfolding 0 using *** **** by simp
    show 2: "cell_index M w i k = cell_index M w i k2"
      unfolding 0 using * by (metis (mono_tags, lifting) ** Max_in finite_nat_set_iff_bounded_le
          mem_Collect_eq)
    show 3: "\<And>k'. k' < k2 \<Longrightarrow> cell_index M w i k' = cell_index M w i k2 \<Longrightarrow> k' \<le> k"
      unfolding 0 using * ** by simp
    have 4: "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
      using a4 1 unfolding TM.cis_final_def [symmetric] apply auto
      by (metis (no_types, lifting) *** 0 cis_final_sub_imp diff_diff_cancel)
    have 5: "nth_ctape (ctapes ((TM.cstep M ^^ k') (TM.cinitial_config M w)) ! i)
             ((cell_index M w i k) - (cell_index M w i k')) =
             TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
             (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
      if "k' \<ge> Suc k" and "k' < k2" for k' :: nat using that
    proof (induction k' rule: nat_induct_at_least)
      case base
      show ?case apply simp
        apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                      (heads ((TM.step M ^^ k) (TM.initial_config M w))) i")
          apply simp_all
        unfolding cotm_steps_congruences [symmetric] cotm_heads_steps_congruence [symmetric]
          apply (subst nth_ctape_cstep_Shift_Left2)
              apply simp_all
            apply (rule 4)
           apply (rule a3)+
         apply (subst nth_ctape_cstep_Shift_Right2)
        apply simp_all
           apply (rule 4)
          apply (rule a3)+
        apply (subst nth_ctape_cstep_No_Shift2)
            apply simp_all
          apply (rule 4)
        by (rule a3)+
    next
      case (Suc n)
      have 5: "n < k2" using Suc(3) by simp
      note 6 = Suc(2) [OF 5]
      have 7: "cell_index M w i k \<noteq> cell_index M w i n"
        apply standard
        using 3 [OF 5] 2 Suc(1) by simp
      show ?case apply (simp add: 6 [symmetric])
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i")
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply simp_all
        using a4 5 unfolding TM.cis_final_def [symmetric] apply auto[1]
              apply (metis cis_final_sub_imp diff_diff_cancel nat_less_le)
             apply (rule a3)+
           apply (subst cell_index.simps(2))
            apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        using 7 apply simp
          apply (subst cell_index.simps(2))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply simp
         apply (subst nth_ctape_cstep_Shift_Right1)
              apply simp_all
        using a4 5 unfolding TM.cis_final_def [symmetric] apply auto[1]
             apply (metis cis_final_sub_imp diff_diff_cancel nat_less_le)
            apply (rule a3)+
          apply (subst cell_index.simps(3))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        using 7 apply simp
        apply (subst cell_index.simps(3))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply simp
        apply (subst nth_ctape_cstep_No_Shift1)
             apply simp_all
        using a4 5 unfolding TM.cis_final_def [symmetric] apply auto[1]
            apply (metis cis_final_sub_imp diff_diff_cancel nat_less_le)
           apply (rule a3)+
         apply (subst cell_index.simps(4))
        apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        using 7 apply simp
        apply (subst cell_index.simps(4))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        by simp
    qed
    show "cheads ((TM.cstep M ^^ k2) (TM.cinitial_config M w)) ! i =
          TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
          (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
    proof (cases "Suc k = k2")
      case True
      show ?thesis using 2 apply (simp add: True [symmetric])
        apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                      (heads ((TM.step M ^^ k) (TM.initial_config M w))) i")
          apply simp_all
        apply (subst nth_map)
        using a3 apply simp
        apply (subst nth_ctape_0 [symmetric])
        apply (subst nth_ctape_cstep_No_Shift2)
            apply simp_all
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply (rule 4)
        by (rule a3)+
    next
      case False
      hence 6: "Suc k \<le> k2 - 1" using 1 by simp
      have 7: "k2 - 1 < k2" using 6 by simp
      have 8: "k2 = Suc (k2 - 1)" using 7 by simp
      note 9 = 5 [OF 6 7, simplified]
      show ?thesis apply (subst 8)
        apply simp
        unfolding 9 [symmetric] 2 apply (subst nth_map)
        using a3 apply simp
        apply (subst nth_ctape_0 [symmetric])
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ (k2 - Suc 0)) (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ (k2 - Suc 0)) (TM.cinitial_config M w))) i")
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply simp_all
        using a4 TM.cis_final_def cis_final_sub_imp apply blast
            apply (rule a3)+
          apply (subst (3) 8)
          apply (subst cell_index.simps(2))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply simp
         apply (subst nth_ctape_cstep_Shift_Right1)
              apply simp_all
        using a4 TM.cis_final_def cis_final_sub_imp apply blast
           apply (rule a3)+
         apply (subst (3) 8)
         apply (subst cell_index.simps(3))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply simp
        apply (subst nth_ctape_cstep_No_Shift2)
            apply simp_all
        using a4 TM.cis_final_def cis_final_sub_imp apply blast
          apply (rule a3)+
        using 3 [OF 7] 6 by (metis 1 8 One_nat_def cell_index.simps(4) cotm_heads_steps_congruence
            cotm_steps_congruences(1) le_less_Suc_eq less_eq_Suc_le less_not_refl)
    qed
  qed
qed

lemma nth_ctape_is_last_next_write: "k1 < k2 \<Longrightarrow> cell_index M w i k1 = cell_index M w i k2 + j \<Longrightarrow>
                                     i < TM.tape_count M \<Longrightarrow>
                                     \<not>TM.cis_final M (TM.csteps M k2 (TM.cinitial_config M w)) \<Longrightarrow>
                                     \<exists>!k. k < k2 \<and> (\<forall>k'<k2. cell_index M w i k' =
                                     cell_index M w i k2 + j \<longrightarrow> k' \<le> k) \<and>
                                     cell_index M w i k = cell_index M w i k2 + j \<and>
                                     nth_ctape (ctapes (TM.csteps M k2 (TM.cinitial_config M w)) ! i) j =
                                     TM.next_write M (cstate (TM.csteps M k (TM.cinitial_config M w)))
                                     (cheads (TM.csteps M k (TM.cinitial_config M w))) i"
proof (rule ex1I')
  assume a1: "k1 < k2" and a2: "cell_index M w i k1 = cell_index M w i k2 + j" and
         a3: "i < TM.TM.tape_count M" and a4: "\<not> TM.cis_final M ((TM.cstep M ^^ k2) (TM.cinitial_config M w))"
  show "\<exists>\<^sub>\<le>\<^sub>1 k. k < k2 \<and> (\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 + j \<longrightarrow> k' \<le> k) \<and>
        cell_index M w i k = cell_index M w i k2 + j \<and>
        nth_ctape (ctapes ((TM.cstep M ^^ k2) (TM.cinitial_config M w)) ! i) j =
        TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
  proof (rule Uniq_I, auto)
    fix k0 k0' :: nat
    assume a4: "k0 < k2" and a5: "k0' < k2" and
           a6: "\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 + j \<longrightarrow> k' \<le> k0" and
           a7: "\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 + j \<longrightarrow> k' \<le> k0'" and
           a8: "cell_index M w i k0 = cell_index M w i k2 + j" and
           a9: "cell_index M w i k0' = cell_index M w i k2 + j"
    show "k0 = k0'"
    proof (rule ccontr, cases "k0 < k0'")
      case True
      show False using a6 [THEN spec, THEN mp, THEN mp, OF a5 a9] True by simp
    next
      case False
      assume a10: "k0 \<noteq> k0'"
      have *: "k0' < k0" using False a10 by simp
      show False using a7 [THEN spec, THEN mp, THEN mp, OF a4 a8] * by simp
    qed
  qed
  define k :: nat where "k \<equiv> Max {k. k < k2 \<and> cell_index M w i k = cell_index M w i k2 + j}"
  show "\<exists>k<k2. (\<forall>k'<k2. cell_index M w i k' = cell_index M w i k2 + j \<longrightarrow> k' \<le> k) \<and>
        cell_index M w i k = cell_index M w i k2 + j \<and>
        nth_ctape (ctapes ((TM.cstep M ^^ k2) (TM.cinitial_config M w)) ! i) j =
        TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
  proof (rule exI, safe)
    have 0: "{k. k < k2 \<and> cell_index M w i k = cell_index M w i k2 + j} \<noteq> {}"
      using a1 a2 by blast
    have 1: "k \<le> k2"
      unfolding k_def apply (rule natset_bounded_Max_bounded)
       apply fact
      by simp
    have 2: "\<And>k. k \<in> {k. k < k2 \<and> cell_index M w i k = cell_index M w i k2 + j} \<Longrightarrow> k < k2" by simp
    show 3: "k < k2" using 1 unfolding k_def
      by (metis (no_types, lifting) 0 Max_in finite_nat_set_iff_bounded mem_Collect_eq)
    show 4: "\<And>k'. k' < k2 \<Longrightarrow> cell_index M w i k' = cell_index M w i k2 + j \<Longrightarrow> k' \<le> k"
      unfolding k_def by auto
    show 5: "cell_index M w i k = cell_index M w i k2 + j"
      using 0 2 unfolding k_def by (metis (mono_tags, lifting) Max_in finite_nat_set_iff_bounded mem_Collect_eq)
    have 6: "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
      using a4 1 unfolding TM.cis_final_def [symmetric] apply auto
      by (metis cis_final_sub_imp diff_diff_cancel)
    have 7: "nth_ctape (ctapes ((TM.cstep M ^^ k') (TM.cinitial_config M w)) ! i)
             ((cell_index M w i k) - (cell_index M w i k')) =
             TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
             (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
      if "k' \<ge> Suc k" and "k' \<le> k2" for k' :: nat using that
    proof (induction k' rule: nat_induct_at_least)
      case base
      show ?case apply simp
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
          apply (subst cell_index.simps(2))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply simp
          apply (subst nth_ctape_cstep_Shift_Left2)
              apply simp_all
            apply (rule 6)
           apply (rule a3)+
         apply (subst cell_index.simps(3))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply simp
         apply (subst nth_ctape_cstep_Shift_Right2)
             apply simp_all
           apply (rule 6)
          apply (rule a3)+
        apply (subst cell_index.simps(4))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply simp
        apply (subst nth_ctape_cstep_No_Shift2)
            apply simp_all
        apply (rule 6)
        by (rule a3)+
    next
      case (Suc n)
      hence *: "n \<le> k2" by simp
      note 7 = Suc(2) [OF *]
      have 8: "cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
        using a4 * unfolding TM.cis_final_def [symmetric] apply auto
        by (metis cis_final_sub_imp diff_diff_cancel)
      have 9: "cell_index M w i k \<noteq> cell_index M w i n"
        by (metis 4 5 Suc.hyps Suc.prems less_eq_Suc_le not_less_eq_eq)
      show ?case apply (subst 7 [symmetric])
        apply simp
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))) i")
          apply (subst cell_index.simps(2))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply (cases "cell_index M w i k - (cell_index M w i n - 1) = 1")
           apply (simp add: 9)
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply simp_all
            apply (rule 8)
           apply (rule a3)+
         apply (subst cell_index.simps(3))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply (cases "cell_index M w i k - (cell_index M w i n - 1) = -1")
          apply (simp add: 8 a3 nth_ctape_cstep_Shift_Right1)
         apply (subst nth_ctape_cstep_Shift_Right1)
              apply simp_all
             apply (rule 8)
           apply (rule a3)+
         apply (rule 9)
        apply (subst cell_index.simps(4))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        apply (cases "cell_index M w i k - (cell_index M w i n - 1) = 0")
         apply (simp add: 8 a3 nth_ctape_cstep_No_Shift1)
        apply (subst nth_ctape_cstep_No_Shift1)
             apply simp_all
           apply (rule 8)
          apply (rule a3)+
        by (rule 9)
    qed
    have 8: "Suc k \<le> k2" using 3 by simp
    show "nth_ctape (ctapes ((TM.cstep M ^^ k2) (TM.cinitial_config M w)) ! i) j =
          TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
          (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i"
      by (rule 7 [OF 8 Nat.le_refl, unfolded 5, simplified])
  qed
qed
end