theory ExtBinary
imports Main Binary
begin
type_synonym bin' = "bool list list"

datatype bit2 = TT | TF | FT | FF (* Use this definition maybe, if working
                                     specifically with lists of lists of length 2 is
                                     too tedious. Then, less conditions are necessary.
                                  *)

instantiation bit2 :: finite
begin
instance proof
  have 1: "UNIV = {TT, TF, FT, FF}" apply auto
    by (metis bit2.exhaust)
  show "finite (UNIV :: bit2 set)" unfolding 1 by simp
qed
end

type_synonym bin2 = "bit2 list"

fun bin_of_bin2 :: "bin2 \<Rightarrow> bin" where
  "bin_of_bin2 [] = []" |
  "bin_of_bin2 (TT#t) = bin_of_bin2 t@[True, True]" |
  "bin_of_bin2 (TF#t) = bin_of_bin2 t@[False, True]" |
  "bin_of_bin2 (FT#t) = bin_of_bin2 t@[True, False]" |
  "bin_of_bin2 (FF#t) = bin_of_bin2 t@[False, False]"

fun bin2_of_bin :: "bin \<Rightarrow> bin2" where
  "bin2_of_bin [] = []" |
  "bin2_of_bin [True] = [FT]" |
  "bin2_of_bin [False] = [FF]" |
  "bin2_of_bin (True#True#t) = bin2_of_bin t@[TT]" |
  "bin2_of_bin (True#False#t) = bin2_of_bin t@[FT]" |
  "bin2_of_bin (False#True#t) = bin2_of_bin t@[TF]" |
  "bin2_of_bin (False#False#t) = bin2_of_bin t@[FF]"

fun bin_of_bin' :: "bin' \<Rightarrow> bin" where
  "bin_of_bin' b' = trimRight False (rev (flatten b'))"

fun bin'_of_bin :: "bin \<Rightarrow> bin'" where
  "bin'_of_bin b = group_2 False (rev b)"

fun starts_with_True :: "bin' \<Rightarrow> bool" where
  "starts_with_True [] \<longleftrightarrow> False" |
  "starts_with_True (h#t) \<longleftrightarrow> True \<in> set h"

lemma starts_with_True_app: "xs1 \<noteq> [] \<Longrightarrow> starts_with_True (xs1 @ xs2) \<longleftrightarrow>
                             starts_with_True xs1"
  by (induction xs1) simp_all

lemma trim_flatten_bin'_of_bin [simplified, simp]:
      "trimLeft False (flatten (bin'_of_bin b)) = trimLeft False (rev b)"
  apply (induction False b rule: group_2.induct)
    apply auto
  by (metis dropWhile.simps(2) flatten_group_2_even flatten_group_2_odd)+

lemma inc'_inner_cases: "(l = [] \<Longrightarrow> P) \<Longrightarrow> (l = [False] \<Longrightarrow> P) \<Longrightarrow>
                         (l = [True] \<Longrightarrow> P) \<Longrightarrow> (\<And>b. l = [b, False] \<Longrightarrow> P) \<Longrightarrow>
                         (l = [False, True] \<Longrightarrow> P) \<Longrightarrow> (l = [True, True] \<Longrightarrow> P) \<Longrightarrow>
                         (\<And>t b1 b2 b3. l = t @ [b1, b2, b3] \<Longrightarrow> P) \<Longrightarrow> P"
    apply (induction l)
     apply auto
  by (metis append_Nil)

fun inc' :: "bin' \<Rightarrow> bin'" where
  "inc' b = group_2 False (rev (inc (bin_of_bin' b)))"

fun bin'_of_nat :: "nat \<Rightarrow> bin'" where
  "bin'_of_nat n = bin'_of_bin (bin_of_nat n)"

fun nat_of_bin' :: "bin' \<Rightarrow> nat" where
  "nat_of_bin' b' = nat_of_bin (bin_of_bin' b')"

lemma inc'_Suc: "nat_of_bin' (inc' b) = Suc (nat_of_bin' b)"
  apply auto
  by (metis bin_nat_bin_drop_zs inc_Suc nat_bin_nat)

definition bin'_wf :: "bin' \<Rightarrow> bool" where
  "bin'_wf b' \<equiv> \<forall>bit\<in>set b'. length bit = 2"

lemma length_2_ex_iff: "length l = 2 \<longleftrightarrow> (\<exists>x y. l = [x, y])"
  by (induction l) (auto simp add: length_1_ex_iff)

lemma bin'_wfI [intro]: "(\<And>bit. bit \<in> set b' \<Longrightarrow> \<exists>x y. bit = [x, y]) \<Longrightarrow> bin'_wf b'"
  unfolding bin'_wf_def length_2_ex_iff by simp

lemma bin'_wfE [elim]: "bin'_wf b' \<Longrightarrow>
                        ((\<And>bit. bit \<in> set b' \<Longrightarrow> \<exists>x y. bit = [x, y]) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding bin'_wf_def length_2_ex_iff by simp

lemma bin'_wfD: "bin'_wf b' \<Longrightarrow> b \<in> set b' \<Longrightarrow> \<exists>x y. b = [x, y]"
  by blast

lemma bin'_wf_ConsD: "bin'_wf (h#t) \<Longrightarrow> bin'_wf t"
  by fastforce

lemma bin'_wf_even: "bin'_wf b' \<Longrightarrow> even (length (flatten b'))"
  by (induction b') (simp_all add: bin'_wf_def)

lemma bin'_of_bin_eq1: "ends_in True b \<Longrightarrow> bin_of_bin' (bin'_of_bin b) = b"
  by auto

lemma nat_bin'_nat [simp]: "nat_of_bin' (bin'_of_nat n) = n"
  apply (induction n)
   apply auto
  by (metis bin_nat_bin_drop_zs inc_Suc nat_bin_nat)

lemma bin'_wf_length [simp]: "bin'_wf b' \<Longrightarrow> length (flatten b') = 2 * length b'"
  apply (induction b')
   apply auto
  apply (frule bin'_wf_ConsD)
  by (simp add: bin'_wf_def)

lemma bin'_wf_empty [simp, intro]: "bin'_wf []"
  by auto

lemma bin'_wf_appI: "bin'_wf b1 \<Longrightarrow> bin'_wf b2 \<Longrightarrow> bin'_wf (b1@b2)"
  by fastforce

lemma bin'_wf_appE [elim]: "bin'_wf (xs1@xs2) \<Longrightarrow>
                            (bin'_wf xs1 \<Longrightarrow> bin'_wf xs2 \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction xs1) (simp_all add: bin'_wf_def)

lemma bin'_wf_rev [simp]: "bin'_wf (rev xs) \<longleftrightarrow> bin'_wf xs"
  unfolding bin'_wf_def by simp

lemma bin'_wf_induct [case_names Nil Cons2]: "P [] \<Longrightarrow> (\<And>xs x y. bin'_wf xs \<Longrightarrow> P xs \<Longrightarrow> P ([x, y]#xs)) \<Longrightarrow>
                                              bin'_wf xs \<Longrightarrow> P xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then obtain x y :: bool where a_def: "a = [x, y]" by fastforce
  show ?case unfolding a_def apply (rule Cons(3))
    using Cons(4) apply fastforce
    apply (rule Cons(1))
    apply fact+
    using Cons(4) by fastforce
qed

lemma bin'_wf_rev_induct [case_names Nil snoc2]:
  "P [] \<Longrightarrow> (\<And>xs x y. bin'_wf xs \<Longrightarrow> P xs \<Longrightarrow> P (xs@[[x, y]])) \<Longrightarrow> bin'_wf xs \<Longrightarrow> P xs"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc a xs)
  then obtain x y :: bool where a_def: "a = [x, y]" by fastforce
  show ?case unfolding a_def apply (rule snoc(3))
    using snoc(4) apply blast
    apply (rule snoc(1))
    apply fact+
    using snoc(4) by blast
qed

lemma group_2_bin'_wf [intro]: "bin'_wf (group_2 d b)"
  apply (induction b rule: group_2_Cons_induct)
     apply auto
    apply (simp add: bin'_wf_def)
   apply (simp add: bin'_wf_def even_group_2_Cons2)
  apply (simp add: odd_group_2_Cons bin'_wf_def odd_group_2_Cons1)
  by (metis even_diff_nat even_group_2_Cons1 even_plus_one_iff even_zero
      length_0_conv length_tl list.exhaust_sel list.set_intros(2))

lemma bin'_of_bin_wf [intro]: "bin'_wf (bin'_of_bin b)"
  by auto

lemma bin'_of_nat_wf [intro]: "bin'_wf (bin'_of_nat n)"
  by auto

lemma bin'_cases: "(\<forall>s\<in>set b'. \<exists>x. s = [x]) \<longleftrightarrow>
                   (\<forall>s\<in>set b'. s = [True] \<or> s = [False])"
  by auto

lemma subset_TF_iff: "(\<forall>s\<in>set b'. \<exists>x. s = [x]) \<longleftrightarrow> set b' \<subseteq> {[True], [False]}"
  by auto

lemma inc'_not_Nil: "inc' xs \<noteq> []"
  by (simp add: inc_not_Nil)

lemma inc'_altdef: "bin_of_bin' (inc' xs) = trimRight False (inc (rev (flatten xs)))"
  apply auto
  by (metis ExtBinary.bin_of_bin'.simps bin_nat_bin_drop_zs inc_Suc nat_bin_nat
      rev_swap)

lemma nat_of_bin'_app0: "nat_of_bin' ([False, False] # xs) = nat_of_bin' xs"
  by (induction xs) simp_all

lemma flatten_nat_of_bin'_cong: "flatten xs1 = flatten xs2 \<Longrightarrow>
                                 nat_of_bin' xs1 = nat_of_bin' xs2"
  by simp

lemma flatten_bin_of_bin'_cong: "flatten xs1 = flatten xs2 \<Longrightarrow>
                                 bin_of_bin' xs1 = bin_of_bin' xs2"
  by simp

lemma nat_of_bin_via_bin' [simp]: "nat_of_bin' (bin'_of_bin b) = nat_of_bin b"
  using nat_of_bin_trim by simp

lemma bin'_of_nat_of_bin: "bin'_of_nat (nat_of_bin b) =
                           bin'_of_bin (trimRight False b)"
  by (simp add: bin_nat_bin_drop_zs)

lemma nat_of_bin'_app1_1: "nat_of_bin' ([False, True] # xs) =
                           nat_of_bin' xs + 2 ^ length (flatten xs)"
  apply (induction xs)
   apply auto
  by (metis add.commute append_Cons length_append length_rev nat_of_bin_append1
      nat_of_bin_trim rev.simps(2) rev_append rev_rev_ident)

lemma nat_of_bin'_app1_2: "nat_of_bin' ([True, False]#xs) =
                           nat_of_bin' xs + 2 ^ (Suc (length (flatten xs)))"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  have 1: "nat_of_bin (rev (dropWhile Not xs)) =
           nat_of_bin (rev xs)" for xs
    by (metis nat_of_bin_trim rev_rev_ident)
  show ?case apply (simp add: 1)
    by (smt (verit, del_insts) Binary.inc.simps(1) One_nat_def add.commute
        add_2_eq_Suc' append.assoc inc_Suc length_append length_rev mult_2
        nat_of_bin.simps(1) nat_of_bin.simps(2) nat_of_bin_app numeral_2_eq_2
        plus_1_eq_Suc)
qed

lemma nat_of_bin'_app1_3: "nat_of_bin' ([True, True]#xs) =
                           nat_of_bin' xs + 2 ^ (length (flatten xs)) +
                           2 ^ (Suc (length (flatten xs)))"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  have 1: "nat_of_bin (rev (dropWhile Not xs)) =
           nat_of_bin (rev xs)" for xs
    by (metis nat_of_bin_trim rev_rev_ident)
  show ?case apply (simp add: 1)
    by (smt (verit, del_insts) Binary.inc.simps(1) One_nat_def add.commute
        append.assoc inc_Suc length_append length_rev mult_2 nat_of_bin.simps(1)
        nat_of_bin.simps(2) nat_of_bin_app numeral_3_eq_3 plus_1_eq_Suc)
qed

lemma nat_of_bin'_app: "nat_of_bin' (up @ lo) =
                        (nat_of_bin' up) * 2^(length (flatten lo)) + (nat_of_bin' lo)"
proof (induction lo)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a lo)
  then show ?case apply auto
    by (metis length_append length_rev nat_of_bin_app nat_of_bin_trim
        rev_append rev_swap)
qed

lemma nat_of_bin'_0s [simp]: "nat_of_bin' ((replicate n False) \<up> k) = 0"
  by (induction k) (simp_all add: dropWhile_append)

corollary nat_of_bin'_app_0s: "nat_of_bin' (up @ (replicate n False) \<up> k) =
                               (nat_of_bin' up) * 2^(n * k)"
  apply simp
  by (metis bin_nat_bin_drop_zs nat_bin_nat nat_of_bin_app_0s rev_append
      rev_replicate rev_rev_ident)

corollary nat_of_bin'_leading_0s[simp]: "nat_of_bin' ([False] \<up> k @ xs) =
                                         nat_of_bin' xs"
  by (induction k) simp_all

lemma hd'_one_nonzero: "nat_of_bin' ([True] # xs) > 0" by simp

lemma nat_of_bin'_div2': "nat_of_bin' xs div 2 = nat_of_bin (tl (bin_of_bin' xs))"
  by (induction xs) (auto simp add: map_butlast nat_of_bin_div2'
                      rev_butlast_is_tl_rev)

lemma length_trim_flatten_xs: "length (trimLeft False (flatten xs)) =
                               length (bin_of_bin' xs)"
  by simp

lemma nat_of_bin'_max: "nat_of_bin' xs < 2 ^ (length (flatten xs))"
  apply (induction xs)
   apply auto
  by (metis length_append length_rev nat_of_bin_max nat_of_bin_trim rev_rev_ident)
lemma nat_of_bin'_min: "True \<in> set (flatten xs) \<Longrightarrow> nat_of_bin' xs \<ge>
                        2 ^ (length (trimLeft False (flatten xs)) - 1)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  have "True \<in> set a \<Longrightarrow> 2 ^ (length (dropWhile Not (flatten (a # xs))) - Suc 0)
                          \<le> (rev (dropWhile Not (flatten (a # xs))))\<^sub>2"
    apply (induction a)
    apply auto
    by (smt (verit, ccfv_threshold) left_add_mult_distrib length_rev
        nat_le_iff_add nat_of_bin_app nat_of_bin_app1 power_add trans_le_add2)+
  moreover have "True \<in> set (flatten xs) \<Longrightarrow>
                  2 ^ (length (dropWhile Not (flatten (a # xs))) - Suc 0)
                  \<le> (rev (dropWhile Not (flatten (a # xs))))\<^sub>2" using IH(1) apply auto
    by (metis (full_types) calculation dropWhile_append2 flatten.simps(2))
  ultimately show ?case using IH(2) by fastforce
qed

lemma bin'_of_nat_double: "n > 0 \<Longrightarrow> bin'_of_nat (2 * n) =
                           bin'_of_bin (False#bin_of_nat n)"
  apply (induction n rule: nat_induct_non_zero)
   apply (auto simp: numeral_2_eq_2 inc_inc)
  by (metis bin_of_nat_double bit_len_eq_0_iff bot_nat_0.not_eq_extremum
      inc_inc list.size(3) mult_2 rev.simps(2))

corollary bin'_of_nat_double_p1: "bin'_of_nat (2 * n + 1) =
                                  (bin'_of_bin (True#bin_of_nat n))"
  using bin_of_nat_double by (cases "n > 0") auto

lemma nat_of_bin_dropWhile [simp]: "(rev (dropWhile Not (flatten xs)))\<^sub>2 =
                                    (rev (flatten xs))\<^sub>2"
  apply (induction xs)
   apply auto
  by (metis nat_of_bin_trim rev_append rev_rev_ident)

fun bin'_shr :: "bin' \<Rightarrow> nat \<Rightarrow> bin'" where
  "bin'_shr b' n = bin'_of_bin (drop n (bin_of_bin' b'))"

fun bin'_shl :: "bin' \<Rightarrow> nat \<Rightarrow> bin'" where
  "bin'_shl b' n = bin'_of_bin (replicate n False @ (bin_of_bin' b'))"

lemma nat_of_bin'_shr [simp]: "nat_of_bin' (bin'_shr b' n) =
                               (nat_of_bin' b') div 2 ^ n"
  apply (induction n)
   apply auto
   apply (metis dropWhile_idem_iff nat_of_bin_dropWhile no_leading_dropWhile
      rev_rev_ident trim_flatten_bin'_of_bin)
  using nat_of_bin_drop nat_of_bin_trim by force

lemma nat_of_bin'_shl [simp]: "nat_of_bin' (bin'_shl b' n) =
                               (nat_of_bin' b') * 2 ^ n"
  apply (induction n)
   apply auto
   apply (metis dropWhile_idem_iff nat_of_bin_dropWhile no_leading_dropWhile
      rev_rev_ident trim_flatten_bin'_of_bin)
  by (metis ExtBinary.bin_of_bin'.simps ExtBinary.nat_of_bin'.elims One_nat_def
      bin_nat_bin_drop_zs nat_of_bin_app_0s nat_of_bin_dropWhile nat_of_bin_via_bin'
      plus_1_eq_Suc power_Suc0_right power_add replicate_Suc rev.simps(2) rev_append
      rev_replicate rev_swap trim_flatten_bin'_of_bin)

subsection\<open>Addressing Leading Zeroes\<close>

text\<open>\<^typ>\<open>bin\<close> enables arbitrary string manipulation, but makes reasoning about
  numeric values more difficult, since leading zeroes cause non-injectivity.
  (\<^typ>\<open>num\<close> avoids this issue by defining the MSB to always be \<open>1\<close>,
  at the cost of being able to represent arbitrary strings.)
  To remedy this limitation when handling numeric values, we make use of \<^const>\<open>ends_in\<close>.\<close>

lemma starts_with_True_induct [consumes 1]: "starts_with_True xs \<Longrightarrow>
        (\<And>x. True \<in> set x \<Longrightarrow> P [x]) \<Longrightarrow>
        (\<And>x y xs. P (x#xs) \<Longrightarrow> True \<in> set x \<Longrightarrow> P (x#y#xs)) \<Longrightarrow> P xs"
  apply (cases xs)
   apply auto
  by (metis starts_induct2)

lemma starts_with_True_group_2: "starts_with_True (group_2 False b) \<longleftrightarrow>
                                 b \<noteq> [] \<and> hd b \<or>
                                 length b \<ge> 2 \<and> even (length b) \<and> hd (tl b)"
  apply (induction False b rule: group_2.induct)
    apply auto
                  apply (metis append_Cons append_Nil group_2.simps(3)
      starts_with_True.simps(1) starts_with_True_app)
                 apply (metis append_Cons append_Nil group_2.simps(3)
      group_2_empty_iff starts_with_True_app)
                apply (metis hd_append2 impossible_Cons leD length_Cons list.size(3)
      numeral_2_eq_2 pos2 tl_Nil tl_append2)
               apply (metis append_Cons append_Nil group_2.simps(3)
      starts_with_True.simps(1) starts_with_True_app)
              apply (metis append_Cons append_Nil group_2.simps(3)
      starts_with_True.simps(1) starts_with_True_app)
             apply (metis append_Cons append_Nil group_2.simps(1)
      group_2.simps(3) list.sel(1) list.set(1) list.simps(15) set_ConsD singletonD
      starts_with_True.elims(1))
            apply (metis append.left_neutral append_Cons group_2.simps(1)
      group_2.simps(3) list.set_intros(1) starts_with_True.simps(2))
           apply (metis append.left_neutral append_Cons group_2.simps(1)
      group_2.simps(3) in_set_conv_decomp starts_with_True.simps(2))
               apply (metis append.left_neutral append_Cons flatten_group_2_even
      flatten_group_2_odd gcd_nat.extremum group_2.simps(1) group_2.simps(3)
      list.distinct(1) list.size(3) starts_with_True_app)
proof -
  fix t :: "bool list" and e' e :: bool
  assume a1: "\<not>starts_with_True (group_2 False t)" and
         a2: "\<not>2 \<le> length t" and
         a3: "\<not>hd t" and
         a4: "hd (t @ [e', e])"
  have "t = [] \<Longrightarrow> starts_with_True (group_2 False [e', e])"
  proof -
    assume a5: "t = []"
    have 1: "group_2 False [e', e] = [[e', e]]"
      by (metis append.left_neutral append_Cons group_2.simps(1) group_2.simps(3))
    show "starts_with_True (group_2 False [e', e])" unfolding 1
      using a4 unfolding a5 by simp
  qed
  moreover have "\<And>x. t = [x] \<Longrightarrow> False" using a3 a4 by auto
  ultimately show "starts_with_True (group_2 False (t @ [e', e]))"
    using a2 by (metis a3 a4 append_self_conv2 hd_append2)
next
  fix t :: "bool list" and e' e :: bool
  assume a1: "\<not>starts_with_True (group_2 False t)" and
         a2: "\<not>2 \<le> length t" and
         a3: "\<not>hd t" and
         a4: "hd (tl (t @ [e', e]))" and
         a5: "even (length t)"
  have "t = [] \<Longrightarrow> starts_with_True (group_2 False (t @ [e', e]))"
  proof simp
    assume a5: "t = []"
    have 1: "group_2 False [e', e] = [[e', e]]"
      by (metis append_Cons append_self_conv2 group_2.simps(1) group_2.simps(3))
    show "starts_with_True (group_2 False [e', e])" unfolding 1
      using a4 [unfolded a5] by simp
  qed
  moreover have "\<And>x. t = [x] \<Longrightarrow> False" using a5 by simp
  ultimately show "starts_with_True (group_2 False (t @ [e', e]))"
    by (metis a2 leD le_Suc_eq length_1_hd_iff length_greater_0_conv not_less_eq_eq
        numeral_2_eq_2)
next
  fix t :: "bool list" and e' e :: bool
  assume a1: "\<not>starts_with_True (group_2 False t)" and
         a2: "\<not>2 \<le> length t" and
         a3: "\<not>hd t" and
         a4: "starts_with_True (group_2 False (t @ [e', e]))" and
         a5: "\<not>hd (t @ [e', e])"
  have 1: "t = []" using a1 a4
    by (metis append_Cons append_Nil group_2.simps(3) group_2_empty_iff
        starts_with_True_app)
  have 2: "group_2 False (t @ [e', e]) = [[e', e]]" unfolding 1
    by (metis append_Cons append_Nil group_2.simps(3) group_2_empty_iff)
  have "starts_with_True [[e', e]]" using a4 by (unfold 2)
  hence "e' \<or> e" by simp
  moreover have "\<not>e'" using a5 unfolding 1 by simp
  ultimately have e by blast
  thus "hd (tl (t @ [e', e]))" unfolding 1 by simp
next
  show 1: "\<And>e' e. starts_with_True (group_2 False [False, e]) \<Longrightarrow> \<not> e' \<Longrightarrow> e"
    by (metis append.left_neutral append_Cons empty_iff group_2.simps(1)
        group_2.simps(3) insert_iff list.set(1) list.simps(15)
        starts_with_True.simps(2))
  show 2: "\<And>e. starts_with_True (group_2 False [True, e])"
    by (metis append.left_neutral append_Cons group_2.simps(1) group_2.simps(3)
        list.set_intros(1) starts_with_True.simps(2))
  show 3: "\<And>e'. starts_with_True (group_2 False [e', True])"
    by (metis append_Cons eq_Nil_appendI group_2.simps(3) group_2_empty_iff
        list.set_intros(1) list.set_intros(2) starts_with_True.simps(2))
  show 4: "\<And>t e' e. \<not> starts_with_True (group_2 False t) \<Longrightarrow> \<not> hd t \<Longrightarrow>
           odd (length t) \<Longrightarrow> starts_with_True (group_2 False (t @ [e', e])) \<Longrightarrow>
           \<not> hd (t @ [e', e]) \<Longrightarrow> False"
    by (metis append.left_neutral append_Cons flatten_group_2_even flatten_group_2_odd
        gcd_nat.extremum group_2.simps(1) group_2.simps(3) list.distinct(1)
        list.size(3) starts_with_True_app)
  thus "\<And>t e' e. \<not> starts_with_True (group_2 False t) \<Longrightarrow> \<not> hd t \<Longrightarrow>
        odd (length t) \<Longrightarrow> starts_with_True (group_2 False (t @ [e', e])) \<Longrightarrow>
        \<not> hd (t @ [e', e]) \<Longrightarrow> hd (tl (t @ [e', e]))" by blast
  show "\<And>t e' e. \<not> starts_with_True (group_2 False t) \<Longrightarrow> \<not> hd t \<Longrightarrow>
        odd (length t) \<Longrightarrow> hd (t @ [e', e]) \<Longrightarrow>
        starts_with_True (group_2 False (t @ [e', e]))"
    using hd_append2 odd_pos by blast
  show "\<And>t e' e. \<not> starts_with_True (group_2 False t) \<Longrightarrow> \<not> hd t \<Longrightarrow> \<not> hd (tl t) \<Longrightarrow>
        starts_with_True (group_2 False (t @ [e', e])) \<Longrightarrow> \<not> hd (t @ [e', e]) \<Longrightarrow>
        even (length t)" using 4 by blast
  show "\<And>t e' e. \<not> starts_with_True (group_2 False t) \<Longrightarrow> \<not> hd t \<Longrightarrow> \<not> hd (tl t) \<Longrightarrow>
        starts_with_True (group_2 False (t @ [e', e])) \<Longrightarrow> \<not> hd (t @ [e', e]) \<Longrightarrow>
        hd (tl (t @ [e', e]))"
    by (smt (z3) 1 append_Cons append_Nil group_2.simps(2) group_2.simps(3)
        group_2_empty_iff list.sel(1) list.sel(3) starts_with_True_app)
  show "\<And>t e' e. \<not> starts_with_True (group_2 False t) \<Longrightarrow> \<not> hd t \<Longrightarrow> \<not> hd (tl t) \<Longrightarrow>
        hd (t @ [e', e]) \<Longrightarrow> starts_with_True (group_2 False (t @ [e', e]))"
    by (metis (mono_tags, lifting) 2 append_Nil hd_append list.sel(1))
  show "\<And>t e' e. \<not> starts_with_True (group_2 False t) \<Longrightarrow> \<not> hd t \<Longrightarrow> \<not> hd (tl t) \<Longrightarrow>
        even (length t) \<Longrightarrow> hd (tl (t @ [e', e])) \<Longrightarrow>
        starts_with_True (group_2 False (t @ [e', e]))"
    by (smt (z3) 3 append.left_neutral dvd_imp_le hd_append2 impossible_Cons
        length_Cons length_greater_0_conv list.exhaust_sel list.sel(3) list.size(3)
        not_Cons_self2 numeral_2_eq_2 separator_def tl_append2)
qed

lemma starts_with_True_bin'_bin: "ends_in True b \<Longrightarrow> starts_with_True (bin'_of_bin b)"
  using starts_with_True_group_2 by force

lemma inc'_start_True[simp]:
  fixes xs
  assumes "starts_with_True xs" and
          "bin'_wf xs"
        shows "starts_with_True (inc' xs)"
  using assms apply simp unfolding starts_with_True_group_2
  apply auto
  using inc_not_Nil apply blast
      apply (smt (verit, best) One_nat_def diff_Suc_1 diff_Suc_Suc diff_Suc_less
      hd_rev inc_Suc last.simps leI length_0_conv length_1_ex_iff length_inc_rev
      less_2_cases_iff less_Suc_eq less_not_refl3 nat_of_bin.simps(1) nat_of_bin_app0
      replicate_0 replicate_append_same)
  using inc_not_Nil apply blast
      apply (smt (verit, best) One_nat_def diff_Suc_1 diff_Suc_Suc diff_Suc_less
      hd_rev inc_Suc last.simps leI length_0_conv length_1_ex_iff length_inc_rev
      less_2_cases_iff less_Suc_eq less_not_refl3 nat_of_bin.simps(1) nat_of_bin_app0
      replicate_0 replicate_append_same)
  by (metis bin_nat_bin_drop_zs bin_of_nat.simps(2) dropWhile_dropWhile1
      dropWhile_eq_self_iff inc_Suc inc_not_Nil rev_is_Nil_conv rev_swap)+

lemma bin'_of_nat_gt_0_start_True[simp]: "n > 0 \<Longrightarrow> starts_with_True (bin'_of_nat n)"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  have "bin'_wf (bin'_of_nat n)" by blast
  with \<open>starts_with_True (bin'_of_nat n)\<close> show ?case
    unfolding bin'_of_nat.simps
  proof (cases "set (bin_of_nat n) = {True}")
    case True
    then obtain k :: nat where n_def: "bin_of_nat n = replicate k True"
      by (metis replicate_length_same singletonD)
    hence "inc (bin_of_nat n) = replicate k False @ [True]"
      by (metis Binary.inc.simps(1) append_Nil2 inc_append_overflow)
    then show "starts_with_True (ExtBinary.bin'_of_bin (bin_of_nat (Suc n)))"
      using starts_with_True_bin'_bin by blast
  next
    case False
    then show "starts_with_True (ExtBinary.bin'_of_bin (bin_of_nat (Suc n)))"
      using starts_with_True_bin'_bin by blast
  qed
qed \<comment> \<open>case \<^term>\<open>n = 1\<close> by\<close> simp

lemma nat_of_bin'_gt_0_start_True[simp]:
  assumes eTw: "starts_with_True w"
  shows "nat_of_bin' w > 0"
  using assms apply (induction w)
   apply auto
  by (smt (verit, ccfv_SIG) Nil_is_rev_conv add_is_0 bin_nat_bin_drop_zs
      bin_of_nat.simps(1) dropWhile_dropWhile1 dropWhile_eq_Nil_conv gr_zeroI
      mult_is_0 nat_of_bin_app nat_of_bin_max rev_rev_ident)



subsection\<open>String Length\<close>

lemma inc'_len: "bin'_wf xs \<Longrightarrow> starts_with_True xs \<Longrightarrow> length xs \<le> length (inc' xs)"
proof (cases "set (flatten xs) = {True}")
  case True
  assume a1: "bin'_wf xs"
  obtain n :: nat where flatten_xs_def: "flatten xs = replicate (2 * n) True"
    using True a1 by (metis bin'_wf_length dual_order.refl replicate_set_eq)
  hence 1: "length xs = n" using a1
    by (metis bin'_wf_length length_replicate mult_cancel1 nat_less_le pos2)
  show ?thesis by (simp add: flatten_xs_def 1)
next
  case False
  assume a1: "bin'_wf xs" and a2: "starts_with_True xs"
  then show ?thesis
    apply (cases "set (flatten xs) = {}")
    using False apply simp
     apply (metis bin'_wf_empty bin'_wf_length flatten.simps(1) le_SucI
        le_zero_eq list.size(3) mult_cancel1 zero_neq_numeral)
  proof -
    assume a1: "bin'_wf xs" and a3: "set (flatten xs) \<noteq> {}"
    hence 1: "False \<in> set (flatten xs)" using False
      by (smt (verit, ccfv_SIG) singletonI subset_iff subset_singletonD)
    have "length (flatten xs) = length (flatten (inc' xs))"
    proof auto
      obtain h :: "bool list" and t :: "bool list list" where xs_def: "xs = h#t"
        using a3 by (metis flatten.elims set_empty)
      obtain x y :: bool where h_def: "h = [x, y]" using a1 xs_def
        by (meson bin'_wfE list.set_intros(1))
      have 2: "xs = [x, y]#t" unfolding xs_def h_def ..
      have 3: "x \<or> y" using a2 unfolding 2 by simp
      show "length (flatten xs) = length (flatten (group_2 False (rev (inc (rev
            (dropWhile Not (flatten xs)))))))" unfolding 2 using 3 apply auto
           apply (smt (z3) a1 add_2_eq_Suc' bin'_wf_ConsD bin'_wf_even even_Suc
            flatten_group_2_even length_Cons length_append length_inc_eq_iff
            length_rev less_add_Suc2 list.size(3) nth_append_length nth_mem
            numeral_2_eq_2 plus_1_eq_Suc xs_def)
      proof -
        assume a4: x and a5: y
        have "False \<in> set (flatten t)" using 1 2 a4 a5 by auto
        thus "Suc (Suc (length (flatten t))) = length (flatten (group_2 False (rev
              (inc (rev (flatten t) @ [True, True])))))"
          by (smt (z3) a1 add_2_eq_Suc' bin'_wf_ConsD bin'_wf_even even_Suc
              flatten_group_2_even inc_append_no_overflow length_Cons length_append
              length_inc_eq_iff length_rev list.size(3) numeral_2_eq_2 set_rev xs_def)
        thus "Suc (Suc (length (flatten t))) = length (flatten (group_2 False (rev
              (inc (rev (flatten t) @ [True, True])))))" .
      next
        show "y \<Longrightarrow> \<not> x \<Longrightarrow> Suc (Suc (length (flatten t))) =
              length (flatten (group_2 False (rev (inc (rev (flatten t) @ [True])))))"
          by (smt (z3) a1 bin'_wf_ConsD bin'_wf_even even_Suc flatten_group_2_even
              flatten_group_2_odd length_Cons length_append_singleton
              length_inc_cases length_rev xs_def)
      qed
    qed
    thus "length xs \<le> length (ExtBinary.inc' xs)" by (simp add: a1 group_2_bin'_wf)
  qed
qed

lemma nat_of_bin'_len_mono:
  assumes e: "starts_with_True ys" and wfxs: "bin'_wf xs" and wfys: "bin'_wf ys"
    and l: "length (trimLeft False (flatten xs)) <
            length (trimLeft False (flatten ys))"
  shows "nat_of_bin' xs < nat_of_bin' ys"
proof -
  have "nat_of_bin' xs < 2 ^ (length (trimLeft False (flatten xs)))"
    using ExtBinary.nat_of_bin'.simps length_trim_flatten_xs
      nat_of_bin_max by presburger
  also have "... \<le> 2 ^ (length (trimLeft False (flatten ys)) - 1)"
    using l by fastforce
  also have "... \<le> nat_of_bin' ys"
    by (metis (full_types) ExtBinary.nat_of_bin'_min dropWhile_eq_Nil_conv
        l less_nat_zero_code list.size(3))
  finally show ?thesis .
qed


subsubsection\<open>Bit-Length\<close>

text\<open>The number of bits in the binary representation.
  This does not count any leading zeroes; the bit-length of \<open>0\<close> is \<open>0\<close>.\<close>

subsection\<open>Inverses\<close>
corollary surj_nat_of_bin': "surj nat_of_bin'" using nat_bin'_nat by (rule surjI)

lemma bin'_nat_bin'[simp]: "starts_with_True w \<Longrightarrow> bin'_wf w \<Longrightarrow>
                            bin'_of_nat (nat_of_bin' w) = w"
proof (induction w rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case IH: (snoc x xs)
  then obtain a b :: bool where x_def [simp]: "x = [a, b]"
    by (meson bin'_wfE bin'_wf_appE list.set_intros(1))
  have "starts_with_True xs \<or> (xs = [] \<and>  a) \<or> (xs = [] \<and> b)"
    by (metis IH.prems(1) append_self_conv2 empty_iff empty_set set_ConsD
        starts_with_True.simps(2) starts_with_True_app x_def)
  moreover have "starts_with_True xs \<Longrightarrow> ?case"
  proof -
    assume a1: "starts_with_True xs"
    have 1 [simplified, simp]: "ExtBinary.bin'_of_nat (ExtBinary.nat_of_bin' xs) = xs"
      using IH(1) [OF a1] IH.prems(2) by blast
    have [simp]: "dropWhile Not (flatten xs @ [a, b]) =
                  dropWhile Not (flatten xs) @ [a, b]" using a1
      by (metis ExtBinary.bin_of_bin'.simps ExtBinary.nat_of_bin'.simps
          bin_nat_bin_drop_zs dropWhile_append dropWhile_eq_Nil_conv
          less_numeral_extra(3) nat_bin_nat nat_of_bin'_gt_0_start_True
          nat_of_bin.simps(1) nat_of_bin_dropWhile rev.simps(1))
    have 2: "Suc (Suc (Suc (4 * (rev (flatten xs))\<^sub>2))) =
                  4 * (rev (flatten xs))\<^sub>2 + 3"
      by simp
    have Suc_Suc_2: "Suc (Suc (2 ^ 2 * (rev (flatten xs))\<^sub>2)) =
                  4 * (rev (flatten xs))\<^sub>2 + 2"
      by simp
    have 3: "(4::nat) = 2 ^ 2" by simp
    have 4: "bin_of_nat 3 = [True, True]" by (simp add: numeral_3_eq_3)
    have 5: "bin_of_nat (2\<^sup>2 * (rev (flatten xs))\<^sub>2 + 3) =
             bin_of_nat 3 @ bin_of_nat (rev (flatten xs))\<^sub>2"
      using nat_of_bin_app [of "bin_of_nat 3"] unfolding nat_bin_nat 4 apply simp
      by (metis 3 Binary.inc.simps(2) Suc_eq_plus1 2 bin_of_nat.simps(2)
          bin_of_nat_double_p1 mult.assoc power2_eq_square)
    have 6: "bin_of_nat (2\<^sup>2 * (rev (flatten xs))\<^sub>2 + 2) =
             bin_of_nat 2 @ bin_of_nat (rev (flatten xs))\<^sub>2"
      using nat_of_bin_app [of "bin_of_nat 2"] unfolding nat_bin_nat
      by (metis "3" Binary.inc.simps(1) Binary.inc.simps(2) One_nat_def Suc_1
          Suc_Suc_2 Suc_eq_plus1 append_Cons append_Nil bin_of_nat.simps(1)
          bin_of_nat.simps(2) bin_of_nat_double_p1 mult_numeral_left_semiring_numeral
          num_double)
    show ?case apply (auto simp flip: bin_of_nat.simps(2)) unfolding 2 unfolding 3 5
      apply simp
         apply (metis 1 4 Binary.inc.simps(1) group_2.simps(3) inc_all_True
          replicate_0 rev.simps(1) rev.simps(2))
      unfolding Suc_Suc_2 6
        apply (metis 1 3 6 Binary.inc.simps(1) Binary.inc.simps(2) append_Nil
          bin_of_nat.simps(1) bin_of_nat.simps(2) group_2.simps(3) numeral_2_eq_2
          rev.simps(1) rev.simps(2) rev_append)
       apply (metis (no_types, lifting) 1 ExtBinary.bin_of_bin'.elims
          ExtBinary.nat_of_bin'.simps One_nat_def a1 add.commute append.assoc
          bin_of_nat_double bin_of_nat_double_p1 group_2.simps(3)
          nat_of_bin'_gt_0_start_True nat_of_bin_dropWhile numerals(1) plus_1_eq_Suc
          power_Suc0_right power_add_numeral2 rev.simps(2) rev_rev_ident
          semiring_norm(2))
    proof -
      have f1: "\<forall>b. (b::bool) \<up> 0 = []"
        using replicate_0 by blast
      have f2: "\<forall>bs. ExtBinary.bin'_of_bin bs = group_2 False (rev bs)"
        using ExtBinary.bin'_of_bin.simps by blast
      have f3: "\<forall>n bss. bss = ExtBinary.bin'_of_bin (bin_of_nat n) \<or>
                ExtBinary.bin'_of_nat n \<noteq> bss"
        by (meson ExtBinary.bin'_of_nat.elims)
      have f4: "\<forall>n na nb. (n::nat) * na * nb = n * (na * nb)"
        using mult.assoc by blast
      have f5: "4 = (2::nat)\<^sup>2"
        by simp
      have f6: "\<forall>bs. 0 < length (bs::bool list) \<or> bs = []"
        by fastforce
      have f7: "\<forall>bss. ExtBinary.nat_of_bin' bss = (rev (flatten bss))\<^sub>2"
        by simp
      have "ExtBinary.bin'_of_nat (ExtBinary.nat_of_bin' xs) = xs"
        by simp
      then have "ExtBinary.bin'_of_nat (4 * ExtBinary.nat_of_bin' xs) =
                 xs @ [[False, False]]"
        using f6 f5 f4 f3 f2 f1 by (metis Suc_eq_numeral a1 append.assoc
            bin_of_nat_double group_2.simps(3) length_replicate list.distinct(1)
            nat_0_less_mult_iff nat_of_bin'_gt_0_start_True power2_eq_square
            replicate_Suc rev.simps(2))
      then show "group_2 False (rev (bin_of_nat (2\<^sup>2 * (rev (flatten xs))\<^sub>2))) =
                 xs @ [[False, False]]"
        using f7 f5 f3 f2 by (smt (z3))
    qed
  qed
  moreover have "a \<Longrightarrow> xs = [] \<Longrightarrow> ?case" by (simp_all add: even_group_2_Cons2)
  moreover have "b \<Longrightarrow> xs = [] \<Longrightarrow> ?case" by (simp_all add: even_group_2_Cons2)
  ultimately show ?case by blast
qed

corollary inj_on_nat_of_bin':
  "inj_on nat_of_bin' {w. starts_with_True w \<and> bin'_wf w}"
  apply (intro inj_on_inverseI, elim CollectE)
  apply (rule bin'_nat_bin')
  by simp_all

lemma bij_nat_of_bin':
  "bij_betw nat_of_bin' {w. starts_with_True w \<and> bin'_wf w} {0<..}"
  using inj_on_nat_of_bin'
proof (intro bij_betw_imageI)
  have 1: "inj bin'_of_nat"
  proof
    fix x y :: nat
    assume "bin'_of_nat x = bin'_of_nat y"
    thus "x = y" by (metis ExtBinary.nat_bin'_nat)
  qed
  show "nat_of_bin' ` {w. starts_with_True w \<and> bin'_wf w} = {0<..}"
    apply standard
     apply standard
     apply (erule imageE)
    using nat_of_bin'_gt_0_start_True apply fast
  proof (standard, rule image_eqI)
    fix x' :: nat
    assume a1: "x' \<in> {0<..}"
    show "x' = ExtBinary.nat_of_bin' (bin'_of_nat x')"
      using ExtBinary.nat_bin'_nat by presburger
    show "bin'_of_nat x' \<in> {w. starts_with_True w \<and> bin'_wf w}"
      using a1 bin'_of_nat_gt_0_start_True by blast
  qed
qed

lemma bin'_nat_bin'_drop_zs:
  fixes w :: "bool list list"
  assumes "bin'_wf w"
  shows "bin'_of_nat (nat_of_bin' w) = group_2 False (trimLeft False (flatten w))"
  apply (insert assms, induction w)
   apply auto
  apply (frule bin'_wf_ConsD)
  by (simp add: bin_nat_bin_drop_zs)

lemma group_2_flatten_id [simp]: "bin'_wf b \<Longrightarrow> group_2 d (flatten b) = b"
  apply (induction b)
   apply auto
  apply (frule bin'_wf_ConsD)
proof auto
  fix a :: "bool list" and b :: "bool list list"
  assume a1: "group_2 d (flatten b) = b" and a2: "bin'_wf (a # b)" and a3: "bin'_wf b"
  then obtain x y :: bool where a_def: "a = [x, y]"
    by (meson bin'_wfE list.set_intros(1))
  show "group_2 d (a @ flatten b) = a # b" unfolding a_def
    by (metis a1 append.left_neutral append_Cons even_group_2_Cons2
        flatten_group_2_odd not_Cons_self2)
qed

lemma len_bin_nat_bin': "length (bin_of_nat (nat_of_bin' w)) \<le>
                         length (trimLeft False (flatten w))"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case
  proof (induction a)
    case Nil
    then show ?case by simp
  next
    case IH: (Cons a1 a2)
    have "a1 \<Longrightarrow> ?case" by simp
    moreover have "\<not>a1 \<Longrightarrow> ?case" using IH.IH local.Cons by fastforce
    ultimately show ?case by blast
  qed
qed

lemma length_bin_bin'_nat: "length (bin_of_nat (nat_of_bin' w)) \<le>
                            length (flatten (bin'_of_nat (nat_of_bin' w)))"
  by (metis ExtBinary.bin_of_bin'.elims ExtBinary.nat_bin'_nat
      ExtBinary.nat_of_bin'.simps len_bin_nat_bin length_rev nat_of_bin_dropWhile
      rev_rev_ident)

subsection\<open>Advanced Properties\<close>

definition bit'_length :: "nat \<Rightarrow> nat" where
  "bit'_length n \<equiv> length (trimLeft False (flatten (bin'_of_nat n)))"

lemma bin'_of_nat_div2: "bin'_of_nat (n div 2) = bin'_shr (bin'_of_nat n) 1"
  by (metis ExtBinary.bin'_of_nat.simps ExtBinary.bin_of_bin'.simps
      ExtBinary.nat_bin'_nat ExtBinary.nat_of_bin'.simps One_nat_def bin'_shr.simps
      bin_nat_bin_drop_zs bin_of_nat_div2 drop0 drop_Suc nat_of_bin_trim)

corollary bin'_of_nat_div2_times2: "n > 1 \<Longrightarrow>
  bin'_of_nat (2 * (n div 2)) = group_2 False (rev (tl (bin_of_nat n)) @ [False])"
  by (simp add: bin_of_nat_div2_times2)

corollary bin'_of_nat_div2_times2_len: "n > 1 \<Longrightarrow>
  bit'_length (2 * (n div 2)) = bit'_length n"
  unfolding bit'_length_def apply simp
  by (metis One_nat_def bin_nat_bin_drop_zs bin_of_nat_div2_times2_len
      length_rev nat_bin_nat)

lemma bit'_length_is_bit_length [simp]: "bit'_length n = bit_length n"
  unfolding bit'_length_def apply simp
  by (metis bin_nat_bin_drop_zs length_rev nat_bin_nat)

lemma bit'_length_le_word_length: "bit'_length n \<le> 2 * length (bin'_of_nat n)"
  by simp

lemma bin'_of_nat_start_True[iff]: "starts_with_True (bin'_of_nat n) \<longleftrightarrow> n > 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI)
  show "?lhs \<Longrightarrow> ?rhs" by (drule nat_of_bin'_gt_0_start_True) (unfold nat_bin'_nat)
  show "?rhs \<Longrightarrow> ?lhs" by (rule bin'_of_nat_gt_0_start_True)
qed

lemma nat_of_bin'_lt_pow4k: "length w \<le> k \<Longrightarrow> bin'_wf w \<Longrightarrow> nat_of_bin' w < 4 ^ k"
  apply (induction k rule: nat_induct_at_least)
   apply auto
  by (metis bin'_wf_length length_rev nat_of_bin_max numeral_Bit0_eq_double
      power2_eq_square power_mult)

lemma take_mod': "(nat_of_bin' w) mod 2^k =
                  nat_of_bin (take k (bin_of_bin' w))"
  apply (induction w arbitrary: k)
   apply auto
  using take_mod by blast

subsection\<open>Log and Bit-Length\<close>

lemma bit'_len_eq_log2: "n > 0 \<Longrightarrow> bit'_length n = nat_log 2 n + 1"
proof (simp, induction n rule: log2_induct)
  case (div n)
  from \<open>n \<ge> 2\<close> have "n div 2 > 0" by force

  have "bit_length n = bit_length (2 * (n div 2))" using \<open>n \<ge> 2\<close>
    by (subst bin_of_nat_div2_times2_len) force+
  also have "... = bit_length (n div 2) + 1"
    using \<open>n \<ge> 2\<close> by (subst bit_len_double) force+
  also have "... = nat_log 2 (n div 2) + 1 + 1" unfolding div.IH by simp
  also have "... = nat_log 2 (n) + 1" using log2.rec[OF \<open>n \<ge> 2\<close>] by presburger
  finally show "length (bin_of_nat n) = Suc (nat_log 2 n)" by simp
qed \<comment> \<open>case \<^term>\<open>n < 2\<close> by\<close> force+

lemma bit'_length_eq_log:
  assumes "n > 0"
  shows "bit'_length n = \<lfloor>log 2 n\<rfloor> + 1"
  using assms log2.altdef bit_len_eq_log2 by auto


subsection\<open>Order\<close>

text\<open>From @{cite \<open>ch.~4.4\<close> rassOwf2017}: "we will order two words \<open>u, v \<in> \<Sigma>\<^sup>*\<close> as \<open>u \<le> v \<Longleftrightarrow> (u)\<^sub>2 \<le> (v)\<^sub>2\<close>."
  Note: defining the \<^const>\<open>less\<close> relation is necessary for \<^class>\<open>ord\<close>
  (of which \<^class>\<open>preorder\<close> is a subclass).
  As anti-symmetry is not given, no partial order (\<^class>\<open>order\<close>) can be established.\<close>

\<comment> \<open>The following approach (locale interpretation instead of class instantiation)
  is necessary as \<^typ>\<open>bin\<close> is defined as a type-synonym and not as independent type.\<close>
interpretation bin'_preorder:
  preorder "\<lambda>a b. (nat_of_bin' a) \<le> (nat_of_bin' b)"
           "\<lambda>a b. (nat_of_bin' a) < (nat_of_bin' b)"
  using less_le_not_le le_refl le_trans apply simp apply (rule class.preorder.intro)
  by auto


subsection\<open>Number of Binary Strings of Given Length\<close>

lemma card_bin'_len_eq:
  "card {w::bin'. length w = l \<and> bin'_wf w} = 4 ^ l"
proof -
  let ?bools = "{w::bool list. length w = 2}"
  have card_bools: "card ?bools = 4" by (simp add: card_bin_len_eq)
  have "card {w::bin'. length w = l \<and> bin'_wf w} =
        card {w. set w \<subseteq> ?bools \<and> length w = l}"
    by (metis (mono_tags, lifting) bin'_wf_def mem_Collect_eq subset_code(1))
  also have "... = card ?bools ^ l"
    by (intro card_lists_length_eq finite_bin_len_eq)
  also have "... = 4 ^ l" unfolding card_bools ..
  finally show ?thesis .
qed

lemma flatten_surj: "surj flatten"
  by (metis append_Nil2 concat.simps(1) concat.simps(2) flatten_is_concat surj_def)

corollary finite_bin'_len_eq:
  "finite {w::bin'. length w = l \<and> bin'_wf w}"
  using card_bin'_len_eq by (intro card_ge_0_finite) presburger

corollary finite_bin'_len_less:
  "finite {w::bin'. length w < l \<and> bin'_wf w}"
proof -
  let ?W = "\<lambda>l. {w::bin'. length w = l \<and> bin'_wf w}"
  let ?W\<^sub>L = "{?W l' | l'. l' < l}"

  have *: "{w::bin'. length w < l \<and> bin'_wf w} = \<Union> ?W\<^sub>L" by blast
  show "finite {w::bin'. length w < l \<and> bin'_wf w}" unfolding *
    using finite_bin_len_eq apply (intro finite_Union) apply auto
    by (rule finite_bin'_len_eq)
qed

(*lemma card_bin'_len_less:
  "card {w::bin'. length w < l \<and> bin'_wf w} = 4 ^ l - 1"
proof -
  let ?W = "\<lambda>l. {w::bin'. length w = l \<and> bin'_wf w}"
  let ?W\<^sub>L = "{?W l' | l'. l' < l}"

  have "card {w::bin'. length w < l \<and> bin'_wf w} = card (\<Union> ?W\<^sub>L)"
    by (intro arg_cong[where f=card]) blast
  also have "card (\<Union> ?W\<^sub>L) = sum card ?W\<^sub>L"
  proof (intro card_Union_disjoint)
    show "pairwise disjnt ?W\<^sub>L"
    proof (intro pairwiseI)
      fix x y
      assume "x \<in> ?W\<^sub>L" then obtain l\<^sub>x where l\<^sub>x: "x = ?W l\<^sub>x" by blast
      assume "y \<in> ?W\<^sub>L" then obtain l\<^sub>y where l\<^sub>y: "y = ?W l\<^sub>y" by blast

      assume "x \<noteq> y"
      then have "l\<^sub>x \<noteq> l\<^sub>y" unfolding l\<^sub>x l\<^sub>y by force
      then show "disjnt x y" unfolding l\<^sub>x l\<^sub>y disjnt_def by blast
    qed

    fix W
    assume "W \<in> ?W\<^sub>L" then obtain l\<^sub>W where "W = ?W l\<^sub>W" by blast
    show "finite W" unfolding \<open>W = ?W l\<^sub>W\<close> by (rule finite_bin'_len_eq)
  qed
  also have "sum card ?W\<^sub>L = sum card (?W ` {..<l})"
    by (intro arg_cong[where f="sum card"]) (unfold lessThan_def, rule image_Collect[symmetric])
  also have "sum card (?W ` {..<l}) = sum (card \<circ> ?W) {..<l}"
  proof (intro sum.reindex inj_onI)
    fix x y :: nat
    obtain w :: bin' where "length w = x" and "bin'_wf w"
      by (meson bin'_wfI in_set_replicate length_replicate)
    assume "?W x = ?W y"
    then have "w \<in> ?W x \<longleftrightarrow> w \<in> ?W y" by (rule arg_cong)
    hence "length w = x \<and> bin'_wf w \<longleftrightarrow>
           length w = y \<and> bin'_wf w" by simp
    hence "length w = x \<Longrightarrow> length w = y"
      by (simp add: \<open>bin'_wf w\<close>)
    then show "x = y" unfolding \<open>length w = x\<close> by force
  qed
  also have "sum (card \<circ> ?W) {..<l} = (\<Sum>n<l. 4^n)"
    unfolding comp_def card_bin'_len_eq ..
  also have "... = 4^l - 1" unfolding lessThan_atLeast0 sorry
  finally show ?thesis .
qed*)

lemma bit'_length_pow2_eq: "bit'_length n = k \<Longrightarrow> n < 2 ^ k"
proof (induct k)
  case 0
  then show ?case unfolding bit'_length_is_bit_length by fastforce
next
  case (Suc k)
  then show ?case unfolding bit'_length_is_bit_length
    by (metis nat_bin_nat nat_of_bin_max)
qed

lemma lengths_le: "n \<le> x \<Longrightarrow> length (bin_of_nat n) \<le> length (bin_of_nat x)"
  by (rule Binary.lengths_le)

lemma lengths_lt: "length (bin_of_nat n) < length (bin_of_nat x) \<Longrightarrow> n < x"
  by (rule Binary.lengths_lt)

lemma rev_bin'_nat_bin'_rev_id [simp]: "starts_with_True (rev l) \<Longrightarrow> bin'_wf l \<Longrightarrow>
                                        rev (bin'_of_nat (nat_of_bin' (rev l))) = l"
  apply (induction l)
   apply auto
  by (smt (z3) ExtBinary.bin'_nat_bin' ExtBinary.bin'_nat_bin'_drop_zs One_nat_def
      add_Suc_shift bin'_wfE bin'_wf_rev bin_nat_bin_drop_zs dropWhile_cong
      dropWhile_dropWhile1 flatten_concat flatten_group_2_odd group_2.simps(2)
      list.set_intros(1) list.size(3) list.size(4) odd_one plus_1_eq_Suc rev.simps(2)
      rev_rev_ident)

lemma nat_of_bin'_append2 [simp]: "nat_of_bin' ([True, False]#xs) =
                                   2^(Suc (length (flatten xs))) + nat_of_bin' xs"
  apply (induction xs)
   apply auto
proof -
  fix a :: "bool list" and xsa :: "bool list list"
  have "\<forall>bs bsa bsb b. (bs @ bsb = (b::bool) # bsa \<or> ([] \<noteq> bs \<or> b # bsa \<noteq> bsb) \<and>
        (\<forall>bsc. bsc @ bsb \<noteq> bsa \<or> b # bsc \<noteq> bs)) \<and> ([] = bs \<and> b # bsa = bsb \<or>
        (\<exists>bsc. bsc @ bsb = bsa \<and> b # bsc = bs) \<or> bs @ bsb \<noteq> b # bsa)"
    by (metis Cons_eq_append_conv)
  then obtain bbs :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> bool list" and bbsa :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> bool list" where
    f1: "\<forall>bs bsa bsb b. (bs @ bsb = b # bsa \<or> ([] \<noteq> bs \<or> b # bsa \<noteq> bsb) \<and>
        (\<forall>bsc. bsc @ bsb \<noteq> bsa \<or> b # bsc \<noteq> bs)) \<and> ([] = bs \<and> b # bsa = bsb \<or>
        bbs bs bsa bsb b @ bsb = bsa \<and> b # bbs bs bsa bsb b = bs \<or>
        bs @ bsb \<noteq> b # bsa)"
    by moura
  have f2: "\<forall>bss. (rev (dropWhile Not (flatten bss)))\<^sub>2 = ExtBinary.nat_of_bin' bss"
    by simp
  have f3: "\<forall>bs b. bs @ [b::bool] = rev (b # rev bs)"
    by simp
  have f4: "\<forall>b bs bss. flatten (((b::bool) # bs) # bss) = b # flatten (bs # bss)"
    by simp
  have "\<forall>b bs. (b::bool) # rev bs = b # rev (bs @ [])"
    by blast
  then show "(rev (flatten xsa) @ rev a @ [False, True])\<^sub>2 =
             2 * 2 ^ (length a + length (flatten xsa)) +
             (rev (dropWhile Not (a @ flatten xsa)))\<^sub>2"
    using f4 f3 f2 f1 by (metis (no_types) add.commute flatten.simps(2) length_append
        nat_of_bin'_app1_2 nat_of_bin_dropWhile power_Suc rev_append rev_swap)
qed

lemma nat_of_bin'_append1 [simp]: "nat_of_bin' ([False, True]#xs) =
                                   2^(length (flatten xs)) + nat_of_bin' xs"
  apply (induction xs)
   apply auto
  by (metis append_Cons flatten.simps(2) length_append length_rev nat_of_bin_append1
      nat_of_bin_dropWhile rev.simps(2) rev_append)

lemma nat_of_bin'_eq_0_iff: "nat_of_bin' xs = 0 \<longleftrightarrow> set (flatten xs) \<subseteq> {False}"
proof
  assume "nat_of_bin' xs = 0"
  then obtain n :: nat where xs_def: "flatten xs = replicate n False"
    apply auto
    apply (induction xs)
     apply auto
    by (smt (verit) Nil_is_rev_conv bin_nat_bin_drop_zs bin_of_nat.simps(1)
        dropWhile_eq_Nil_conv replicate_length_same rev_append rev_rev_ident)
  show "set (flatten xs) \<subseteq> {False}" unfolding xs_def by auto
next
  assume "set (flatten xs) \<subseteq> {False}"
  thus "nat_of_bin' xs = 0" by (simp add: nat_of_bin_eq_0_iff)
qed

lemma set_all_length_2_wf: "set xs \<subseteq> {w. length w = 2} \<longleftrightarrow> bin'_wf xs"
  by (auto simp add: bin'_wf_def)

lemma bin'_of_nat_times4 [simp]: "n > 0 \<Longrightarrow> bin'_of_nat (4 * n) =
                                  (bin'_of_nat n)@[[False, False]]"
  apply simp
  by (metis ab_semigroup_mult_class.mult_ac(1) append_assoc bin_of_nat_double
      divisors_zero group_2.simps(3) neq0_conv numeral_Bit0_eq_double rev.simps(2)
      zero_neq_numeral)

lemma length_bin'_of_nat_Suc_iff: "length (bin'_of_nat (Suc n)) =
                                   Suc (length (bin'_of_nat n)) \<longleftrightarrow>
                                   (\<exists>k. bin'_of_nat n = replicate k [True, True])"
proof
  assume a1: "length (ExtBinary.bin'_of_nat (Suc n)) =
              Suc (length (ExtBinary.bin'_of_nat n))"
  have "False \<in> set (flatten (bin'_of_nat n)) \<Longrightarrow> False"
    using a1 apply auto
    by (metis div2_Suc_Suc flatten_group_2_even length_group_2 length_inc_cases
        length_inc_eq_iff length_inc_rev length_rev n_not_Suc_n odd_length_group_2)
  hence 1: "\<And>x. x \<in> set (flatten (bin'_of_nat n)) \<Longrightarrow> x" by (metis (full_types))
  have "bin'_wf (bin'_of_nat n)" ..
  hence 2: "\<And>x. x \<in> set (bin'_of_nat n) \<Longrightarrow> x = [False, False] \<or> x = [False, True] \<or>
          x = [True, False] \<or> x = [True, True]" by auto
  have 3: "[False, False] \<in> set (bin'_of_nat n) \<Longrightarrow> False" using 1
    by (metis in_set_flatten_iff list.set_intros(1))
  have 4: "[False, True] \<in> set (bin'_of_nat n) \<Longrightarrow> False" using 1
    by (metis in_set_flatten_iff list.set_intros(1))
  have 5: "[True, False] \<in> set (bin'_of_nat n) \<Longrightarrow> False" using 1
    by (metis in_set_flatten_iff list.set_intros(1) list.set_intros(2))
  show "\<exists>k. bin'_of_nat n = [True, True] \<up> k" using 1 2 3 4 5
    by (metis replicate_length_same)
next
  assume "\<exists>k. bin'_of_nat n = [True, True] \<up> k"
  then obtain k :: nat where k_def: "bin'_of_nat n = [True, True] \<up> k" ..
  have 1: "bin_of_nat n = replicate (2 * k) True" using k_def apply simp
    by (smt (verit, ccfv_threshold) Cons_replicate_eq One_nat_def Suc_1
        flatten_group_2_even flatten_group_2_odd flatten_repl_repl replicate_0
        replicate_Suc rev_replicate rev_rev_ident)
  show "length (ExtBinary.bin'_of_nat (Suc n)) =
        Suc (length (ExtBinary.bin'_of_nat n))"
    unfolding k_def apply simp
    unfolding 1 by simp
qed

lemma flatten_replicate_TT: "flatten ([True, True] \<up> n) = replicate (2 * n) True"
  by (metis One_nat_def Suc_1 flatten_repl_repl replicate_0 replicate_Suc)

lemma inc'_repl_TT [simp]: "inc' (replicate n [True, True]) =
                            [False, True]#(replicate n [False, False])"
  apply simp
  unfolding flatten_replicate_TT apply simp
proof -
  have 1: "even (length (False \<up> (2 * n)))" by simp
  show "group_2 False (True # False \<up> (2 * n)) = [False, True] # [False, False] \<up> n"
    unfolding 1 [THEN even_group_2_Cons1] apply simp
    apply (induction n)
     apply auto
    by (simp add: even_group_2_Cons2)
qed

lemma bin'_of_nat_4_pow [simp]: "bin'_of_nat (4 ^ n) =
                                 [False, True]#(replicate n [False, False])"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have 1: "\<And>n. (4::nat) ^ n = 2 ^ (2 * n)"
    by (metis numeral_Bit0_eq_double power2_eq_square power_mult)
  have 2: "(4::nat) = 2 * 2" by simp
  show ?case unfolding 1 apply simp
    unfolding 2
    by (metis 1 2 ExtBinary.bin'_of_bin.elims ExtBinary.bin'_of_nat.elims Suc
        append_Cons bin'_of_nat_times4 nat_zero_less_power_iff pos2
        replicate_append_same)
qed

lemma bin'_of_nat_Suc_inc': "bin'_of_nat (Suc n) = inc' (bin'_of_nat n)"
  by (metis ExtBinary.bin'_of_bin.simps ExtBinary.bin'_of_nat.simps
      ExtBinary.bin_of_bin'.simps ExtBinary.inc'.simps ExtBinary.nat_bin'_nat
      ExtBinary.nat_of_bin'.simps bin_nat_bin_drop_zs bin_of_nat.simps(2)
      nat_of_bin_trim)

lemma inc'_inj: "bin'_wf xs \<Longrightarrow> bin'_wf ys \<Longrightarrow> starts_with_True xs \<Longrightarrow>
                 starts_with_True ys \<Longrightarrow> inc' xs = inc' ys \<Longrightarrow> xs = ys"
  by (metis ExtBinary.bin'_nat_bin' ExtBinary.inc'_Suc nat.inject)

lemma bin'_wf_replicate_2_bits [intro]: "bin'_wf (replicate n [b1, b2])"
  apply (induction n)
   apply auto
  by (simp add: bin'_wf_def)

lemma bin'_repl: "replicate 2 b = [b, b]"
  by (simp add: numeral_2_eq_2)

lemma length_bin'_of_nat_pow4 [simp]: "length (bin'_of_nat (4 ^ n)) = Suc n"
proof simp
  have "length (bin_of_nat (2 ^ (2 * n))) = Suc (2 * n)"
    apply (induction n)
     apply auto
    by (metis (full_types) length_bin_of_nat_pow2 mult_numeral_left_semiring_numeral
        numeral_Bit0_eq_double numeral_times_numeral power_Suc)
  thus "Suc (length (bin_of_nat (4 ^ n))) div 2 = Suc n"
    by (metis even_Suc even_Suc_div_two nonzero_mult_div_cancel_left
        numeral_Bit0_eq_double odd_Suc_div_two power2_eq_square power_mult
        zero_neq_numeral)
qed

lemma length_bin'_of_nat_le_iff: "length (bin'_of_nat n) \<le> k \<longleftrightarrow> n < 4 ^ k"
proof auto
  assume a1: "Suc (length (bin_of_nat n)) div 2 \<le> k"
  hence 1: "length (bin_of_nat n) \<le> k * 2" by simp
  have "n < 2 ^ (2 * k)" using length_bin_of_nat_le_iff [THEN iffD1, OF 1]
    by (simp add: mult.commute)
  thus "n < 4 ^ k"
    by (metis numeral_Bit0_eq_double power2_eq_square power_mult)
next
  assume "n < 4 ^ k"
  hence "n < 2 ^ (2 * k)"
    by (metis numeral_Bit0_eq_double power2_eq_square power_mult)
  hence "length (bin_of_nat n) \<le> 2 * k" using length_bin_of_nat_le_iff by simp
  thus "Suc (length (bin_of_nat n)) div 2 \<le> k" by simp
qed

lemma bin'_of_nat_div4: "bin'_of_nat (n div 4) = butlast (bin'_of_nat n)"
proof -
  have 1: "n div 4 = n div 2 div 2" by simp
  show ?thesis unfolding 1 apply simp
    unfolding bin_of_nat_div2
    unfolding butlast_rev [symmetric] group_2_butlast_butlast ..
qed

lemma bij_betw_nat_of_bin': "bij_betw nat_of_bin'
                             {w. bin'_wf w \<and> starts_with_True w} {n. n > 0}"
proof -
  have "bin'_wf w \<Longrightarrow> bin'_wf w' \<Longrightarrow> starts_with_True w \<Longrightarrow> starts_with_True w' \<Longrightarrow>
        nat_of_bin' w = nat_of_bin' w' \<Longrightarrow> w = w'" for w w' :: bin'
    by (metis ExtBinary.bin'_nat_bin')
  moreover have "n > 0 \<Longrightarrow> \<exists>w. bin'_wf w \<and> starts_with_True w \<and> nat_of_bin' w = n"
    for n :: nat using ExtBinary.nat_bin'_nat by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) Collect_cong ExtBinary.bij_nat_of_bin' bij_betw_def
        bij_betw_nat_of_bin bij_nat_of_bin)
qed

lemma flatten_butlast_bin': "bin'_wf b \<Longrightarrow>
                             flatten (butlast b) = butlast (butlast (flatten b))"
  by (metis One_nat_def bin'_wf_def butlast_conv_take butlast_power butlast_take
      diff_diff_left diff_le_self flatten_butlast flatten_not_emptyD last_in_set
      numeral_2_eq_2 plus_1_eq_Suc take_Nil)

lemma bin'_wf_takeI: "bin'_wf b \<Longrightarrow> bin'_wf (take n b)"
  apply (induction n)
   apply auto
  by (meson set_all_length_2_wf set_take_subset subset_trans)

lemma bin'_wf_dropI: "bin'_wf b \<Longrightarrow> bin'_wf (drop n b)"
  apply (induction n)
   apply auto
  by (meson dual_order.trans set_all_length_2_wf set_drop_subset)

lemma nat_of_bin'_lt_pow4_length: "bin'_wf b \<Longrightarrow> nat_of_bin' b < 4 ^ (length b)"
  by (metis ExtBinary.nat_of_bin'.simps ExtBinary.nat_of_bin'_max bin'_wf_length
      mult_2 numeral_2_eq_2 numeral_Bit0_eq_double power2_eq_square power_mult)

lemma nat_of_bin'_ge_pow4_length: "bin'_wf b \<Longrightarrow> starts_with_True b \<Longrightarrow>
                                   nat_of_bin' b \<ge> 4 ^ ((length b) - 1)"
  by (metis ExtBinary.bin'_nat_bin' ExtBinary.bin'_of_bin.elims
      Nitpick.size_list_simp(2) Suc_n_not_le_n bin'_of_nat_start_True
      group_2.simps(1) length_bin'_of_nat_le_iff length_tl less_numeral_extra(3)
      nat_of_bin.simps(1) nat_of_bin_via_bin' not_le_imp_less rev.simps(1))

lemma length_bin'_of_nat_dsqrt [simp]: "length (bin'_of_nat (dsqrt n)) =
                                        Suc (length (bin'_of_nat n)) div 2"
  by simp

lemma length_bin'_of_nat_2np1_lower_bound: "length (bin'_of_nat (2 * n + 1)) \<ge>
                                            length (bin'_of_nat n)"
  apply simp
  by (metis ExtBinary.lengths_le Suc_le_mono add_self_div_2 bin_of_nat.simps(2)
      div_le_dividend div_le_mono le_Suc_eq mult_2)

lemma length_bin'_of_nat_2np1_upper_bound: "length (bin'_of_nat (2 * n + 1)) \<le>
                                            Suc (length (bin'_of_nat n))"
  apply simp
  by (metis Suc_div_le_mono Suc_eq_plus1 bin_of_nat.simps(2) bin_of_nat_double_p1
      div2_Suc_Suc length_Cons)

lemma length_bin'_of_nat_mono: "n \<le> m \<Longrightarrow>
                                length (bin'_of_nat n) \<le> length (bin'_of_nat m)"
  apply simp
  using ExtBinary.lengths_le Suc_le_mono div_le_mono by presburger

lemma length_diff_next_square: "length (bin'_of_nat (next_square n - n)) \<le>
                                Suc (Suc (length (bin'_of_nat n)) div 2)"
proof -
  have "length (bin'_of_nat (next_square n - n)) \<le>
        length (bin'_of_nat (2 * dsqrt n + 1))"
    by (fact length_bin'_of_nat_mono [OF next_sq_diff])
  also have "... \<le> Suc (Suc (length (bin'_of_nat n)) div 2)"
    apply (cases "length (bin'_of_nat (2 * dsqrt n + 1)) =
                  length (bin'_of_nat (dsqrt n))")
     apply (erule ssubst)
     apply (subst length_bin'_of_nat_dsqrt)
     apply simp
  proof -
    assume a1: "length (ExtBinary.bin'_of_nat (2 * dsqrt n + 1)) \<noteq>
                length (ExtBinary.bin'_of_nat (dsqrt n))"
    moreover have "dsqrt n \<le> 2 * dsqrt n + 1" by simp
    ultimately have "length (ExtBinary.bin'_of_nat (2 * dsqrt n + 1)) =
                     Suc (length (ExtBinary.bin'_of_nat (dsqrt n)))"
      using length_bin'_of_nat_mono length_bin'_of_nat_2np1_upper_bound
      by (meson le_Suc_eq le_antisym)
    thus "length (ExtBinary.bin'_of_nat (2 * dsqrt n + 1))
          \<le> Suc (Suc (length (ExtBinary.bin'_of_nat n)) div 2)"
      using le_refl length_bin'_of_nat_dsqrt by presburger
  qed
  finally show ?thesis .
qed

lemma nat_of_bin'_gt_with_length_mono: "length xs1 > length xs2 \<Longrightarrow>
                                        starts_with_True xs1 \<Longrightarrow> bin'_wf xs1 \<Longrightarrow>
                                        bin'_wf xs2 \<Longrightarrow>
                                        nat_of_bin' xs1 > nat_of_bin' xs2"
  apply simp
  by (smt (verit, best) ExtBinary.bin'_nat_bin' ExtBinary.bin_of_bin'.elims
      ExtBinary.nat_of_bin'.simps bin'_wf_length dual_order.strict_trans2 leD leI
      length_bin'_of_nat_le_iff length_rev nat_of_bin_dropWhile nat_of_bin_max
      numeral_Bit0_eq_double power2_eq_square power_mult rev_rev_ident)

lemma take_mk_bin': "starts_with_True xs \<Longrightarrow> bin'_wf xs \<Longrightarrow> take (length xs - k) xs =
                     bin'_of_nat (nat_of_bin' xs div 4 ^ k)"
  apply (induction k)
   apply (simp_all del: nat_of_bin'.simps bin'_of_nat.simps)
  by (metis bin'_of_nat_div4 butlast_take diff_commute diff_diff_left diff_le_self
      div_mult2_eq mult.commute plus_1_eq_Suc)

lemma starts_with_flattenD: "starts_with x (flatten xs) \<Longrightarrow> x \<noteq> d \<Longrightarrow> bin'_wf xs \<Longrightarrow>
                             \<exists>y. starts_with [x, y] xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  then show ?case by (auto dest: bin'_wfD)
qed

definition is_bin'_pair :: "bin' \<Rightarrow> bool" where
  "is_bin'_pair w \<equiv> (let p = takeWhile (\<lambda>s. length s = 2) w;
                         s = tl (dropWhile (\<lambda>s. length s = 2) w) in
                          w = p@[[]]@s \<and> bin'_wf s)"

lemma is_bin'_pairI [intro]: "w = p@[[]]@s \<Longrightarrow> bin'_wf p \<Longrightarrow> bin'_wf s \<Longrightarrow> is_bin'_pair w"
  unfolding is_bin'_pair_def Let_def
proof auto
  assume a1: "w = p @ [] # s" and a2: "bin'_wf p" and a3: "bin'_wf s"
  have 1: "takeWhile (\<lambda>s. length s = 2) (p @ [] # s) = p"
    using a2 by (simp add: bin'_wf_def)
  have 2: "tl (dropWhile (\<lambda>s. length s = 2) (p @ [] # s)) = s"
    using a3 by (metis 1 list.sel(3) same_append_eq takeWhile_dropWhile_id)
  show "p @ [] # s = takeWhile (\<lambda>s. length s = 2) (p @ [] # s) @
        [] # tl (dropWhile (\<lambda>s. length s = 2) (p @ [] # s))" unfolding 1 2 ..
  show "bin'_wf (tl (dropWhile (\<lambda>s. length s = 2) (p @ [] # s)))"
    using 2 a3 by argo
qed

lemma is_bin'_pairE [elim]: "is_bin'_pair w \<Longrightarrow>
                             (\<And>p s. w = p@[[]]@s \<Longrightarrow> bin'_wf p \<Longrightarrow> bin'_wf s \<Longrightarrow> P) \<Longrightarrow>
                             P"
  unfolding is_bin'_pair_def Let_def
proof (erule conjE)
  assume a1: "w = takeWhile (\<lambda>s. length s = 2) w @ [[]] @
              tl (dropWhile (\<lambda>s. length s = 2) w)"
     and a2: "\<And>p s. w = p @ [[]] @ s \<Longrightarrow> bin'_wf p \<Longrightarrow> bin'_wf s \<Longrightarrow> P" and
         a3: "bin'_wf (tl (dropWhile (\<lambda>s. length s = 2) w))"
  have 1: "bin'_wf (takeWhile (\<lambda>s. length s = 2) w)" unfolding bin'_wf_def apply auto
    by (meson set_takeWhileD)
  show P apply (rule a2)
      apply (rule a1)
    by fact+
qed

lemma is_bin'_pair_iff: "is_bin'_pair w \<longleftrightarrow> (\<exists>p s. bin'_wf p \<and> bin'_wf s \<and> w = p@[[]]@s)"
  by blast

definition get_bin'_as_pair :: "bin' \<Rightarrow> bin' \<times> bin'" where
  "get_bin'_as_pair w \<equiv>
   (takeWhile (\<lambda>s. length s = 2) w, tl (dropWhile (\<lambda>s. length s = 2) w))"

definition get_bin'_pair :: "bin' \<times> bin' \<Rightarrow> bin'" where
  "get_bin'_pair p \<equiv> (fst p) @ [[]] @ (snd p)"

lemma get_bin'_pair_altdef: "get_bin'_pair (w1, w2) = w1 @ [[]] @ w2"
  unfolding get_bin'_pair_def by simp

lemma get_bin'_pair_as_pair [simp]: "bin'_wf (fst p) \<Longrightarrow>
                                     get_bin'_as_pair (get_bin'_pair p) = p"
  unfolding get_bin'_as_pair_def get_bin'_pair_def by (auto simp add: bin'_wf_def)

lemma get_bin'_as_pair_pair [simp]: "is_bin'_pair w \<Longrightarrow>
                                     get_bin'_pair (get_bin'_as_pair w) = w"
  unfolding get_bin'_pair_def get_bin'_as_pair_def apply auto
  using is_bin'_pair_def by fastforce

lemma get_bin'_as_pair_bij: "bij_betw get_bin'_as_pair {w. is_bin'_pair w}
                             {(w1, w2). bin'_wf w1 \<and> bin'_wf w2}"
  unfolding bij_betw_def apply auto
  using get_bin'_as_pair_pair apply (metis inj_on_inverseI mem_Collect_eq)
  using bin'_wf_def get_bin'_as_pair_def apply fastforce
   apply (metis get_bin'_as_pair_def is_bin'_pair_def snd_conv)
  unfolding image_def by (metis (mono_tags, lifting) fst_conv get_bin'_pair_altdef
      get_bin'_pair_as_pair is_bin'_pairI mem_Collect_eq)

lemma get_bin'_pair_bij: "bij_betw get_bin'_pair {(w1, w2). bin'_wf w1 \<and> bin'_wf w2}
                          {w. is_bin'_pair w}"
  by (smt (verit, best) bij_betw_iff_bijections get_bin'_as_pair_bij get_bin'_as_pair_pair
      mem_Collect_eq)

lemma get_bin'_as_pair_valid1: "is_bin'_pair w \<Longrightarrow> bin'_wf (fst (get_bin'_as_pair w))"
  using bin'_wf_def get_bin'_as_pair_def by auto

lemma get_bin'_as_pair_valid2: "is_bin'_pair w \<Longrightarrow> bin'_wf (snd (get_bin'_as_pair w))"
  using bin'_wf_def get_bin'_as_pair_def by auto

lemma get_bin'_pair_valid: "bin'_wf (fst p) \<Longrightarrow> bin'_wf (snd p) \<Longrightarrow>
                            is_bin'_pair (get_bin'_pair p)"
  using get_bin'_pair_def by blast
end