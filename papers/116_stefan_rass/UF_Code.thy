theory UF_Code
  imports Universal_Turing_Machine.UF "HOL-Computational_Algebra.Primes"
begin

lemma code_Nil: "code [] = 1" unfolding code.simps Let_def godel_code_eq_1 modify_tprog.simps ..
lemma code_gt_0: "code M > 0" unfolding code.simps Let_def using godel_code_great .

lemma godel_code'_mono2: "godel_code' ps n \<le> godel_code' ps (Suc n)"
proof (induction n rule: godel_code'.induct)
  case (1 n)
  thus ?case unfolding godel_code'.simps ..
next
  case (2 x xs n)
  from Pi_inc[of n] have "Pi n ^ x \<le> Pi (Suc n) ^ x" by (intro power_mono) simp_all
  find_theorems "_ ^ _ < _ ^ _"
  then show ?case unfolding godel_code'.simps using "2.IH" by (rule mult_le_mono)
qed

corollary Pi_pow_gr_1: "Pi n ^ p \<ge> 1"
  using one_le_power[of "Pi n"] less_imp_le Pi_gr_1 unfolding One_nat_def .

lemma godel_code'_mono1: "godel_code' ps n \<le> godel_code' (p#ps) n"
proof -
  have "(Suc 0) * godel_code' ps n \<le> Pi n ^ p * godel_code' ps (Suc n)"
    using Pi_pow_gr_1 godel_code'_mono2 unfolding One_nat_def by (rule mult_le_mono)
  then show ?thesis unfolding godel_code'.simps by simp
qed

lemma code_Cons: "code M < code (i # M)"
proof -
  obtain a n where i: "i = (a, n)" by (rule prod.exhaust)
  let ?g = godel_code' and ?M = "modify_tprog M" and ?M' = "modify_tprog ((a, n) # M)"
  have a: "2 ^ length ?M < (2::nat) ^ length ?M'" by (subst power_strict_increasing) simp_all

  have "?g ?M (Suc 0) \<le> ?g ?M (Suc (Suc (Suc 0)))" using godel_code'_mono2 le_trans by blast
  also have "... \<le> Pi (Suc 0) ^ action_map a * Pi (Suc (Suc 0)) ^ n * ..." using Pi_pow_gr_1 by simp
  finally have b: "?g ?M (Suc 0) \<le> ?g ?M' (Suc 0)"
    unfolding modify_tprog.simps godel_code'.simps mult.assoc .

  have "code M = 2 ^ length ?M * ?g ?M (Suc 0)" unfolding code.simps godel_code.simps Let_def ..
  also from a have "... < 2 ^ length ?M' * ?g ?M (Suc 0)" using godel_code'_nonzero by (rule mult_less_mono1)
  also from b have "... \<le> 2 ^ length ?M' * ?g ?M' (Suc 0)" by (rule mult_le_mono2)
  also have "... = code ((a, n) # M)" unfolding code.simps godel_code.simps Let_def ..
  finally show ?thesis by (unfold i)
qed

lemma code_gt_1: "M \<noteq> [] \<Longrightarrow> code M > 1"
proof (induction M rule: list_nonempty_induct)
  case (single x)
  have "1 = code []" using code_Nil ..
  also have "... < code [x]" by (rule code_Cons)
  finally show ?case .
next
  case (cons x xs)
  note \<open>1 < code xs\<close>
  also have "code xs < code (x # xs)" by (rule code_Cons)
  finally show ?case .
qed

lemma code_1_iff: "code M = 1 \<longleftrightarrow> M = []"
proof (intro iffI)
  assume "code M = 1"
  then show "M = []" using code_gt_1 by fastforce
next
  assume "M = []"
  then show "code M = 1" using code_Nil by blast
qed

lemma action_map_inj: "inj action_map"
proof (intro injI)
  fix x y
  assume "action_map x = action_map y"
  then show "x=y" by (cases x; cases y) simp_all
qed

fun unroll :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a\<times>'b) list \<Rightarrow> 'c list" where
  "unroll _ _ [] = []"
| "unroll f g ((a,b)#t) = f a#g b#unroll f g t"

lemma unroll_inj:
  fixes f::"'a \<Rightarrow> 'c" and g::"'b \<Rightarrow> 'c"
  assumes "inj f" "inj g"
  shows "inj (unroll f g)"
proof (intro injI)
  let ?F = "unroll f g"
  fix xs ys assume "?F xs = ?F ys"
  then show "xs = ys" proof (induction xs arbitrary: ys)
    case Nil
    then have "?F ys = []" by simp
    then show ?case using unroll.elims list.distinct(1) by blast
  next
    case (Cons ab xs)
    define a b where "a \<equiv> fst ab" and "b \<equiv> snd ab"
    have ab_def: "ab = (a,b)" unfolding a_def b_def by simp
    with Cons.prems have "\<exists>ys' a' b'. ys = (a',b')#ys' \<and> (?F ys' = ?F xs) \<and> f a' = f a \<and>  g b' = g b"
        using list.discI list.sel unroll.elims case_prod_conv
        by (smt (verit, del_insts) unroll.simps(2))
    then obtain ys' a' b' where "ys = (a',b')#ys'" and "?F ys' = ?F xs" and "f a' = f a" and "g b' = g b"
      by blast
    note * = this
    with assms have "(a,b) = (a',b')" unfolding inj_def by simp
    with Cons.IH * show ?case unfolding ab_def by force
  qed
qed

corollary modify_tprog_unroll_def: "modify_tprog = unroll action_map (\<lambda>b. b)"
proof (* why is this so hard? *)
  fix xs
  note unroll_simps = unroll.simps[of action_map "\<lambda>b. b"]
  show "modify_tprog xs = unroll action_map (\<lambda>b. b) xs" proof (induction xs)
    case (Cons a xs)
    then show ?case using unroll_simps(2) modify_tprog.simps(2)
      by (smt (verit, best) list.discI list.sel(1) unroll.elims)
  qed simp
qed

corollary modify_tprog_inj: "inj modify_tprog"
  unfolding modify_tprog_unroll_def
  using unroll_inj[of action_map "\<lambda>x. x"] action_map_inj by simp

(* godel_code :: nat list \<Rightarrow> nat
encodes nat list in prime powers
the length of the list is encoded in the power of 2

godel_code [42, 1, 9] = 2^3 * 3^42 * 5^1 * 7^9
*)

lemma godel_code_altdef: "godel_code xs = godel_code' (length xs#xs) 0"
  using Pi.simps(1) godel_code'.simps(2) godel_code.simps by presburger

lemma Prime_prime_eq: "UF.Prime n \<longleftrightarrow> Factorial_Ring.prime n"
  unfolding UF.Prime.simps(1) prime_nat_iff dvd_def
  by (metis Suc_lessI dvd_mult_cancel2 less_irrefl less_numeral_extra(1) less_trans mult.right_neutral n_less_m_mult_n n_less_n_mult_m nat_0_less_mult_iff nat_dvd_not_less)

lemma godel_code_prime_factorization_len:
  shows "count (prime_factorization(godel_code xs)) 2 = length xs"
  sorry

lemma godel_code_prime_factorization:
  fixes i::nat
  assumes "i < length xs"
  shows "count (prime_factorization(godel_code xs)) (Pi (i+1)) = xs ! i"
  sorry

lemma godel_inj: "inj godel_code" (is "inj ?gn")
proof (intro injI)
  fix xs ys
  assume assm: "?gn xs = ?gn ys"
  define "Fx" "Fy"
    where "Fx \<equiv> prime_factorization (?gn xs)" and "Fy = prime_factorization (?gn ys)"
    note F_def = this
  show "xs = ys" proof (subst list_eq_iff_nth_eq, safe)
    from godel_code_prime_factorization_len
    show len_eq: "length xs = length ys" using assm F_def by metis
  
    fix i
    assume "i < length xs"
    moreover have "i < length ys" using calculation len_eq by simp

    ultimately show "xs ! i = ys ! i"
      using godel_code_prime_factorization assm by metis
  qed
qed

lemma code_inj: "inj code"
  using modify_tprog_inj godel_inj
  and code.simps inj_compose[of godel_code modify_tprog]
  by (metis comp_apply inj_on_cong)
 
end
