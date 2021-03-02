theory ex3_4_no_auto
  imports Main HOL.HOL
begin 

inductive star :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  isingle: "r x y \<Longrightarrow> iter r (Suc 0) x y" |
  istep: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"


(* yes, these use auto, but h4 and the main lemma are more interesting anyways *)
lemma h0: "r x y \<Longrightarrow> star r x y"
  by (auto simp add: refl step)

lemma h2: "iter r n x y \<Longrightarrow> star r x y"
  by (induction arbitrary: n rule: iter.induct)
    (auto simp add: h0 refl step)

lemma h3: "r x x \<Longrightarrow> iter r (Suc n) x x"
  by (induction n)
    (auto simp add: h0 h2 isingle istep)


lemma h4:
  fixes r x z
  assumes "star r x z" and "x \<noteq> z"
  obtains y where "r x y" "star r y z"
  using assms
proof (induction rule: star.induct)
  case (refl x)
  (*
  find_theorems "?x = ?x"
  find_theorems "(\<not>True) = False"
  find_theorems "(\<not>?a) = (\<not>?b)"
  find_theorems "(\<not>?a) \<Longrightarrow> ?a \<Longrightarrow> _"
  find_theorems "False \<Longrightarrow> _"
  thm HOL.refl[of x]
  thm Not_eq_iff[of "x = x" True]
  thm not_True_eq_False
  thm notE[of "x = x" False]
  from \<open>x \<noteq> x\<close> HOL.refl[of x] have False by (rule notE)
  *)
  from HOL.refl have "x = x" .
  with \<open>x \<noteq> x\<close> have False by (rule notE)
  thus ?case by (rule FalseE)
  (*
   * note that "have False" could be replaced with "show ?case", 
   * as anything could already be derived using notE.
   * the explicit detour over "False" is included here for demonstrating the standard pattern.
   * 
   * also note that the following would not work as the order of input facts matters for "rule":
   *
   * case (refl x)
   * with HOL.refl[of x] have False by (rule notE)
   * 
   * correct order:
   * from \<open>x \<noteq> x\<close> HOL.refl[of x] have False by (rule notE)
   *)
next
  case (step x y z)
  from \<open>r x y\<close> \<open>star r y z\<close> show ?case
    by (rule \<open>r x y \<Longrightarrow> star r y z \<Longrightarrow> ?case\<close>)
qed

theorem 
  fixes r x z
  assumes "star r x z" and "x \<noteq> z"
  shows "\<exists>n. iter r n x z"
  using assms
proof (induction rule: star.induct)
  case (refl x)
  from \<open>x \<noteq> x\<close> HOL.refl[of x] have False by (rule notE)
  then show ?case by simp
next
  case (step x y z)

  thm step.IH

  show ?case
  proof (cases "y = z")
    case True
    from \<open>r x y\<close> have "iter r (Suc 0) x y" by (rule isingle)
    then have "iter r (Suc 0) x z" unfolding \<open>y = z\<close> . 
        (* after unfolding, the goal and facts are equal, therefore "." (== "by this") will solve it *)

    thm exI
    then show ?thesis by (rule exI)
  next
    case False
    thm step (* "step" contains the "induction hypotheses" *)
    with step(3) obtain n where "iter r n y z" by auto (* obtain(s) is somewhat complicated *)
    with \<open>r x y\<close> have "iter r (Suc (n)) x z" by (rule istep)
    then show ?thesis by (rule exI)
  qed
qed

(* 
 * same lemma using obtains.
 * this was a lot harder to prove manually, since the IH is more complicated
 * (as the internal reasoning does not have an existential quantifier)
 *)
theorem 
  fixes r x z
  assumes "star r x z" and "x \<noteq> z"
  obtains n where "iter r n x z"
  using assms
proof (induction rule: star.induct)
  case (refl x)
  then show ?case by simp
next
  case (step x y z)

  (* now the induction facts are in context. see isar-ref.pdf ch. 6.5.2 Proof methods *)
  print_cases
  thm step.hyps  (* hypotheses assumptions from the induction case *)
  thm step.IH    (* the induction hypothesis *)
  thm step.prems (* premises: outer assumptions *)
  thm step       (* set of the above facts *)
    

  show ?case
  proof (cases "y = z")
    case True
      (* interestingly, "try" is not able to solve this rather trivial goal *)
    from \<open>r x y\<close> have "iter r (Suc 0) x z" unfolding \<open>y = z\<close> by (rule isingle)
    then show ?thesis by (rule step.prems(1))
  next
    case False
    from step.hyps(1) have "\<And>n. iter r n y z \<Longrightarrow> iter r (Suc n) x z" by (rule istep)
    then have "\<And>n. iter r n y z \<Longrightarrow> thesis" by (rule step.prems(1)) (* finding this took more trial and error than expected *)
    then have "y \<noteq> z \<Longrightarrow> thesis" by (rule step.IH)
    from this and \<open>y \<noteq> z\<close> show ?thesis .
    (*
     * the following are equivalent:
     *   from a show b by (rule c)
     * and
     *   from c and a show b .
     *
     * pattern: from "a \<Longrightarrow> b" and "a" show "b" .
     *
     * the following are also equivalent ("with" puts facts at the beginning of the list):
     *   have a
     *   with b have c
     * and
     *   from b and a have c
     *)
  qed
qed

end