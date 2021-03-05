theory ex3_4
  imports Main HOL.HOL
begin


inductive star :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  isingle: "r x y \<Longrightarrow> iter r (Suc 0) x y" |
  istep: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"


lemma h0: "r x y \<Longrightarrow> star r x y"
  by (auto simp add: refl step)

lemma h2: "iter r n x y \<Longrightarrow> star r x y"
  by (induction arbitrary: n rule: iter.induct)
    (auto simp add: h0 refl step)

lemma h3: "r x x \<Longrightarrow> iter r (Suc n) x x"
  by (induction n)
    (auto simp add: h0 h2 isingle istep)

(* early drafts: the proofs of the following two lemmas are incorrect *)

lemma h4: "star r x z \<Longrightarrow> (x = z \<or> (r x y \<and> star r y z))"
  apply (induction rule: star.induct)
   apply (auto simp add: refl step h0 h2 h3)
  nitpick
  oops

lemma "star r x y \<Longrightarrow> x \<noteq> y \<Longrightarrow> iter r (Suc n) x y"
  apply (induction n)
   apply (auto simp add: isingle istep h0 h2 h3)
  nitpick
  oops

(* 
 * working versions.
 * note that these inline proofs are in fact derived from the explicit proof,
 * with the help of sledgehammer, as implied by the use of "metis"
 *)

lemma h4:
  fixes r x z
  assumes "star r x z" and "x \<noteq> z"
  obtains y where "r x y" "star r y z"
  using assms by (induction rule: star.induct; simp)

theorem
  fixes r x z
  assumes "star r x z" and "x \<noteq> z"
  shows "\<exists>n. iter r n x z"
  using assms
  by (induction rule: star.induct, simp, metis isingle istep)

(* different problem formulation using "obtains" (equivalent in theory, somewhat more explicit) *)
theorem
  fixes r x z
  assumes "star r x z" and "x \<noteq> z"
  obtains n where "iter r n x z"
  using assms
  by (induction rule: star.induct, simp, metis isingle istep)

end