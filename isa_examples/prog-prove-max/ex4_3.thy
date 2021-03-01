theory ex4_3
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"


(* TODO: find a way to inline this proof *)
lemma "\<not> ev(Suc 0)"
proof
  assume "ev(Suc 0)" then show False by cases
qed

lemma
  fixes n::nat
  assumes "ev(Suc (Suc n))" 
  shows "ev n"
proof -
  show "ev n" using assms by cases
qed

lemma
  fixes n::nat
  assumes "ev(Suc (Suc n))" 
  shows "ev n"
  using assms by cases

(*
lemma
  fixes n::nat
  assumes "ev(Suc (Suc n))" 
  shows "ev n"
proof -
  from assms show "ev n"
  proof cases
qed
*)

lemma
  fixes n::nat
  assumes "ev(Suc (Suc n))" 
  shows "ev n"
proof (rule ccontr)
  assume "\<not> ev n"
  thm ev.cases
  hence "\<not> ev (Suc (Suc n))"
    using ev.cases by auto (* from sledgehammer *)
  thus False using assms by metis
qed

end