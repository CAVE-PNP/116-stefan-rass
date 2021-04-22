theory complexity
  imports Main "HOL-Library.BigO"
begin

(*a locale to capture our intuition of Turing machines*)
locale TM =
  fixes \<Gamma>\<^sub>i\<^sub>n :: "'a set" (*input alphabet*)
  fixes k :: nat (*tape count*)
  fixes time :: "'a list \<Rightarrow> nat"
  fixes space :: "'a list \<Rightarrow> nat"

  assumes input_alphabet_finite: "finite \<Gamma>\<^sub>i\<^sub>n"

  (*in one step only k cells can be visited*)
  assumes "space x \<le> k * time x"
begin
 
end

end