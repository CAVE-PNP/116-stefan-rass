theory Formal_Languages
  imports Main "Supplementary/Lists" Intro_Dest_Elim.IHOL_IDE
begin

datatype ('s) lang = Lang (alphabet: "'s set") (gen_pred: "'s list \<Rightarrow> bool")

definition words :: "'s lang \<Rightarrow> 's list set"
  where "words L = {w\<in>(alphabet L)*. gen_pred L w}"


abbreviation member_lang :: "'s list \<Rightarrow> 's lang \<Rightarrow> bool" (infix "\<in>\<^sub>L" 50)
  where "w \<in>\<^sub>L L \<equiv> w \<in> words L"

abbreviation not_member_lang :: "'s list \<Rightarrow> 's lang \<Rightarrow> bool" (infix "\<notin>\<^sub>L" 50)
  where "w \<notin>\<^sub>L L \<equiv> \<not> (w \<in>\<^sub>L L)"

lemma member_lang_iff[iff]: "w \<in>\<^sub>L L \<longleftrightarrow> w\<in>(alphabet L)* \<and> gen_pred L w"
  unfolding words_def by blast


end
