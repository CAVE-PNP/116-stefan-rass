theory Formal_Languages
  imports Main "Supplementary/Lists" Intro_Dest_Elim.IHOL_IDE
begin

datatype ('s) lang = Lang (alphabet: "'s set") (words: "'s list set")

definition valid_lang :: "'s lang \<Rightarrow> bool"
  where "valid_lang L \<equiv> words L \<subseteq> (alphabet L)*"

lemma valid_langI[intro]: "words L \<subseteq> (alphabet L)* \<Longrightarrow> valid_lang L"
  unfolding valid_lang_def by blast
lemma valid_langD[dest]: "valid_lang L \<Longrightarrow> w \<in> words L \<Longrightarrow> w \<in> (alphabet L)*"
  unfolding valid_lang_def by blast


definition member_lang :: "'s list \<Rightarrow> 's lang \<Rightarrow> bool" (infix "\<in>\<^sub>L" 50)
  where "w \<in>\<^sub>L L \<equiv> w \<in> (alphabet L)* \<and> w \<in> words L"

abbreviation not_member_lang :: "'s list \<Rightarrow> 's lang \<Rightarrow> bool" (infix "\<notin>\<^sub>L" 50)
  where "w \<notin>\<^sub>L L \<equiv> \<not> (w \<in>\<^sub>L L)"

lemma valid_lang_member[simp, dest]: "valid_lang L \<Longrightarrow> w \<in>\<^sub>L L \<longleftrightarrow> w \<in> words L"
  unfolding member_lang_def by blast


lemma valid_lang_listsI[simp, intro]: "valid_lang (Lang \<Sigma> {w\<in>\<Sigma>*. P})"
  unfolding valid_lang_def by auto

end
