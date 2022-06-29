theory Formal_Languages
  imports Main Intro_Dest_Elim.IHOL_IDE
begin

datatype ('s) lang = Lang (alphabet: "'s set") (words: "'s list set")

definition valid_lang :: "'s lang \<Rightarrow> bool"
  where "valid_lang L \<equiv> \<forall>w\<in>words L. set w \<subseteq> alphabet L"

lemma valid_langI[intro]: "(\<And>w. w\<in>words L \<Longrightarrow> set w \<subseteq> alphabet L) \<Longrightarrow> valid_lang L"
  unfolding valid_lang_def by blast
lemma valid_langD[dest]: "valid_lang L \<Longrightarrow> w \<in> words L \<Longrightarrow> set w \<subseteq> alphabet L"
  unfolding valid_lang_def by blast


definition lang_from_pred :: "'s set \<Rightarrow> ('s list \<Rightarrow> bool) \<Rightarrow> 's lang"
  where "lang_from_pred \<Sigma> P = Lang \<Sigma> {w. set w \<subseteq> \<Sigma> \<and> P w}"

syntax "_lang_from_pred" :: "pttrn \<Rightarrow> 's set \<Rightarrow> bool \<Rightarrow> 's lang" ("(3{(_/\<in>_*.)/ _})")
translations "{w\<in>\<Sigma>*. P}" \<rightleftharpoons> "CONST lang_from_pred \<Sigma> (\<lambda>w. P)"

lemma valid_lang_from_pred[simp, intro]: "valid_lang {w\<in>\<Sigma>*. P}"
  unfolding valid_lang_def lang_from_pred_def by simp


definition member_lang :: "'s list \<Rightarrow> 's lang \<Rightarrow> bool" (infix "\<in>\<^sub>L" 50)
  where "w \<in>\<^sub>L L \<equiv> set w \<subseteq> alphabet L \<and> w \<in> words L"

lemma valid_lang_member[simp, dest]: "valid_lang L \<Longrightarrow> w \<in>\<^sub>L L \<longleftrightarrow> w \<in> words L"
  unfolding member_lang_def by blast


end
