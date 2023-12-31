theory Formal_Languages
  imports Main "Supplementary/Lists" Intro_Dest_Elim.IHOL_IDE
begin

datatype ('s) lang = Lang (alphabet: "'s set") (gen_pred: "'s list \<Rightarrow> bool")

abbreviation "ULang \<equiv> Lang UNIV"

definition words :: "'s lang \<Rightarrow> 's list set"
  where "words L = {w\<in>(alphabet L)*. gen_pred L w}"

lemma words_simp: "words (Lang \<Sigma> P) = {w\<in>\<Sigma>*. P w}" by (simp add: words_def)


abbreviation member_lang :: "'s list \<Rightarrow> 's lang \<Rightarrow> bool" (infix "\<in>\<^sub>L" 50)
  where "w \<in>\<^sub>L L \<equiv> w \<in> words L"

abbreviation not_member_lang :: "'s list \<Rightarrow> 's lang \<Rightarrow> bool" (infix "\<notin>\<^sub>L" 50)
  where "w \<notin>\<^sub>L L \<equiv> \<not> (w \<in>\<^sub>L L)"

lemma member_lang_iff: "w \<in>\<^sub>L L \<longleftrightarrow> w\<in>(alphabet L)* \<and> gen_pred L w"
  unfolding words_def by blast

corollary member_lang_iff'[simp]: "w \<in>\<^sub>L Lang \<Sigma> P \<longleftrightarrow> w\<in>\<Sigma>* \<and> P w" by (simp add: member_lang_iff)
corollary member_lang_UNIV[simp]: "w \<in>\<^sub>L Lang UNIV P \<longleftrightarrow> P w" by simp

mk_ide member_lang_iff |intro member_langI[intro]| |dest member_langD[dest]| |elim member_langE[elim]|


text\<open>Defining complement and intersection analogous to sets.
  See \<^const>\<open>inter\<close> and @{thm uminus_set_def inf_set_def}.\<close>

instantiation lang :: (type) uminus begin
definition "- L \<equiv> Lang (alphabet L) (- gen_pred L)" instance .. end

instantiation lang :: (type) inf begin
definition "inf_lang A B \<equiv> Lang (alphabet A \<inter> alphabet B) (\<lambda>w. gen_pred A w \<and> gen_pred B w)"
instance .. end

abbreviation inter_lang :: "'s lang \<Rightarrow> 's lang \<Rightarrow> 's lang" (infixl "\<inter>\<^sub>L" 70)
  where "inter_lang \<equiv> inf"

lemma inf_lang_altdef: "Lang \<Sigma>1 P1 \<inter>\<^sub>L Lang \<Sigma>2 P2 = Lang (inf \<Sigma>1 \<Sigma>2) (inf P1 P2)"
  unfolding inf_lang_def by auto

lemma inter_lang_commute: "L\<^sub>1 \<inter>\<^sub>L L\<^sub>2 = L\<^sub>2 \<inter>\<^sub>L L\<^sub>1" unfolding inf_lang_def by blast

lemma inter_lang_words[simp]: "words (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2) = words L\<^sub>1 \<inter> words L\<^sub>2"
  unfolding inf_lang_def by (induction L\<^sub>1, induction L\<^sub>2) auto

lemma inter_lang_member[iff]: "w \<in>\<^sub>L (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2) \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>1 \<and> w \<in>\<^sub>L L\<^sub>2" by simp

end
