theory Formal_Languages
  imports Main "Supplementary/Lists" "Intro_Dest_Elim.IHOL_IDE" TM Binary
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

abbreviation Blall :: "('s list \<Rightarrow> bool) \<Rightarrow> 's lang \<Rightarrow> bool" where
  "Blall P L \<equiv> \<forall>x. x \<in>\<^sub>L L \<longrightarrow> P x"

syntax
  "_Blall" :: "pttrn \<Rightarrow> 's lang \<Rightarrow> ('s list \<Rightarrow> bool) \<Rightarrow> 's lang" ("(\<forall>_\<in>\<^sub>L_./ _)" [0, 0, 20] 20)
translations
  "\<forall>x\<in>\<^sub>LA. P" \<rightleftharpoons> "CONST Blall (\<lambda>x. P) A"

abbreviation Blex :: "('s list \<Rightarrow> bool) \<Rightarrow> 's lang \<Rightarrow> bool" where
  "Blex P L \<equiv> \<exists>x. x \<in>\<^sub>L L \<and> P x"

syntax
  "_Blex" :: "pttrn \<Rightarrow> 's lang \<Rightarrow> ('s list \<Rightarrow> bool) \<Rightarrow> 's lang" ("(\<exists>_\<in>\<^sub>L_./ _)" [0, 0, 20] 20)
translations
  "\<exists>x\<in>\<^sub>LA. P" \<rightleftharpoons> "CONST Blex (\<lambda>x. P) A"

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

lemma inter_lang_alphabet [simp]: "alphabet (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2) = (alphabet L\<^sub>1) \<inter> (alphabet L\<^sub>2)"
  unfolding inf_lang_def by simp

lemma inter_lang_alphabet_words [iff]:
  "x \<in> (alphabet (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2))* \<longleftrightarrow> x \<in> (alphabet L\<^sub>1)* \<and> x \<in> (alphabet L\<^sub>2)*"
  unfolding inf_lang_def by simp

lemma inter_lang_words[simp]: "words (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2) = words L\<^sub>1 \<inter> words L\<^sub>2"
  unfolding inf_lang_def by (induction L\<^sub>1, induction L\<^sub>2) auto

lemma inter_lang_member[iff]: "w \<in>\<^sub>L (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2) \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>1 \<and> w \<in>\<^sub>L L\<^sub>2" by simp

lemma compl2_lang [simp]: "-(-L) = (L::'a lang)" by (simp add: uminus_lang_def)

lemma compl_alphabet: "alphabet (-L) = alphabet L" by (simp add: uminus_lang_def)

lemma compl_word: "w\<in>(alphabet L)* \<Longrightarrow> w\<in>\<^sub>LL \<longleftrightarrow> w\<notin>\<^sub>L(-L)"
  by (simp add: member_lang_iff uminus_lang_def)

fun ext_lang :: "'s lang \<Rightarrow> 's list lang" where
  "ext_lang (Lang ss p) = Lang (symbols_to_extensible ss) (\<lambda>w. p (map hd w))"

lemma ext_lang_gen_pred: "gen_pred (ext_lang L) (map (\<lambda>x. [x]) w) = gen_pred L w"
  apply (induction L)
  apply (induction w)
  by simp_all

lemma ext_lang_length: "\<And>s. s\<in>alphabet (ext_lang L) \<Longrightarrow> length s = 1"
  by (induction L) simp

lemma ext_lang_singleton: "\<And>s. s\<in>alphabet (ext_lang L) \<Longrightarrow> \<exists>x. s=[x]"
  apply (drule ext_lang_length)
  by (metis One_nat_def length_1_ex_iff)

lemma ext_lang_eq: "(map (\<lambda>x. [x]) w) \<in>\<^sub>L (ext_lang L) \<longleftrightarrow> w \<in>\<^sub>L L"
proof
  assume "w \<in>\<^sub>L L"
  hence "w \<in> words L" by simp
  hence "map (\<lambda>x. [x]) w \<in> words (ext_lang L)"
  proof
    assume "w \<in> (alphabet L)*" and "gen_pred L w"
    hence "map (\<lambda>x. [x]) w \<in> (alphabet (ext_lang L))*" by (induction L) auto
    moreover have "gen_pred (ext_lang L) (map (\<lambda>x. [x]) w)"
      by (simp add: \<open>gen_pred L w\<close> ext_lang_gen_pred)
    ultimately have "map (\<lambda>x. [x]) w \<in> words (ext_lang L)" by (induction L) simp
    thus "map (\<lambda>x. [x]) w \<in>\<^sub>L ext_lang L" by simp
  qed
  thus "map (\<lambda>x. [x]) w \<in>\<^sub>L ext_lang L" by simp
next
  assume "map (\<lambda>x. [x]) w \<in>\<^sub>L ext_lang L"
  hence "map (\<lambda>x. [x]) w \<in> words (ext_lang L)" by simp
  hence "w \<in> words L" by (induction L, induction w, auto simp add: map_idI)
  thus "w \<in>\<^sub>L L" by simp
qed

lemma ext_lang_alphabet_eq: "[s]\<in>alphabet (ext_lang L) \<longleftrightarrow> s\<in>alphabet L"
  by (induction L) simp

lemma ext_lang_alphabet_eq2: "length s = 1 \<Longrightarrow>
                              s\<in>alphabet (ext_lang L) \<longleftrightarrow> hd s\<in>alphabet L"
  by (metis One_nat_def ext_lang_alphabet_eq length_1_hd_iff)

lemma alphabet_symbols_subset [iff]:
  "alphabet (ext_lang L) \<subseteq> TM.symbols (Abs_TM (tm_to_ext_tm M)) \<longleftrightarrow>
  alphabet L \<subseteq> TM.symbols M"
  apply (rule sym)
  using ext_lang_alphabet_eq ext_lang_singleton ext_tm_valid valid_tm_symbols
  by fastforce

lemma empty_alphabet_only_empty_word: "alphabet L = {} \<Longrightarrow> words L \<subseteq> {[]}"
  by auto

definition option_lang :: "'s lang \<Rightarrow> 's option lang" where
  "option_lang L \<equiv> Lang (options (alphabet L)) (\<lambda>w. None \<notin> set w \<and> map the w \<in>\<^sub>L L)"

lemma option_lang_iff: "map Some w \<in>\<^sub>L option_lang L \<longleftrightarrow> w \<in>\<^sub>L L"
  unfolding option_lang_def by auto

lemma Lang_for_pred: obtains L :: "'a lang" where
  "alphabet L = UNIV" and "\<And>w. w \<in>\<^sub>L L \<longleftrightarrow> P w"
proof -
  assume a1: "\<And>L. alphabet L = UNIV \<Longrightarrow> (\<And>w. (w \<in>\<^sub>L L) = P w) \<Longrightarrow> thesis"
  define L :: "'a lang" where "L \<equiv> Lang UNIV P"
  have 1: "\<And>w. w \<in>\<^sub>L L \<longleftrightarrow> P w" unfolding words_def using L_def by simp
  have 2: "alphabet L = UNIV" using L_def by simp
  show thesis apply (rule a1)
     apply (rule 2)
    by (rule 1)
qed
end
