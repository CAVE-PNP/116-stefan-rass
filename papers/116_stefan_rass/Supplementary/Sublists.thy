theory Sublists
  imports "HOL-Library.Sublist"
begin

lemma suffix_drop_le:
  assumes "a \<ge> b"
  shows "suffix (drop a xs) (drop b xs)"
proof -
  from \<open>a \<ge> b\<close> have *: "drop a xs = drop (a - b) (drop b xs)" by simp
  show "suffix (drop a xs) (drop b xs)" unfolding * by (rule suffix_drop)
qed

lemma suffix_drop_iff[iff]: "suffix sfx xs \<longleftrightarrow> drop (length xs - length sfx) xs = sfx"
proof
  assume "suffix sfx xs"
  then obtain ps where ps: "xs = ps @ sfx" ..
  show "drop (length xs - length sfx) xs = sfx" unfolding ps by force
next
  assume drop_eq: "drop (length xs - length sfx) xs = sfx"
  have "suffix (drop (length xs - length sfx) xs) xs" by (rule suffix_drop)
  then show "suffix sfx xs" unfolding drop_eq .
qed


lemma suffix_length_unique: "suffix ps xs \<Longrightarrow> suffix qs xs \<Longrightarrow> length ps = length qs \<Longrightarrow> ps = qs"
  by (subst suffix_order.eq_iff, intro conjI; subst suffix_length_suffix) simp_all

end
