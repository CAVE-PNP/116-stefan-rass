theory complexity
  imports Main gn "Universal_Turing_Machine.UTM"
begin

subsection\<open>Termination\<close>

text\<open>The tape size can not use the universal function \<^term>\<open>size\<close>, since for any pair \<^term>\<open>p = (a, b)\<close>, \<^term>\<open>size p = 1\<close>.\<close>
fun tape_size :: "tape \<Rightarrow> nat" \<comment> \<open>using \<open>fun\<close> since \<open>definition\<close> does not recognize patterns like \<^term>\<open>(l, r)\<close>\<close>
  where "tape_size (l, r) = length l + length r"

text\<open>The time restriction predicate is similar to \<^term>\<open>Hoare_halt\<close>, but includes a maximum number of steps.\<close>
definition time_restricted :: "(nat \<Rightarrow> nat) \<Rightarrow> tprog0 \<Rightarrow> bool"
  where "time_restricted T p \<equiv> \<forall>tp. \<exists>n.
            n \<le> T (tape_size tp)
          \<and> is_final (steps0 (1, tp) p n)"

(* TODO (?) notation: \<open>p terminates_in_time T\<close> *)

text\<open>\<open>time\<^sub>M(x)\<close> is the number of steps until the computation of \<open>M\<close> halts on input \<open>x\<close>\<close>
definition time :: "tprog0 \<Rightarrow> tape \<Rightarrow> nat option"
  where "time p tp = (
    if \<exists>n. is_final (steps0 (1, tp) p n)
      then Some (LEAST n. is_final (steps0 (1, tp) p n))
      else None
    )"

lemma least_p:
  fixes P and n::nat
  assumes "n = (LEAST m. P n)"
  shows "P n"
sorry

lemma "time_restricted T p \<longleftrightarrow> (\<forall>tp. the (time p tp) \<le> T (tape_size tp))"
proof (intro iffI allI)
  fix tp
  assume "time_restricted T p"
  then have e: "\<exists>n. n \<le> T (tape_size tp) \<and> is_final (steps0 (1, tp) p n)" unfolding time_restricted_def ..
  then obtain n where "n \<le> T (tape_size tp)" and nH: "is_final (steps0 (1, tp) p n)" by blast

  have "the (time p tp) = (LEAST n. is_final (steps0 (1, tp) p n))" unfolding time_def using e by auto
  also have "... \<le> n" using Least_le nH .
  also note \<open>n \<le> T (tape_size tp)\<close>
  finally show "the (time p tp) \<le> T (tape_size tp)" .
next
  assume assm: "\<forall>tp. the (time p tp) \<le> T (tape_size tp)"
  show "time_restricted T p" unfolding time_restricted_def proof
    fix tp
    define n where "n \<equiv> the (time p tp)"
    from assm have "time p tp \<noteq> None" sorry
    then have "n = (LEAST m. is_final (steps0 (1, tp) p m))" using n_def time_def by auto
    then have C1: "is_final (steps0 (1, tp) p n)" using least_p by metis
    from assm have C2: "n \<le> T(tape_size tp)" unfolding n_def ..
    show "\<exists>n\<le>T (tape_size tp). is_final (steps0 (1, tp) p n)" using C1 C2 by auto
  qed
qed



subsection\<open>Encoding\<close>

text\<open>Encoding binary words as TM tape cells: \<^term>\<open>Num.Bit1\<close> is encoded as \<^term>\<open>[Oc, Oc]\<close> and \<^term>\<open>Num.Bit1\<close> as term>\<open>[Oc, Bk]\<close>.
  Thus, the ends of an encoded term can be marked with the pattern \<^term>\<open>[Bk, Bk]\<close>.\<close>
fun encode_word :: "word \<Rightarrow> cell list"
  where "encode_word Num.One = []"
      | "encode_word (Num.Bit0 w) = Oc # Bk # encode_word w"
      | "encode_word (Num.Bit1 w) = Oc # Oc # encode_word w"

fun is_encoded_word :: "cell list \<Rightarrow> bool"
  where "is_encoded_word [] = True"
      | "is_encoded_word (Oc # _ # cs) = is_encoded_word cs"
      | "is_encoded_word _ = False"

fun decode_word :: "cell list \<Rightarrow> word"
  where "decode_word (Oc # Bk # cs) = Num.Bit0 (decode_word cs)"
      | "decode_word (Oc # Oc # cs) = Num.Bit1 (decode_word cs)"
      | "decode_word _ = Num.One"


lemma encode_decode_word: "decode_word (encode_word w) = w" 
  by (induction w) simp_all

lemma decode_encode_word:
  "is_encoded_word cs \<Longrightarrow> encode_word (decode_word cs) = cs" 
  (is "?ie cs \<Longrightarrow> ?de cs = cs")
proof (induction cs rule: is_encoded_word.induct)
  case (2 c cs) (* cs = Oc # c # cs *)
  from \<open>?ie (Oc # c # cs)\<close> have "?ie cs" by simp
  with "2.IH" have IH: "?de cs = cs" .
  then show ?case by (cases c) simp_all
qed (* cases "cs = []", "cs = Bk # _", "cs = [_]" by *) simp_all


subsection\<open>Deciding Languages\<close>

hide_const (open) L

text\<open>A TM \<^term>\<open>p\<close> is considered to decide a language \<^term>\<open>L\<close>, iff for every possible word \<^term>\<open>w\<close>
  it correctly calculates language membership. 
  That is, for \<^term>\<open>w \<in> L\<close> the computation results in \<^term>\<open>Oc\<close> under the TM head, 
  and for \<^term>\<open>w \<notin> L\<close> in \<^term>\<open>Bk\<close>.
  The head is over the first cell of the right tape. 
  That is for \<^term>\<open>tp = (L, x # r)\<close>, the symbol under the head is \<open>x\<close>, or \<open>hd (snd tp)\<close>\<close>
definition decides :: "lang \<Rightarrow> tprog0 \<Rightarrow> bool"
  where "decides L p \<equiv> \<forall>w. Hoare_halt
    (\<lambda>tp. tp = ([], encode_word w)) p (\<lambda>tp. hd (snd tp) = (if w \<in> L then Oc else Bk))"

(* TODO (?) notation: \<open>p decides L\<close> *)


subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition DTIME :: "(nat \<Rightarrow> nat) \<Rightarrow> lang set"
  where "DTIME T \<equiv> {L. \<exists>p. decides L p \<and> time_restricted T p}"

lemma in_dtimeI[intro]:
  assumes "decides L p"
    and "time_restricted T p"
  shows "L \<in> DTIME T"
  unfolding DTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> DTIME T"
  obtains p
  where "decides L p" 
    and "time_restricted T p"
  using assms unfolding DTIME_def by blast

lemma in_dtimeE'[elim]:
  assumes "L \<in> DTIME T"
  shows "\<exists>p. decides L p \<and> time_restricted T p"
  using assms unfolding DTIME_def ..


end