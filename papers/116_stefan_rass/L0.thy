theory L0
  imports Complexity
begin

(* TODO (?) model the free (unknown) function T (and t) as locale *)

definition L\<^sub>D :: "(nat \<Rightarrow> nat) \<Rightarrow> lang"
  where LD_def[simp]: "L\<^sub>D T \<equiv> {w. let M\<^sub>w = TM_decode_pad w in
                                rejects M\<^sub>w w \<and> the (time M\<^sub>w ([], encode_word w)) \<le> T (length w)}"
(* TODO (?) create separate definition "halts_within" *)

definition L\<^sub>0 :: "(nat \<Rightarrow> nat) \<Rightarrow> lang"
  where L0_def[simp]: "L\<^sub>0 T \<equiv> L\<^sub>D T \<inter> SQ"


(* Lemma 4.6, p15 *)
theorem dens_L0: "dens (L\<^sub>0 T) n \<le> dsqrt n" oops

end
