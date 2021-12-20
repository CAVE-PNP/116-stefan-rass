theory Simpl_Notes
  imports Main Simpl.Simpl Universal_Turing_Machine.UTM
begin

definition Looping_TM :: tprog0 where "Looping_TM = [(W0, 1), (W0, 1)]"

definition decode_TM :: "nat \<Rightarrow> tprog0" where "decode_TM m \<equiv>
  if \<exists>!M. m = code M then THE M. m = code M else Looping_TM"

definition halts' :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  where "halts' m t \<equiv> halts (decode_TM m) [t]"

record 'g vars = "'g StateSpace.state" +
  m_' :: nat
  t_' :: nat
  h_' :: bool

procedures halts(m,t|h) = "\<acute>h :== halts' \<acute>m \<acute>t"

  halts_spec: "\<Gamma>\<turnstile> \<lbrace> True \<rbrace> \<acute>h :== PROC halts(\<acute>m,\<acute>t) \<lbrace> \<acute>h = halts' \<acute>m \<acute>t \<rbrace>"

lemma (in halts_impl) halts_spec by (hoare_rule HoarePartial.ProcRec1) vcg

end
