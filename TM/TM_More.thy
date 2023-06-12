theory TM_More
  imports "Cook_Levin.Basics"
    "../Supplementary/Misc" "../Supplementary/Lists"
    Intro_Dest_Elim.IHOL_IDE
begin


definition valid_tape :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where "valid_tape G tp = (case tp of (f, i) \<Rightarrow> \<forall>j. f j < G)"

lemma valid_tape_contents[intro]: "G \<ge> 4 \<Longrightarrow> symbols_lt G xs \<Longrightarrow> valid_tape G (contents xs, i)"
  unfolding valid_tape_def contents_def by simp

lemma valid_tape_act:
  assumes "valid_tape G tp"
    and "fst a < G"
  shows "valid_tape G (act a tp)"
  using \<open>fst a < G\<close>
proof (induction a)
  case (Pair w m)
  thus ?case unfolding fst_conv using \<open>valid_tape G tp\<close>
    by (induction tp) (simp add: act valid_tape_def)
qed


definition valid_config :: "nat \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool"
  where "valid_config k G cfg = ( ||cfg|| = k \<and> list_all (valid_tape G) (snd cfg) )"

mk_ide valid_config_def |intro valid_configI[intro]| |elim valid_configE[elim]| |dest valid_configD[dest]|


lemma valid_config_readD[dest]:
  assumes "valid_config k G cfg"
  shows "length (config_read cfg) = k"
    and "symbols_lt G (config_read cfg)"
proof -
  from assms show "length (config_read cfg) = k" by (auto simp: read_length)

  from assms have "list_all (valid_tape G) (snd cfg)" ..
  then show "symbols_lt G (config_read cfg)"
    unfolding read_def length_map list_all_length valid_tape_def by (elim all_transferE) fastforce
qed



lemma valid_start_config:
  assumes "k \<ge> 2" and "G \<ge> 4" and "symbols_lt G xs"
  shows "valid_config k G (start_config k xs)"
proof (intro valid_configI)
  from \<open>k \<ge> 2\<close> show "||start_config k xs|| = k" by (simp add: start_config_length)
  from \<open>G \<ge> 4\<close> and \<open>symbols_lt G xs\<close> show "list_all (valid_tape G) (snd (start_config k xs))"
    unfolding start_config_def snd_conv list_all_simps(1)
    by (intro conjI list_all_replicate valid_tape_contents) auto
qed


lemma exe_num_tapes':
  assumes "turing_machine k G M"
    and "valid_config k G cfg"
  shows "||exe M cfg|| = ||cfg||"
  using assms exe_num_tapes[OF assms(1)] valid_configD(1) by presburger


lemma valid_config_exe:
  assumes "turing_machine k G M" and "valid_config k G cfg"
  shows "valid_config k G (exe M cfg)"
proof (cases "fst cfg < length M")
  case False with \<open>valid_config k G cfg\<close> show "valid_config k G (exe M cfg)" by (simp add: exe_def)
next
  let ?i = "fst cfg" let ?q = "M ! ?i"
  let ?hds = "config_read cfg"
  case True
  then have "exe M cfg = sem ?q cfg" by (fact exe_lt_length)

  show ?thesis using \<open>valid_config k G cfg\<close>
  proof (elim valid_configE, intro valid_configI)
    assume "||cfg|| = k"
    with \<open>turing_machine k G M\<close> show "||exe M cfg|| = k" using exe_num_tapes by simp

    assume "list_all (valid_tape G) (snd cfg)"
    then show "list_all (valid_tape G) (snd (exe M cfg))"
      unfolding list_all_length and \<open>||cfg|| = k\<close> and \<open>||exe M cfg|| = k\<close>
    proof (elim all_transferE)
      fix n
      assume "n < k" and "valid_tape G (cfg <!> n)"

      from \<open>turing_machine k G M\<close> have h1: "turing_command k (length M) G (M ! fst cfg)"
        using \<open>fst cfg < length M\<close> by (fact turing_machineD)
      from \<open>valid_config k G cfg\<close> have h2: "length ?hds = k" ..

      have h3: "exe M cfg <!> n = act ((M ! fst cfg) ?hds [!] n) (cfg <!> n)"
        unfolding \<open>exe M cfg = sem ?q cfg\<close>
      proof (intro sem_snd)
        from h1 show "\<forall>gs. length gs = k \<longrightarrow> length ([!!] (M ! fst cfg) gs) = length gs"
          by (blast dest: turing_commandD(1))
      qed (fact \<open>n < k\<close> \<open>||cfg|| = k\<close> refl)+

      from \<open>valid_tape G (cfg <!> n)\<close> show "valid_tape G (exe M cfg <!> n)" unfolding h3
      proof (elim valid_tape_act)
        from h1 h2 assms(2) \<open>n < k\<close> show "?q ?hds [.] n < G" by (auto intro: turing_commandD(2))
      qed
    qed
  qed
qed

lemma valid_config_execute:
  assumes "turing_machine k G M" and "valid_config k G cfg"
  shows "valid_config k G (execute M cfg t)"
proof (induction t)
  case 0  show ?case unfolding execute.simps by (fact \<open>valid_config k G cfg\<close>)  next
  case (Suc t)  with assms show ?case unfolding execute.simps by (intro valid_config_exe)
qed


end
