theory ex4_2
  imports Main
begin

lemma fixes xs :: "'a list" 
  shows "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"

  using [[simp_trace_new mode=full]]
proof cases
  assume "even (length xs)"
  then obtain k where "2* k = length xs" by auto
  obtain ys where "ys = take k xs" by simp
  obtain zs where "zs = drop k xs" by simp

  have "length ys = k" using \<open>2 * k = length xs\<close> \<open>ys = take k xs\<close> by auto
  moreover have "length zs = k" using \<open>2 * k = length xs\<close> \<open>zs = drop k xs\<close> by auto
  ultimately have "length ys = length zs" by simp
  moreover have "xs = ys@zs" by (simp add: \<open>ys = take k xs\<close> \<open>zs = drop k xs\<close>)
  ultimately show "?thesis" by auto
next
  assume "odd (length xs)"
  then obtain k where "2*k = length xs +1"
    using dvd_mult_div_cancel odd_even_add odd_one by blast
  obtain ys where "ys = take k xs" by simp
  obtain zs where "zs = drop k xs" by simp

  have "length ys = k" using \<open>2 * k = length xs +1\<close> \<open>ys = take k xs\<close> by auto
  moreover have "length zs = k-1" using \<open>2 * k = length xs +1\<close> \<open>zs = drop k xs\<close> by auto
  ultimately have "length ys = Suc (length zs)"
    using \<open>odd (length xs)\<close> \<open>ys = take k xs\<close> \<open>zs = drop k xs\<close> odd_pos by fastforce
  moreover have "xs = ys@zs" by (simp add: \<open>ys = take k xs\<close> \<open>zs = drop k xs\<close>)
  ultimately show "?thesis" by auto
qed

end
