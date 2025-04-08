section \<open> (Temp) Theorem 2 Work to make it General \<close>

theory thm2_general_work
  imports 
    "thm2_TEMP" 
begin   

(*Interval splitting,
for every dimension, d

i starts from 0, I IS 0 INDEXED, noInt is the number of SPLITS
 *)
definition int_split :: "nat \<Rightarrow> nat \<Rightarrow> (real \<times> real) list" where
"int_split i noInt = [ ( (fst(int(1)) + ((i :: real) * (snd(int(1)) / noInt))), 
                         (fst(int(1)) + ((i + 1 :: real) * (snd(int(1)) / noInt)))),
                      ( (fst(int(2)) + ((i :: real) * (snd(int(2)) / noInt))), 
                         (fst(int(2)) + ((i + 1 :: real) * (snd(int(2)) / noInt)))) ]"


(*Marabou interval results: *)

(*Temporary, but shows that with one interval, we obtain 
2 queries, as is our hard coded marabou results lemma as below.

Will expand to generate noInt * 2 (for every dimension, *)
lemma marabou_interval_results: 
  fixes x :: real list and noInt :: nat and inSize :: nat and FANN :: real list \<Rightarrow> real
  assumes "noInt = 1"
  shows "
          (\<forall> int_list :: nat list. (# int_list = inSize \<and> 
              (\<forall> i :: nat. i \<in> {1..(#int_list)} \<longrightarrow> int_list(n) \<in> {0..(noInt-1)}) ) \<longrightarrow>
          (\<forall> i :: nat. i \<in> {1..inSize} \<longrightarrow> 
          (x(i) \<ge> fst((int_split (int_list(i)) noInt)(i)) \<and> 
           x(i) \<le> snd((int_split (int_list(i)) noInt)(i))))
          \<longrightarrow>
          \<not> FANN x \<ge> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
           \<and>   
          (\<forall> i :: nat. i \<in> {1..inSize} \<longrightarrow>
          (x(i) \<ge> fst((int_split (int_list(i)) noInt)(i)) \<and> 
           x(i) \<le> snd((int_split (int_list(i)) noInt)(i))))
          \<longrightarrow>       
          \<not> FANN x \<le> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>))
" 
proof - 
  show "?thesis" 
    apply (simp add: assms)
  proof - 
    have 1:"(x1 \<ge> fst((int_split 0 (Suc 0))(1)) \<and> 
          x1 \<le> snd((int_split 0 (Suc 0))(1)) \<and>
          x2 \<ge> fst((int_split 0 (Suc 0))(2)) \<and>
          x2 \<le> snd((int_split 0 (Suc 0))(2)) \<longrightarrow>
          \<not> f_ann x_1 x_2 \<ge> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
          )" sorry
    have 2: "(x1 \<ge> fst((int_split 0 (Suc 0))(1)) \<and> 
          x1 \<le> snd((int_split 0 (Suc 0))(1)) \<and>
          x2 \<ge> fst((int_split 0 (Suc 0))(2)) \<and>
          x2 \<le> snd((int_split 0 (Suc 0))(2)) \<longrightarrow>        
          \<not> f_ann x_1 x_2 \<le> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>))
      " sorry

    from 1 2 have 3:"
          (x1 \<ge> fst((int_split 0 (Suc 0))(1)) \<and> 
          x1 \<le> snd((int_split 0 (Suc 0))(1)) \<and>
          x2 \<ge> fst((int_split 0 (Suc 0))(2)) \<and>
          x2 \<le> snd((int_split 0 (Suc 0))(2)) \<longrightarrow>
          \<not> f_ann x_1 x_2 \<ge> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
          )
           \<and>   
          (x1 \<ge> fst((int_split 0 (Suc 0))(1)) \<and> 
          x1 \<le> snd((int_split 0 (Suc 0))(1)) \<and>
          x2 \<ge> fst((int_split 0 (Suc 0))(2)) \<and>
          x2 \<le> snd((int_split 0 (Suc 0))(2)) \<longrightarrow>        
          \<not> f_ann x_1 x_2 \<le> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>))
      " by auto
qed

end
