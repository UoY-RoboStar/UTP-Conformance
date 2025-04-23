section \<open> (Temp) Theorem 2 Work to make it General \<close>

theory thm2_general_work
  imports 
    "thm2_TEMP" 
begin   


(*Spec mono, in general: *)

(*For functions from a list of real numbers. 

Let x be the input here, list of any variables, 

output of any variables too? yes,

within a given range, sure; 

Insize outsize.  *)
(*needs to take number of inputs, *)
fun intlist_min :: "nat \<Rightarrow> real list" where 
"intlist_min 0 = []" | 
"intlist_min n = [fst(int(n))] @ intlist_min (n-1)"

fun intlist_max :: "nat \<Rightarrow> real list" where 
"intlist_max 0 = []" | 
"intlist_max n = [snd(int(n))] @ intlist_max (n-1)"


lemma spec_mono_ann_general:
  fixes  
        insize :: "nat" and
        outsize :: "nat" and 
        x y :: "real list" and
        S f :: "real list \<Rightarrow> real list"
      assumes 
          "\<forall> n :: nat. n \<le> varNo \<longrightarrow> fst(int(i)) \<le> x(i) \<and> x(i) \<le> snd(int(i))" and 
          "\<forall> n :: nat. 
            (snd(outRanges ! n) > fst(outRanges ! n) \<and> 
            snd(annRange) > fst(annRange))" and

          "\<epsilon> \<ge> 0" and 
          
          (*Monotonicity property for our specification function: 
          Needs to be monotonic in every variable, this assumption shows this:
          Every output is monotonically increasing, is this *)
          "\<forall> x y :: real list. 
             (\<forall> n :: nat. n \<le> insize \<longrightarrow>  (x(n) \<le> y(n))) \<longrightarrow>
             (\<forall> out :: nat. out \<le> outsize \<longrightarrow> (S x)(out) \<le> (S y)(out))" and

          "#x = insize"
  
shows "\<forall> n :: nat. n \<in> {1..outsize} \<longrightarrow>
           (f x)(n) \<le> normO n ((S (intlist_min(varNo)))(n) + \<epsilon>) \<and>
           (f x)(n) \<ge> normO n ((S (intlist_max(varNo)))(n) - \<epsilon>) 
           \<longrightarrow>
           (f x)(n) \<le> normO n ((S x)(n) + \<epsilon>) \<and>
           (f x)(n) \<ge> normO n ((S x)(n) - \<epsilon>)
                "


(*
proof (rule conjI)
  have 1: "f x_1 x_2 \<le> normO 1 (S (fst(int(1))) (fst(int(2))) + \<epsilon>)" using assms by simp 
  have 2: "f x_1 x_2 \<ge> normO 1 (S (snd(int(1))) (snd(int(2))) - \<epsilon>)" using assms by simp

  (*GOAL 1: first conjunct of the goal: *)
  from assms(1) assms(2) have "x_1 \<ge> fst(int(1)) \<and> x_2 \<ge> fst(int(2))" by simp
  have "... \<longrightarrow> 
        (S x_1 x_2) \<ge> (S (fst(int(1))) (fst(int(2))))" 
    using assms by simp
  have "... \<longrightarrow> 
        (S x_1 x_2) + \<epsilon> \<ge> (S (fst(int(1))) (fst(int(2)))) + \<epsilon>"
    by simp
  have c1:"... \<longrightarrow> 
        normO 1 ((S x_1 x_2) + \<epsilon>) \<ge> normO 1 ((S (fst(int(1))) (fst(int(2)))) + \<epsilon>)"
    using assms 
    apply (simp add: mono_normO)
    by (smt (verit, ccfv_SIG) diff_Suc_1 mono_normO)
  from 1 c1 show "f x_1 x_2 \<le> normO 1 ((S x_1 x_2) + \<epsilon>)"
    using \<open>fst (thm2_TEMP.int(1)\<^sub>s) \<le> x_1 \<and> fst (thm2_TEMP.int(2)\<^sub>s) \<le> x_2\<close> \<open>fst (thm2_TEMP.int(2)\<^sub>s) \<le> x_2 \<longrightarrow> S (fst (thm2_TEMP.int(1)\<^sub>s)) (fst (thm2_TEMP.int(2)\<^sub>s)) \<le> S x_1 x_2\<close> by argo
    
  (*Goal 2: second cojunct of the goal: *)
  from assms(1) assms(2) have "x_1 \<le> snd(int(1)) \<and> x_2 \<le> snd(int(2))" by simp
  have "... \<longrightarrow> 
        (S x_1 x_2) \<le> (S (snd(int(1))) (snd(int(2))))" 
    using assms by simp
  have "... \<longrightarrow> 
        (S x_1 x_2) - \<epsilon> \<le> (S (snd(int(1))) (snd(int(2)))) - \<epsilon>"
    by simp
  have c2: "... \<longrightarrow> 
        normO 1 ((S x_1 x_2) - \<epsilon>) \<le> normO 1 ((S (snd(int(1))) (snd(int(2)))) - \<epsilon>)"
    using assms 
    apply (simp add: mono_normO)
    by (smt (verit, ccfv_SIG) diff_Suc_1 mono_normO)
  from 2 c2 show "f x_1 x_2 \<ge> (normO 1 (S (x_1) (x_2) - \<epsilon>))"
    using \<open>x_1 \<le> snd (thm2_TEMP.int(1)\<^sub>s) \<and> x_2 \<le> snd (thm2_TEMP.int(2)\<^sub>s)\<close> \<open>x_2 \<le> snd (thm2_TEMP.int(2)\<^sub>s) \<longrightarrow> S x_1 x_2 \<le> S (snd (thm2_TEMP.int(1)\<^sub>s)) (snd (thm2_TEMP.int(2)\<^sub>s))\<close> by linarith
qed
*)





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
