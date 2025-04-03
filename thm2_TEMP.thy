section \<open> (Temp) Theorem 2 Mechanisation \<close>

theory thm2_TEMP
  imports 
    "thm2_prelims_TEMP" 
begin   

section \<open> Preliminaries \<close>

text \<open> The actual UTP semantics themselves, we will declare them as constants for now
  They will be instantiated with the patterns, these will be instances of the patterns. \<close>

text \<open> We declare the following channel as the visible events of AnglePID_C and AnglePIDANN. \<close>

(*They are of channel type context_ch, because this is for the example *)
chantype context_ch = anewError :: "real" adiff :: "real" angleOutputE :: "real"

text \<open> We declare the semantics of the controllers as constants for now, with a given epsilon as 
       a constant, to be initialised later. \<close>
consts AnglePIDANN :: "(context_ch, 's) caction"
       AnglePID_C :: "(context_ch, 's) caction"
       \<epsilon> :: "real"
       \<delta> :: "real"

section \<open> Proofs \<close>

text \<open> Theorem 4 from the report, the theorem that shows the verification conditions for conformance. \<close>

text \<open> Automating the proof of this theorem is future work, we have proved a similar theorem on paper though. \<close>
(*P and D should not be free, should be constants: *)

consts P :: "real"
       D :: "real"

theorem conf_vcs:
assumes "\<epsilon> \<ge> 0" and 
  "\<And> x_1 x_2 :: real. \<And> y_1 :: real. 
      (y_1 = (P * x_1) + (D * x_2)) \<longrightarrow>
             \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>"
shows "(conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)"
  sorry


(*Preliminary, monotonicity of the f function. *)

definition spec_f :: "real \<Rightarrow> real \<Rightarrow> real" where
"spec_f x_1 x_2 = (P * x_1) + (D * x_2)"

definition spec_f_single :: "real \<Rightarrow> real" where
"spec_f_single x_1 = (P * x_1)"

lemma spec_f_mono: 
  fixes x_1 :: real and x_2 :: real and y_1 :: real and y_2 :: real
  assumes "P > 0" and "D > 0"
  shows "x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> (spec_f x_1 x_2) \<le> (spec_f y_1 y_2)"
  by (simp add: assms(1) assms(2) ordered_ab_semigroup_add_class.add_mono spec_f_def)

term "[ ((normI 1 (inRanges(1).1)), ((normI 1 (inRanges(1).2)))), 
         ((normI 2 (inRanges(2).1)), ((normI 2 (inRanges(2).2)))) ]"

(*Interval definition: *)
definition int :: "(real \<times> real) list" where
"int = [ ((normI 1 (inRanges(1).1)), ((normI 1 (inRanges(1).2)))), 
         ((normI 2 (inRanges(2).1)), ((normI 2 (inRanges(2).2)))) ]"

(*Using FST for MIN and SND for MAX, when encoding the intervals. *)
term "fst(int(1))"
term "fst(int(2))"
term "snd(int(1))"
term "snd(int(2))"

(*Abbreviation for readability, referring to the f_ann as annout 2 1 to correspond 
to the last layer of our example: *)
abbreviation "f_ann x_1 x_2 \<equiv> annout 2 1 [x_1,x_2]"

(*Lemma 5, monotonicity of specification function: *)
(*lets just say the variables x_1 x_2, make them free, 
assumptions, use the intervals for now:

Treat them as free variables here, for any inputs that are within range, this should hold. 
Make it for some free monotonic function. That we then normalise, 
 *)

 (*TEST APPLICATION: *)




lemma spec_mono_ann:
  fixes x_1 x_2 y_1 y_2 :: real and S :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes 
          "fst(int(1)) \<le> x_1 \<and> x_1 \<le> snd(int(1))" and 
          "fst(int(2)) \<le> x_2 \<and> x_2 \<le> snd(int(2))" and 
          "(snd(outRanges ! 0) > fst(outRanges ! 0) \<and> snd(annRange) > fst(annRange))" and
          "\<epsilon> > 0" and 
          "P > 0 \<and> D > 0" and
          "f_ann x_1 x_2 \<le> normO 1 (S (fst(int(1))) (fst(int(2))) + \<epsilon>)
               \<and> f_ann x_1 x_2 \<ge> normO 1 (S (snd(int(1))) (snd(int(2))) - \<epsilon>) 
              " and 
          (*Monotonicity property for our specification function: *)
          "\<forall> x_1 x_2 y_1 y_2 :: real. x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> S x_1 x_2 \<le> S y_1 y_2"
        shows "
               f_ann x_1 x_2 \<ge> (normO 1 (S (x_1) (x_2) - \<epsilon>)) \<and>
               f_ann x_1 x_2 \<le> (normO 1 (S (x_1) (x_2) + \<epsilon>)) 
                "
proof (rule conjI)
  have 1: "f_ann x_1 x_2 \<le> normO 1 (S (fst(int(1))) (fst(int(2))) + \<epsilon>)" using assms by simp 
  have 2: "f_ann x_1 x_2 \<ge> normO 1 (S (snd(int(1))) (snd(int(2))) - \<epsilon>)" using assms by simp

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
    by (smt (verit, ccfv_SIG) One_nat_def mono_normO)
  from 1 c1 show "f_ann x_1 x_2 \<le> normO 1 ((S x_1 x_2) + \<epsilon>)"
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
    by (smt (verit, best) One_nat_def mono_normO)
  from 2 c2 show "f_ann x_1 x_2 \<ge> (normO 1 (S (x_1) (x_2) - \<epsilon>))"
    using \<open>x_1 \<le> snd (thm2_TEMP.int(1)\<^sub>s) \<and> x_2 \<le> snd (thm2_TEMP.int(2)\<^sub>s)\<close> \<open>x_2 \<le> snd (thm2_TEMP.int(2)\<^sub>s) \<longrightarrow> S x_1 x_2 \<le> S (snd (thm2_TEMP.int(1)\<^sub>s)) (snd (thm2_TEMP.int(2)\<^sub>s))\<close> by linarith
qed


(*Rewrite this using our interval definitions, and f_ann, and spec_f. *)
theorem controller_conformance:
  assumes 

    (*Assumption on epsilon*)
    "\<epsilon> \<ge> 0" and

    (*Assumptions on the normalisation, that the ranges are well-formed*)
    "\<forall> i . snd(outRanges ! i) > fst(outRanges ! i) \<and> snd(annRange) > fst(annRange)" and

    (*The assumption on the range of the variables, we need them to be within the defined input ranges. *)
    "\<And> x_1 x_2. x_1 \<ge> (inRanges(1).1) \<and>
          x_1 \<le> (inRanges(1).2) \<and>
          x_2 \<ge> (inRanges(2).1) \<and>
          x_2 \<le> (inRanges(2).2)" and
  
    (*Marabou, these are the actual assumption discharged by Marabou: *)
    "\<And> x_1 x_2. x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<ge> normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ) + \<epsilon>)
          " and
    "\<And> x_1 x_2. x_1 \<ge> normI 1 (inRanges(1).1) \<and>
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<le> normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ) - \<epsilon>)"
    and 
    "P > 0 \<and> D > 0"
    
shows "(conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)" 
  apply (rule conf_vcs)
  (*Discharge first assumption: *)
   apply (simp add: assms(1))

proof - 
  (*Start with some fixed variables, we have no assumptions about them here: *)
  fix x_1 x_2 y_1 :: real
  from assms(4) assms(5) have m3: "x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
      
          \<not> annout 2 1 [x_1, x_2] \<ge> normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ) + \<epsilon>)
           \<and>
          \<not> annout 2 1 [x_1, x_2] \<le> normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ) - \<epsilon>)"
    by auto
    
   have "... \<longrightarrow>
   (annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
     by (smt (z3) assms(3))

  (*Very important step now, *)

   have "... \<longrightarrow> 
      (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (x_1 * P) + (denormI 2 (x_2 * D) ))) - \<epsilon>))
     \<and> 
     (annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (x_1 * P) + (denormI 2 (x_2 * D) ))) + \<epsilon>))
    "
     apply (rule impI)
     apply (rule spec_mono_ann)
     sorry



   (********************************)

  (*This is the ultimate goal: *)
  show "y_1 = P * x_1 + D * x_2 \<longrightarrow> \<bar>denormO 1 (annout 2 1 [normI 1 x_1, normI 2 x_2]) - y_1\<bar> \<le> \<epsilon>" by sorry
qed


  show "(y_1 = (P *x_1) + (D * x_2)) \<and> 
          normI 1 (fst (inRanges(1)\<^sub>s)) \<le> x_1 \<and>
       x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and>
       normI 2 (fst (inRanges(2)\<^sub>s)) \<le> x_2 \<and> x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<longrightarrow> 
        (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>) 
            )"

  show "(\<forall> x_1 x_2. (\<forall> y_1. (y_1 = (P *x_1) + (D * x_2)) \<longrightarrow>
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>) 
            )
          )) \<longrightarrow> ?thesis" 
    using assms apply (simp only: conf_vcs)
    done
  have 2: "(\<forall> x_1 x_2. (\<forall> y_1. (y_1 = (P *x_1) + (D * x_2)) \<longrightarrow>
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>) 
            )
          ))
          = 
          (\<forall> x_1 x_2. (
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - ((P * x_1) + (D * x_2)) \<bar> \<le> \<epsilon>) 
            )
          ))" by simp 

  fix x_1 :: "real" and x_2 :: "real"

  have "(
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - ((P * x_1) + (D * x_2)) \<bar> \<le> \<epsilon>) 
            )
          )
        = 
        ((denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - ((P * x_1) + (D * x_2)) \<le> \<epsilon> \<and> 
               (denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - ((P * x_1) + (D * x_2)) \<ge> -\<epsilon>)"
    by linarith 
  have "... = ((denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) \<le> \<epsilon> + ((P * x_1) + (D * x_2)) \<and> 
               (denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) \<ge> -\<epsilon> + ((P * x_1) + (D * x_2)))" by linarith
  have "... = ((denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) \<le> (denormO 1 (normO 1 (\<epsilon> + ((P * x_1) + (D * x_2))))) \<and> 
               (denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) \<ge> (denormO 1 (normO 1 (-\<epsilon> + ((P * x_1) + (D * x_2))))))" 
    by (simp add: output_norm_2 assms)
  
  
    

  show "?thesis" using "1" "2" assms by sorry
qed

notepad
begin

end

lemma test: "\<forall> x. x > 3"
proof - 
  fix x :: real
  have "x > 3 \<Longrightarrow> \<forall> x. x > 3"












end
