section \<open> (Temp) Theorem 2 Mechanisation \<close>

theory thm2_TEMP
  imports 
    "thm2_prelims_TEMP" 
begin   


(*The actual UTP semantics themselves, we will declare them as constants for now

They will be instantiated with the patterns, these will be instances of the patterns eventually: *)

(*We will be needing the channels: *)


(*They are of channel type context_ch, because this is for the example *)
chantype context_ch = anewError :: "real" adiff :: "real" angleOutputE :: "real"

consts AnglePIDANN :: "(context_ch, 's) caction"
       AnglePID_C :: "(context_ch, 's) caction"
       \<epsilon> :: "real"

(*Theorem 4 from the report, which a version just for the example is Theorem 4 from the paper: *)
theorem conf_vcs:
fixes P :: "real" and D :: "real"
assumes "\<epsilon> \<ge> 0" and 
  "(\<forall> x_1 x_2. (\<forall> y_1. (y_1 = (P *x_1) + (D * x_2)) \<longrightarrow> 
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>) 
            )
          ))"
shows "(conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)"
  sorry


(*This is a mechanisation of Theorem 2 from the conformance report. 

conf_sin because the channel type is a singular type "real \<Longrightarrow> 'a", not a product type. *)


lemma test:
  assumes "(\<And> x_1 x_2. (
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - ((P * x_1) + (D * x_2)) \<bar> \<le> \<epsilon>) 
            )
          ))"
  fixes x_1 :: "real" and x_2 :: "real"
  shows "(\<forall> x_1 x_2. (
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - ((P * x_1) + (D * x_2)) \<bar> \<le> \<epsilon>) 
            )
          ))"
  apply (rule allI)
  apply (rule allI)
  apply (simp)
  using One_nat_def assms by presburger

theorem controller_conformance:
  assumes "\<epsilon> \<ge> 0" and 
    "\<forall> i . snd(outRanges ! i) > fst(outRanges ! i) \<and> snd(annRange) > fst(annRange)"
  shows "(conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)" 
proof - 
  let ?P = "60" and ?D = "0.6"
  have 1: "(\<forall> x_1 x_2. (\<forall> y_1. (y_1 = (P *x_1) + (D * x_2)) \<longrightarrow>
            (
              ( \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>) 
            )
          )) \<longrightarrow> ?thesis" 
    using assms apply (simp add: conf_vcs)
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















end
