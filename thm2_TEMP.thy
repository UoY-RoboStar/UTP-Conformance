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


(*Needs to be implication, back to paper: *)
notepad
begin
  fix x_1 x_2 :: real
(*This is actually truly what Marabou gives us: *)
  (*We actually ahve: *)
  have "p \<Longrightarrow> Q \<and> p \<Longrightarrow> R" by sorry
  (*What we can derive from this. *)
  have "p \<Longrightarrow> Q \<and> p \<Longrightarrow> R \<Longrightarrow> p \<Longrightarrow> Q \<and> R" by auto
  (*IT IS SOUND. *)
  (*Marabou tells us, that this IS THE CASE, but we want the OPPOSITE. *)
  (*Marabou tells us, ideally, if this is NOT THE CASE, but it does try to see if this is the case. 

  Then, it is how we use it, ideally this would be FALSE. We're going to phase it, as its how we USE THE RESULTS. 
  We want this statement, to be FALSE AT THE BEGINNING, THIS IS WHAT WE WANT, if Marabou doesn't tell us this, 
we have a problem. 
 *)
  (*MARABOU 1: *)
  have m1: "x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>
          " by sorry
  have m2: "x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>"
    by sorry
  (*The implication, is the new line, is the separation between INPUT AND OUTPUT*)
  (*Have two separate conditions, then see if we can provve *)
  (*THIS IS THE ACTUAL CONDITIONS, *)
  from m1 m2 have m3: "x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
      
          (\<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
           \<and>
          (\<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
    by auto
    
  (*We get this from our assumptions. *)
    assume a1: "x_1 \<ge> normI 1 (inRanges(1).1) \<and>
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2)"
  from a1 m3 have "
    (\<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (\<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
    by auto


  have "... = 
   (annout 2 1 [x_1, x_2] < (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (annout 2 1 [x_1, x_2] > (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
    using a1 m3 by linarith

   have "... \<longrightarrow>
   (annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
     using a1 m1 by linarith

   
  
end
  

(*Sanity checks: *)
lemma "\<forall> x_1 :: real. 
          x_1 \<ge> 1 \<Longrightarrow> False"
  using not_one_le_zero by blast

lemma "\<And> x_1 :: real. 
          x_1 \<ge> 1 \<Longrightarrow> False"
  quickcheck
  sorry


theorem controller_conformance_manual:
  assumes 

    (*Assumption on epsilon*)
    "\<epsilon> \<ge> 0" and

    (*Assumptions on the normalisation, that the ranges are well-formed*)
    "\<forall> i . snd(outRanges ! i) > fst(outRanges ! i) \<and> snd(annRange) > fst(annRange)" and
    (*The assumption on the range of the variables, we need this to make the proof cleaner: *) 
    "\<And> x_1 x_2. x_1 \<ge> normI 1 (inRanges(1).1) \<and>
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2)" and
  
    (*Marabou, these are the actual assumption discharged by Marabou: *)
    "\<And> x_1 x_2. x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>
          " and
    "\<And> x_1 x_2. x_1 \<ge> normI 1 (inRanges(1).1) \<and>
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>"
     
    
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
      
          (\<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
           \<and>
          (\<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
    by auto

  from assms(3) m3 have "
    (\<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (\<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
    by auto


  have "... = 
   (annout 2 1 [x_1, x_2] < (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (annout 2 1 [x_1, x_2] > (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
    by (meson assms(3) gt_ex linorder_not_less)
    
   have "... \<longrightarrow>
   (annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
     by (smt (z3) assms(3))
  
   have "... = 
    (\<bar>annout 2 1 [x_1, x_2] -
       (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) )))\<bar>
     \<le> \<epsilon>)"
     by (meson assms(3) gt_ex linorder_not_less)

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
