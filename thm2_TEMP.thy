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



(*ULTIMATE GOAL: *)

term "(\<And> x_1 x_2.
          (x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow> 
          \<not> (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta> \<and>
          annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta> )
         ))"

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
  have "(x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta>
          )
           \<and>
          (x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta> )"
    by sorry
  have "... \<longrightarrow> 
          x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
      
          (\<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta>)
           \<and>
          (\<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta>)"
    using \<open>(normI 1 (fst (inRanges(1)\<^sub>s)) \<le> x_1 \<and> x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> x_2 \<and> x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<longrightarrow> \<not> normO 1 (denormI 1 (normI 1 (fst (inRanges(1)\<^sub>s)) * P) + denormI 2 (normI 2 (fst (inRanges(2)\<^sub>s))) * D) + \<epsilon> + \<delta> \<le> annout 2 1 [x_1, x_2]) \<and> (normI 1 (fst (inRanges(1)\<^sub>s)) \<le> x_1 \<and> x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> x_2 \<and> x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<longrightarrow> \<not> annout 2 1 [x_1, x_2] \<le> normO 1 (denormI 1 (normI 1 (snd (inRanges(1)\<^sub>s)) * P) + denormI 2 (normI 2 (snd (inRanges(2)\<^sub>s))) * D) - \<epsilon> - \<delta>)\<close> by fastforce
    
    assume "x_1 \<ge> normI 1 (inRanges(1).1) \<and>
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2)"
  then have "... \<longrightarrow> 
    (\<not> annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta>)
     \<and>
    (\<not> annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta>)"
    using \<open>(normI 1 (fst (inRanges(1)\<^sub>s)) \<le> x_1 \<and> x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> x_2 \<and> x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<longrightarrow> \<not> normO 1 (denormI 1 (normI 1 (fst (inRanges(1)\<^sub>s)) * P) + denormI 2 (normI 2 (fst (inRanges(2)\<^sub>s))) * D) + \<epsilon> + \<delta> \<le> annout 2 1 [x_1, x_2]) \<and> (normI 1 (fst (inRanges(1)\<^sub>s)) \<le> x_1 \<and> x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> x_2 \<and> x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<longrightarrow> \<not> annout 2 1 [x_1, x_2] \<le> normO 1 (denormI 1 (normI 1 (snd (inRanges(1)\<^sub>s)) * P) + denormI 2 (normI 2 (snd (inRanges(2)\<^sub>s))) * D) - \<epsilon> - \<delta>)\<close> by blast
    
   (*we will get rid of these with our assumptions, which will be implicit in the proof: *)
  (*We want this to be false so: *)

  have "... \<longrightarrow> 
   (annout 2 1 [x_1, x_2] < (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta>)
     \<and>
    (annout 2 1 [x_1, x_2] > (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta>)"
    by auto
  (*ANN function is not, in fact, monotonic, but, this works, because this is bounds on the SPEC FUNCTION, THAT IS MONOTONIC. *)
  (*ANN function is TESTED AT EVERY FIXED X_1, within limits, thats why we don't need monotonicity 
  of the ANN function, it is evaluated at every x_1 and x_2, tested with SMT solvers, so we don't need it to be. 
  We do need the spec function to be, because, it is the one being tested. *)
  have "... \<longrightarrow>
   (annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon>)
     \<and>
    (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon>)"
    using 
(*Why doesn't this work ? monotonic, need ann function to be monotonic. *)
  
    
   


   
  
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
    "\<epsilon> \<ge> 0" and 
    "\<forall> i . snd(outRanges ! i) > fst(outRanges ! i) \<and> snd(annRange) > fst(annRange)"
  
shows "
      \<And> x_1 x_2 :: real. (x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow> 
          \<not> (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta> \<and>
          annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta> )
         ) \<Longrightarrow> (conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)" 
  apply (rule conf_vcs)
  (*Discharge first assumption: *)
  apply (simp add: assms)

(*Even though different names, if we have some fixed variables, show this

IT WORKS, IT STILL WORKS: *)
proof - 
  (*Start with some fixed variables, we have no assumptions about them here: *)
  fix x_1 x_2 y_1 :: real

  (*Going to do forwards reasoning, makes the most sense here: *)
  (*Chain of equality and implication, to get to our goal: *)
  (*Add our assumptions here perhaps: *)
  (*This is the MARABOU PREDICATE: *)
  have "(x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow> 
          \<not> (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta> \<and>
          annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta> )
         )" by sorry (*WILL BE MARABOU: *)

  have "(x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x_1 \<le> normI 1 (inRanges(1).2) \<and>
          x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow> 
          \<not> (annout 2 1 [x_1, x_2] \<ge> (normO 1 ((denormI 1 (normI 1 (inRanges(1).1) * P) + (denormI 2 (normI 2 (inRanges(2).1)) * D) ))) + \<epsilon> + \<delta> \<and>
          annout 2 1 [x_1, x_2] \<le> (normO 1 ((denormI 1 (normI 1 (inRanges(1).2) * P) + (denormI 2 (normI 2 (inRanges(2).2)) * D) ))) - \<epsilon> - \<delta> )
         ) = undefined"
  

  (*Then we derive our goal from this: *)

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
