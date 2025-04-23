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
       \<epsilon>C :: "real"

definition \<epsilon> :: "real" where 
"\<epsilon> = 1.0"

section \<open> Proofs \<close>

text \<open> Theorem 4 from the report, the theorem that shows the verification conditions for conformance. \<close>

text \<open> Automating the proof of this theorem is future work, we have proved a similar theorem on paper though. \<close>
(*P and D should not be free, should be constants: *)

consts PC :: "real"
       DC :: "real"

definition P :: "real" where "P = 60.0"
definition D :: "real" where "D = 0.6"


(*If they appear free here, they are for any input, this is a statement about
this input, not for all input, *)
theorem conf_vcs:
  fixes x_1 x_2 y_2 :: real
assumes "\<epsilon> \<ge> 0" and 
  "(y_1 = (P * x_1) + (D * x_2)) \<longrightarrow>
             \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>"
shows "(conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)"
  sorry


(*Preliminary, monotonicity of the f function. *)

definition spec_f :: "real \<Rightarrow> real \<Rightarrow> real" where
"spec_f x_1 x_2 = (P * x_1) + (D * x_2)"

definition norm_spec_f :: "real \<Rightarrow> real \<Rightarrow> real" where 
"norm_spec_f x_1 x_2 = (denormI 1 (x_1 * P) + (denormI 2 (x_2 * D) ))"

definition norm_spec_f_2 :: "real \<Rightarrow> real \<Rightarrow> real" where 
"norm_spec_f_2 x_1 x_2 = 
  (P * denormI 1 (x_1) + (D * denormI 2 (x_2)) )"

lemma norm_spec_f_mono: 
  fixes x_1 :: real and x_2 :: real and y_1 :: real and y_2 :: real
  assumes "P > 0" and "D > 0" and 
    "(snd(inRanges(1)) > fst(inRanges(1)) \<and> snd(inRanges(2)) > fst(inRanges(2)) \<and> snd(annRange) > fst(annRange))"
  shows "x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> (norm_spec_f x_1 x_2) \<le> (norm_spec_f y_1 y_2)"
  using assms apply (simp add: mono_denormI mono_norm norm_spec_f_def ordered_ab_semigroup_add_class.add_mono)
  by (smt (verit, best) One_nat_def assms(3) mono_denormI mult.commute mult_left_mono)
 

lemma norm_spec_f_2_mono: 
  fixes x_1 :: real and x_2 :: real and y_1 :: real and y_2 :: real
  assumes "P > 0" and "D > 0" and 
    "(snd(inRanges(1)) > fst(inRanges(1)) \<and> snd(inRanges(2)) > fst(inRanges(2)) \<and> snd(annRange) > fst(annRange))"
  shows "x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> (norm_spec_f_2 x_1 x_2) \<le> (norm_spec_f_2 y_1 y_2)"
  using assms apply (simp add: mono_denormI mono_norm norm_spec_f_def mono_normI
            ordered_ab_semigroup_add_class.add_mono)
  by (smt (verit, best) assms(3) mono_denormI mono_normI mult.commute mult_le_cancel_left_pos norm_spec_f_2_def)
  

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
term "#int"


(*Using FST for MIN and SND for MAX, when encoding the intervals. *)
term "fst(int(1))"
term "fst(int(2))"
term "snd(int(1))"
term "snd(int(2))"

(*Abbreviation for readability, referring to the f_ann as annout 2 1 to correspond 
to the last layer of our example: *)
abbreviation "f_ann x y \<equiv> annout 2 1 [x,y]"
    

lemma spec_mono_ann:
  fixes x_1 x_2 y_1 y_2 :: real and
        S :: "real \<Rightarrow> real \<Rightarrow> real" and 
        f :: "real \<Rightarrow> real \<Rightarrow> real" 
  assumes 
          "fst(int(1)) \<le> x_1 \<and> x_1 \<le> snd(int(1))" and 
          "fst(int(2)) \<le> x_2 \<and> x_2 \<le> snd(int(2))" and 
          "(snd(outRanges ! 0) > fst(outRanges ! 0) \<and> snd(annRange) > fst(annRange))" and
          "\<epsilon> \<ge> 0" and 
          "f x_1 x_2 \<le> normO 1 (S (fst(int(1))) (fst(int(2))) + \<epsilon>)
               \<and> f x_1 x_2 \<ge> normO 1 (S (snd(int(1))) (snd(int(2))) - \<epsilon>) 
              " and 
          (*Monotonicity property for our specification function: *)
          "\<forall> x_1 x_2 y_1 y_2 :: real. x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> S x_1 x_2 \<le> S y_1 y_2"
        shows "
               f x_1 x_2 \<ge> (normO 1 (S (x_1) (x_2) - \<epsilon>)) \<and>
               f x_1 x_2 \<le> (normO 1 (S (x_1) (x_2) + \<epsilon>)) 
                "
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

(*Marabou combined results: *)

(*This assumes that Marabou returns UNSAT, as is the desired result. 
If Marabou returns SAT, a counterexample, currently, we will choose another epsilon
such that this holds. *)

(*We need to evaluate both: *)
term "inRanges"


(*The idea is, we have 2 facts that are evaluated expressions, that we use 
to show the truth of symbolic expressions, with constant definitions

That we can then reason about the fst int, etc, algebriacally within Isabelle.

But we only prove the evaluated expressions, it only works if we instantiate 
the constants but this is fine. *)

(*Evaluated expressions, for Marabou translation: *)
value "fst(int(1))"
value "snd(int(1))"
value "fst(int(2))"
value "snd(int(2))"
value "normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)"
value "normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>)"

(*We need to have a strategy for the splits, automatically. 
we already have int, meaningless without the splits. 

We need it to be automatic, automated evaluation as well. 

*)

lemma marabou_evaluated_results: 
  fixes x1 x2 :: real
  assumes "x1 \<ge> fst(int(1)) \<and> 
          x1 \<le> snd(int(1)) \<and>
          x2 \<ge> fst(int(2)) \<and>
          x2 \<le> snd(int(2))"
  shows "
          \<not> f_ann x1 x2 \<ge> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
           \<and>           
          \<not> f_ann x1 x2 \<le> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>)
" 
proof - 
  have 1: "x1 \<ge> 0 \<and> 
          x1 \<le> 1 \<and>
          x2 \<ge> 0 \<and>   
          x2 \<le> 1 \<longrightarrow> 
          \<not> f_ann x1 x2 \<ge> (1 / 3900)
          " sorry
  have 2: "x1 \<ge> 0 \<and> 
          x1 \<le> 1 \<and>
          x2 \<ge> 0 \<and>
          x2 \<le> 1 \<longrightarrow>
          \<not> f_ann x1 x2 \<le> (3899 / 3900)
        " sorry
  
  from 1 2 show "?thesis"
    using assms unfolding int_def P_def D_def inRanges_def annRange_def normI_def norm_def int_def
denormI_def normO_def outRanges_def \<epsilon>_def
    apply (simp)
    done    
qed





lemma marabou_combined_results: 
  fixes x1 x2 :: real
  assumes "x1 \<ge> fst(int(1)) \<and> 
          x1 \<le> snd(int(1)) \<and>
          x2 \<ge> fst(int(2)) \<and>
          x2 \<le> snd(int(2))"
  shows "
          \<not> f_ann x1 x2 \<ge> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
           \<and>           
          \<not> f_ann x1 x2 \<le> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>)
" 
proof - 
  have 1: "x1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x1 \<le> normI 1 (inRanges(1).2) \<and>
          x2 \<ge> normI 2 (inRanges(2).1) \<and>   
          x2 \<le> normI 2 (inRanges(2).2) \<longrightarrow> 
          \<not> f_ann x1 x2 \<ge> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
          " sorry
  have 2: "x1 \<ge> normI 1 (inRanges(1).1) \<and> 
          x1 \<le> normI 1 (inRanges(1).2) \<and>
          x2 \<ge> normI 2 (inRanges(2).1) \<and>
          x2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>
          \<not> f_ann x1 x2 \<le> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>)
        " sorry
  from 1 2 show "?thesis" using assms by (simp add: int_def) 
qed


(*Rewrite this using our interval definitions, and f_ann, and spec_f. *)
theorem controller_conformance:
  fixes x_1 x_2 :: real
  assumes 
    (*Assumption on epsilon*)
    "\<epsilon> \<ge> 0" and

    (*Assumptions on the normalisation, that the ranges are well-formed*)
    "\<forall> i :: nat. snd(outRanges ! i) > fst(outRanges ! i) \<and> 
          snd(inRanges ! i) > fst(inRanges ! i) \<and> snd(annRange) > fst(annRange)" and

    (*The assumption on the range of the variables, we need them to be within the defined input ranges. *) 
    "P > 0 \<and> D > 0"  and

    "x_1 \<ge> inRanges(1).1 \<and> 
     x_1 \<le> inRanges(1).2 \<and>
     x_2 \<ge> inRanges(2).1 \<and>
     x_2 \<le> inRanges(2).2"

  
  (*We need to show our goal under a range of our bound input variables. 
    This has to be here, the range assumptions, not as an assumption. *)
  shows " (conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)" 
   apply (rule conf_vcs)  
  (*Discharge first assumption: *)
   apply (simp add: assms(1))

proof - 
  (*Assumption, if we take the ranges of *)
  have 1:"x_1 \<ge> inRanges(1).1 \<and> 
          x_1 \<le> inRanges(1).2 \<and>
          x_2 \<ge> inRanges(2).1 \<and>
          x_2 \<le> inRanges(2).2" using assms by simp
    (*This works: *)
   
  from marabou_evaluated_results[where ?x1.0="normI 1 x_1" and ?x2.0="normI 2 x_2"] have m3: 
          "normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow>

          normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2) \<and>
          \<not> annout 2 1 [normI 1 x_1, normI 2 x_2] \<ge> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
           \<and>
          \<not> annout 2 1 [normI 1 x_1, normI 2 x_2] \<le> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>)"
    by (simp add: int_def)
    
  have "... \<longrightarrow>
  
          normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2) \<and>
   annout 2 1 [normI 1 x_1, normI 2 x_2] \<le> normO 1 ((P * denormI 1 (fst(int(1))) + (D * denormI 2 (fst(int(2)))) ) + \<epsilon>)
     \<and>
    annout 2 1 [normI 1 x_1, normI 2 x_2] \<ge> normO 1 ((P * denormI 1 (snd(int(1))) + (D * denormI 2 (snd(int(2)))) ) - \<epsilon>)"
     using nle_le by blast
     

   have "... \<longrightarrow> 
          normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2) \<and>
     annout 2 1 [normI 1 x_1, normI 2 x_2] \<le> normO 1 (norm_spec_f_2 (fst(int(1))) (fst(int(2))) + \<epsilon>)
     \<and> 
     annout 2 1 [normI 1 x_1, normI 2 x_2] \<ge> normO 1 (norm_spec_f_2 (snd(int(1))) (snd(int(2))) - \<epsilon>)
    "
     unfolding norm_spec_f_2_def
     apply (simp)
     done

   have "... \<longrightarrow> 
    
          normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2) \<and>
     annout 2 1 [normI 1 x_1, normI 2 x_2] \<ge> normO 1 (norm_spec_f_2 (snd(int(1))) (snd(int(2))) - \<epsilon>)
      \<and> 
     annout 2 1 [normI 1 x_1, normI 2 x_2] \<le> normO 1 (norm_spec_f_2 (fst(int(1))) (fst(int(2))) + \<epsilon>)
    "
     apply (simp)
     done
  
  (*Important step, get from the intervals to the actual fixed variables:
    We can still have this, at the moment, be on the normalised ranges.  *)
   have "... \<longrightarrow> 
     annout 2 1 [normI 1 x_1, normI 2 x_2] \<ge> normO 1 (norm_spec_f_2 (normI 1 x_1) (normI 2 x_2) - \<epsilon>)
     \<and> 
     annout 2 1 [normI 1 x_1, normI 2 x_2] \<le> normO 1 (norm_spec_f_2 (normI 1 x_1) (normI 2 x_2) + \<epsilon>)
    "
     apply (rule impI)
     apply (rule spec_mono_ann[where f="f_ann"])
   proof - 
     assume "normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2) \<and>
          annout 2 1 [normI 1 x_1, normI 2 x_2] \<ge> normO 1 (norm_spec_f_2 (snd(int(1))) (snd(int(2))) - \<epsilon>)
      \<and> 
     annout 2 1 [normI 1 x_1, normI 2 x_2] \<le> normO 1 (norm_spec_f_2 (fst(int(1))) (fst(int(2))) + \<epsilon>)"
     show "\<forall> x_1 x_2 y_1 y_2. x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> norm_spec_f_2 x_1 x_2 \<le> norm_spec_f_2 y_1 y_2" 
       using assms apply (simp add: norm_spec_f_2_mono)
       done

     show "fst (int(1)) \<le> normI 1 x_1 \<and> normI 1 x_1 \<le> snd (int(1))"
       by (metis \<open>normI 1 (fst (inRanges(1)\<^sub>s)) \<le> normI 1 x_1 \<and> normI 1 x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> normI 2 x_2 \<and> normI 2 x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<and> normO 1 (norm_spec_f_2 (snd (thm2_TEMP.int(1)\<^sub>s)) (snd (thm2_TEMP.int(2)\<^sub>s)) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (fst (thm2_TEMP.int(1)\<^sub>s)) (fst (thm2_TEMP.int(2)\<^sub>s)) + \<epsilon>)\<close> cancel_comm_monoid_add_class.diff_cancel fst_conv nth_Cons_0 snd_conv thm2_TEMP.int_def)
       

     show "fst (int(2)\<^sub>s) \<le> normI 2 x_2  \<and> normI 2 x_2 \<le> snd (int(2)\<^sub>s)"
       by (metis One_nat_def \<open>normI 1 (fst (inRanges(1)\<^sub>s)) \<le> normI 1 x_1 \<and> normI 1 x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> normI 2 x_2 \<and> normI 2 x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<and> normO 1 (norm_spec_f_2 (snd (thm2_TEMP.int(1)\<^sub>s)) (snd (thm2_TEMP.int(2)\<^sub>s)) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (fst (thm2_TEMP.int(1)\<^sub>s)) (fst (thm2_TEMP.int(2)\<^sub>s)) + \<epsilon>)\<close> diff_Suc_1 nat_1_add_1 nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc split_pairs thm2_TEMP.int_def)
       

    show "0 \<le> \<epsilon>" 
       using assms by simp

     show "fst (outRanges ! 0) < snd (outRanges ! 0) \<and> fst annRange < snd annRange" using assms by simp
        

     show 
     "f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (fst (int(1))) (fst (int(2))) + \<epsilon>) \<and>
      f_ann (normI 1 x_1) (normI 2 x_2) \<ge> normO 1 (norm_spec_f_2 (snd (int(1))) (snd (thm2_TEMP.int(2))) - \<epsilon>)"
       using \<open>normI 1 (fst (inRanges(1)\<^sub>s)) \<le> normI 1 x_1 \<and> normI 1 x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> normI 2 x_2 \<and> normI 2 x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<and> normO 1 (norm_spec_f_2 (snd (thm2_TEMP.int(1)\<^sub>s)) (snd (thm2_TEMP.int(2)\<^sub>s)) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (fst (thm2_TEMP.int(1)\<^sub>s)) (fst (thm2_TEMP.int(2)\<^sub>s)) + \<epsilon>)\<close> by fastforce
       
     qed

     have "... \<longrightarrow> 
      f_ann (normI 1 x_1) (normI 2 x_2) \<ge> normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>) \<and>
      f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>)"
       unfolding norm_spec_f_2_def by simp
    
     have "... \<longrightarrow> 
      denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<ge> denormO 1 (normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>)) \<and>
      denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> denormO 1 (normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>))"
       using assms apply (simp add: mono_denormO)
       by (metis mono_denormO order_le_less)

     have "... \<longrightarrow> 
        denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<ge> (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>) \<and>
        denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>)
        "
       using assms(2) output_norm_2 by presburger 

      have "... \<longrightarrow> 
        denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<ge> (P * x_1 + D * x_2 - \<epsilon>) \<and>
        denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> (P * x_1 + D * x_2 + \<epsilon>)
        "
        using assms(2) input_norm2 by presburger

    have "... \<longrightarrow> 
        \<bar>denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) - (P * x_1 + D * x_2)\<bar> \<le> \<epsilon>
        "
      by linarith

    have goal:"... \<longrightarrow> 
          y_1 = P * x_1 + D * x_2 \<longrightarrow> \<bar>denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) - y_1\<bar> \<le> \<epsilon>
        " by simp

    have goal2:"normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2) \<longrightarrow> y_1 = P * x_1 + D * x_2 \<longrightarrow> \<bar>denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) - y_1\<bar> \<le> \<epsilon>
        "
      using \<open>P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon> \<longrightarrow> P * x_1 + D * x_2 - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> P * x_1 + D * x_2 + \<epsilon>\<close> \<open>denormO 1 (normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>)) \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> denormO 1 (normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>)) \<longrightarrow> P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>\<close> \<open>normI 1 (fst (inRanges(1)\<^sub>s)) \<le> normI 1 x_1 \<and> normI 1 x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> normI 2 x_2 \<and> normI 2 x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (P * denormI 1 (fst (thm2_TEMP.int(1)\<^sub>s)) + D * denormI 2 (fst (thm2_TEMP.int(2)\<^sub>s)) + \<epsilon>) \<and> normO 1 (P * denormI 1 (snd (thm2_TEMP.int(1)\<^sub>s)) + D * denormI 2 (snd (thm2_TEMP.int(2)\<^sub>s)) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<longrightarrow> normI 1 (fst (inRanges(1)\<^sub>s)) \<le> normI 1 x_1 \<and> normI 1 x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> normI 2 x_2 \<and> normI 2 x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (fst (thm2_TEMP.int(1)\<^sub>s)) (fst (thm2_TEMP.int(2)\<^sub>s)) + \<epsilon>) \<and> normO 1 (norm_spec_f_2 (snd (thm2_TEMP.int(1)\<^sub>s)) (snd (thm2_TEMP.int(2)\<^sub>s)) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2)\<close> \<open>normI 1 (fst (inRanges(1)\<^sub>s)) \<le> normI 1 x_1 \<and> normI 1 x_1 \<le> normI 1 (snd (inRanges(1)\<^sub>s)) \<and> normI 2 (fst (inRanges(2)\<^sub>s)) \<le> normI 2 x_2 \<and> normI 2 x_2 \<le> normI 2 (snd (inRanges(2)\<^sub>s)) \<and> normO 1 (norm_spec_f_2 (snd (thm2_TEMP.int(1)\<^sub>s)) (snd (thm2_TEMP.int(2)\<^sub>s)) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (fst (thm2_TEMP.int(1)\<^sub>s)) (fst (thm2_TEMP.int(2)\<^sub>s)) + \<epsilon>) \<longrightarrow> normO 1 (norm_spec_f_2 (normI 1 x_1) (normI 2 x_2) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (normI 1 x_1) (normI 2 x_2) + \<epsilon>)\<close> \<open>normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>) \<longrightarrow> denormO 1 (normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>)) \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> denormO 1 (normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>))\<close> \<open>normO 1 (norm_spec_f_2 (normI 1 x_1) (normI 2 x_2) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (norm_spec_f_2 (normI 1 x_1) (normI 2 x_2) + \<epsilon>) \<longrightarrow> normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>)\<close> m3 by argo

    from 1 have goal3:"normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2)"
      by (smt (verit) assms(2) mono_normI)


    show "y_1 = P * x_1 + D * x_2 \<longrightarrow> \<bar>denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) - y_1\<bar> \<le> \<epsilon>"
      using goal2 goal3 by fastforce


  qed

end
