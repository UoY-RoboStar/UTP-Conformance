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
(*This must be a strengthening, because it is about the patterns, it is a predicate 
on a vector space, that is stronger than the UTP patterns. *)
theorem conf_vcs:
  fixes x_1 x_2 y_1 :: real
assumes "\<epsilon> \<ge> 0" and 
  "(y_1 = (P * x_1) + (D * x_2)) \<longrightarrow>
             \<bar>(denormO 1 (annout 2 1 [(normI 1 x_1), (normI 2 x_2)]) ) - y_1 \<bar> \<le> \<epsilon>"
shows "(conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C)"
  sorry


(*This is a shorthand for the specification function for our example, 
with the denormilisation applied, to help with reasoning.  *)

definition normSpec :: "real \<Rightarrow> real \<Rightarrow> real" where 
"normSpec x_1 x_2 = 
  (P * denormI 1 (x_1) + (D * denormI 2 (x_2)) )"

lemma normSpec_mono: 
  fixes x_1 :: real and x_2 :: real and y_1 :: real and y_2 :: real
  assumes "P > 0" and "D > 0" and 
    "(snd(inRanges(1)) > fst(inRanges(1)) \<and> snd(inRanges(2)) > fst(inRanges(2)) \<and> snd(annRange) > fst(annRange))"
  shows "x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> (normSpec x_1 x_2) \<le> (normSpec y_1 y_2)"
  using assms apply (simp add: mono_denormI mono_norm normSpec_def mono_normI
            ordered_ab_semigroup_add_class.add_mono)
  by (smt (verit, ccfv_SIG) One_nat_def assms(3) mono_denormI mult_left_mono)
  
(*Interval definition: *)
definition normRanges :: "(real \<times> real) list" where
"normRanges = [ ((normI 1 (inRanges(1).1)), ((normI 1 (inRanges(1).2)))), 
         ((normI 2 (inRanges(2).1)), ((normI 2 (inRanges(2).2)))) ]"

(*Using FST for MIN and SND for MAX, when encoding the normRangeservals. *)
term "fst(normRanges(1))"
term "fst(normRanges(2))"
term "snd(normRanges(1))"
term "snd(normRanges(2))"

(*Abbreviation for readability, referring to the f_ann as annout 2 1 to correspond 
to the last layer of our example: 
We only ever refer to the function of an ann, *)
abbreviation "f_ann x y \<equiv> annout 2 1 [x,y]"

term "f_ann 0 0"

lemma spec_mono_ann:
  fixes x_1 x_2 :: real and
        S :: "real \<Rightarrow> real \<Rightarrow> real" and 
        f :: "real \<Rightarrow> real \<Rightarrow> real" 
  assumes 
          "fst(normRanges(1)) \<le> x_1 \<and> x_1 \<le> snd(normRanges(1))" and 
          "fst(normRanges(2)) \<le> x_2 \<and> x_2 \<le> snd(normRanges(2))" and 
          "(snd(outRanges ! 0) > fst(outRanges ! 0) \<and> snd(annRange) > fst(annRange))" and
          "\<epsilon> \<ge> 0" and 
          (*Monotonicity property for our specification function: *)
          "\<forall> x_1 x_2 y_1 y_2 :: real. x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> S x_1 x_2 \<le> S y_1 y_2"
        shows "
              f x_1 x_2 \<le> normO 1 (S (fst(normRanges(1))) (fst(normRanges(2))) + \<epsilon>)
               \<and> f x_1 x_2 \<ge> normO 1 (S (snd(normRanges(1))) (snd(normRanges(2))) - \<epsilon>) 
              \<Longrightarrow>
               f x_1 x_2 \<ge> (normO 1 (S (x_1) (x_2) - \<epsilon>)) \<and>
               f x_1 x_2 \<le> (normO 1 (S (x_1) (x_2) + \<epsilon>)) 
                "
proof (rule conjI)
  assume a1:"f x_1 x_2 \<le> normO 1 (S (fst(normRanges(1))) (fst(normRanges(2))) + \<epsilon>)
               \<and> f x_1 x_2 \<ge> normO 1 (S (snd(normRanges(1))) (snd(normRanges(2))) - \<epsilon>) 
              "

  have 1: "f x_1 x_2 \<le> normO 1 (S (fst(normRanges(1))) (fst(normRanges(2))) + \<epsilon>)" using a1 by simp 
  have 2: "f x_1 x_2 \<ge> normO 1 (S (snd(normRanges(1))) (snd(normRanges(2))) - \<epsilon>)" using a1 by simp

  (*GOAL 1: first conjunct of the goal: *)
  from assms(1) assms(2) have "x_1 \<ge> fst(normRanges(1)) \<and> x_2 \<ge> fst(normRanges(2))" by simp
  have "... = 
        ((S x_1 x_2) \<ge> (S (fst(normRanges(1))) (fst(normRanges(2)))))" 
    using assms by simp
  have "... = 
        ((S x_1 x_2) + \<epsilon> \<ge> (S (fst(normRanges(1))) (fst(normRanges(2)))) + \<epsilon>)"
    by simp
  have c1:"... = 
        (normO 1 ((S x_1 x_2) + \<epsilon>) \<ge> normO 1 ((S (fst(normRanges(1))) (fst(normRanges(2)))) + \<epsilon>))"
    using assms 
    apply (simp add: mono_normO)
    by (smt (verit, ccfv_SIG) diff_Suc_1 mono_normO)
  from 1 c1 show "f x_1 x_2 \<le> normO 1 ((S x_1 x_2) + \<epsilon>)"
    using \<open>(fst (normRanges(2)\<^sub>s) \<le> x_2) = (S (fst (normRanges(1)\<^sub>s)) (fst (normRanges(2)\<^sub>s)) \<le> S x_1 x_2)\<close> \<open>fst (normRanges(1)\<^sub>s) \<le> x_1 \<and> fst (normRanges(2)\<^sub>s) \<le> x_2\<close> by argo
    
  (*Goal 2: second cojunct of the goal: *)
  from assms(1) assms(2) have "x_1 \<le> snd(normRanges(1)) \<and> x_2 \<le> snd(normRanges(2))" by simp
  have "... = 
        ((S x_1 x_2) \<le> (S (snd(normRanges(1))) (snd(normRanges(2)))))" 
    using assms by simp
  have "... = 
        ((S x_1 x_2) - \<epsilon> \<le> (S (snd(normRanges(1))) (snd(normRanges(2)))) - \<epsilon>)"
    by simp
  have c2: "... = (normO 1 ((S x_1 x_2) - \<epsilon>) \<le> normO 1 ((S (snd(normRanges(1))) (snd(normRanges(2)))) - \<epsilon>))"
    using assms 
    apply (simp add: mono_normO)
    by (smt (verit, ccfv_SIG) diff_Suc_1 mono_normO)
  from 2 c2 show "f x_1 x_2 \<ge> (normO 1 (S (x_1) (x_2) - \<epsilon>))"
    using \<open>(x_2 \<le> snd (normRanges(2)\<^sub>s)) = (S x_1 x_2 \<le> S (snd (normRanges(1)\<^sub>s)) (snd (normRanges(2)\<^sub>s)))\<close> assms(2) by argo
    
  qed

(*Marabou combined results: *)

(*This assumes that Marabou returns UNSAT, as is the desired result. 
If Marabou returns SAT, a counterexample, currently, we will choose another epsilon
such that this holds. *)

(*We need to evaluate both: *)
term "inRanges"


(*The idea is, we have 2 facts that are evaluated expressions, that we use 
to show the truth of symbolic expressions, with constant definitions

That we can then reason about the fst normRanges, etc, algebriacally within Isabelle.

But we only prove the evaluated expressions, it only works if we instantiate 
the constants but this is fine. *)

(*Evaluated expressions, for Marabou translation: *)
value "fst(normRanges(1))"
value "snd(normRanges(1))"
value "fst(normRanges(2))"
value "snd(normRanges(2))"
value "normO 1 ((P * denormI 1 (fst(normRanges(1))) + (D * denormI 2 (fst(normRanges(2)))) ) + \<epsilon>)"
value "normO 1 ((P * denormI 1 (snd(normRanges(1))) + (D * denormI 2 (snd(normRanges(2)))) ) - \<epsilon>)"

(*We need to have a strategy for the splits, automatically. 
we already have normRanges, meaningless without the splits. 

We need it to be automatic, automated evaluation as well. 

Apply eval, eval doesn't pause halfway through, solves goal through 
evaluation, we don't want this. evaluating, partial evaluation ? 
*)




(*

The function we need to instantiate is; 

(P * denormI 1 (x_1) + (D * denormI 2 (x_2)))

This is normSpec, f needs to be NORM_SPEC. 

*)                        
lemma marabou_results: 
  fixes x1 x2 :: real and f :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes 
    "x1 \<ge> fst(normRanges(1)) \<and> x1 \<le> snd(normRanges(1)) \<and>
     x2 \<ge> fst(normRanges(2)) \<and> x2 \<le> snd(normRanges(2))" and
    "(snd(outRanges ! 0) > fst(outRanges ! 0) \<and> snd(annRange) > fst(annRange))" and
    "\<epsilon> \<ge> 0" and 
    (*Monotonicity property for our specification function: *)
    "\<forall> x_1 x_2 y_1 y_2 :: real. x_1 \<le> y_1 \<and> x_2 \<le> y_2 \<longrightarrow> normSpec x_1 x_2 \<le> normSpec y_1 y_2" and 
    "f = normSpec" 

  shows 
      "\<not> f_ann x1 x2 \<ge> normO 1 ( f x1 x2 + \<epsilon>)
       \<and>           
       \<not> f_ann x1 x2 \<le> normO 1 ( f x1 x2 - \<epsilon>)" 
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
  
  from 1 2 have "x1 \<ge> fst(normRanges(1)) \<and>
       x1 \<le> snd(normRanges(1)) \<and>
       x2 \<ge> fst(normRanges(2)) \<and>
       x2 \<le> snd(normRanges(2))
       \<longrightarrow> 
       \<not> f_ann x1 x2 \<ge> normO 1 ( f (fst(normRanges(1))) (fst(normRanges(2))) + \<epsilon>)
       \<and>           
       \<not> f_ann x1 x2 \<le> normO 1 ( f (snd(normRanges(1))) (snd(normRanges(2))) - \<epsilon>)"
    using assms unfolding normRanges_def P_def D_def inRanges_def annRange_def normI_def norm_def normRanges_def
denormI_def normO_def outRanges_def \<epsilon>_def normSpec_def
    apply (simp)
    done    
  then show "?thesis" 
    using assms
    by (smt (verit, ccfv_SIG) cancel_comm_monoid_add_class.diff_cancel mono_normO) 
qed

(*Splits work*)

(*Interval definition: 
General definitions should be implemented as a function not a list.*)
definition normRanges_gen :: "nat \<Rightarrow> (real \<times> real)" where
"normRanges_gen = (\<lambda> n :: nat. 
            ((normI n (fst(inRanges(n)))), ((normI n (snd(inRanges(n)))))))"

(*1d int split. for a single interval lower and upper bounds: *)
definition intEval :: "nat list \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> (real \<times> real))" where
"intEval ints noInt = (\<lambda> n :: nat. 
                    ( fst((normRanges_gen n)) + ((ints(n) :: real) * (snd((normRanges_gen n)) / noInt)), 
                    fst((normRanges_gen n)) + ((ints(n) + 1 :: real) * (snd((normRanges_gen n)) / noInt)) ))"

term "intEval ints noInt"
term "fst \<circ> (intEval ints noInt)"

(*Rewrite this using our normRangeserval definitions, and f_ann, and spec_f. *)
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

proof - 

  have 1:"normI 1 x_1 \<ge> normI 1 (inRanges(1).1) \<and> 
          normI 1 x_1 \<le> normI 1 (inRanges(1).2) \<and>
          normI 2 x_2 \<ge> normI 2 (inRanges(2).1) \<and>
          normI 2 x_2 \<le> normI 2 (inRanges(2).2)"
      by (smt (verit) assms(2) assms(4) mono_normI)

    from marabou_results[where ?x1.0="normI 1 x_1" and ?x2.0="normI 2 x_2"] 1 have marabou:
        "(f_ann (normI 1 x_1) (normI 2 x_2) \<ge> normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon>)
         \<and> 
         f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>))"
      by (simp add: assms(1) assms(2) assms(3) normRanges_def normSpec_mono snd_conv)
             
    have
     "(f_ann (normI 1 x_1) (normI 2 x_2) \<ge> normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon>)
         \<and> 
         f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>)) = 
      (denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<ge> denormO 1 (normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon>)) \<and>
      denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> denormO 1 (normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>)))"
      using assms apply (simp add: mono_denormO)
      by (smt (verit) mono_denormO)

   also have "... = 
      (denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<ge> normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon> \<and>
      denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>)"
      using assms by (simp add: output_norm_2)

   also have "... = 
      (denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<ge> (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon>) \<and>
      denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>))"
     by (simp only: normSpec_def)

   also have "... = 
      (denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<ge> (P * x_1 + D * x_2 - \<epsilon>) \<and>
      denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> (P * x_1 + D * x_2 + \<epsilon>))"
     using assms by (simp add: output_norm_2 input_norm2)

    also have "... = 
        (\<bar>denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) - (P * x_1 + D * x_2)\<bar> \<le> \<epsilon>)
        "
      by argo
      
    also have "... = 
        ((y_1 = (P * x_1) + (D * x_2)) \<longrightarrow>
             (\<bar>(denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) ) - y_1 \<bar> \<le> \<epsilon>))"
      using calculation marabou by fastforce
      
    (*This is deriving 2 by drawing in all calculational reasoning, and m3, to show that
    this is true. This should be done with also and finally, but that is failing beyond three steps ? *)    
    finally show "conf_sin \<epsilon> angleOutputE AnglePIDANN AnglePID_C"
    proof -
      have 1: "\<epsilon> \<ge> 0" by (simp only: assms(1))
      have 2:"(y_1 = (P * x_1) + (D * x_2)) \<longrightarrow>
             (\<bar>(denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) ) - y_1 \<bar> \<le> \<epsilon>)"
        using \<open>(P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>) = (P * x_1 + D * x_2 - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> P * x_1 + D * x_2 + \<epsilon>)\<close> \<open>(P * x_1 + D * x_2 - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> P * x_1 + D * x_2 + \<epsilon>) = (\<bar>denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) - (P * x_1 + D * x_2)\<bar> \<le> \<epsilon>)\<close> \<open>(denormO 1 (normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon>)) \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> denormO 1 (normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>))) = (normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>)\<close> \<open>(normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon>) \<le> f_ann (normI 1 x_1) (normI 2 x_2) \<and> f_ann (normI 1 x_1) (normI 2 x_2) \<le> normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>)) = (denormO 1 (normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon>)) \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> denormO 1 (normO 1 (normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>)))\<close> \<open>(normSpec (normI 1 x_1) (normI 2 x_2) - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> normSpec (normI 1 x_1) (normI 2 x_2) + \<epsilon>) = (P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) - \<epsilon> \<le> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<and> denormO 1 (f_ann (normI 1 x_1) (normI 2 x_2)) \<le> P * denormI 1 (normI 1 x_1) + D * denormI 2 (normI 2 x_2) + \<epsilon>)\<close> marabou by presburger
       from 1 2 show "conf_sin \<epsilon> context_ch.angleOutputE AnglePIDANN AnglePID_C"
        apply (rule conf_vcs)
        done
    qed
  qed
end