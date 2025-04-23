section \<open> (Temp) Theorem 2 Preliminaries \<close>

theory thm2_prelims_TEMP
  imports 
    "utp_sfrd_conf" 
begin   

text \<open>This file contains an implementation of the prelimaries for proving Theorem 2 in the Segway Conformance Report. 
      This is a temporary file as eventually I will merge this into 'utp_ann_defs' to have a consistent account of 
      all constants, functions, and patterns we need to automate the proof of ANNs. This is made to communicate 
      the basic definitions, those I need for Theorem 2, in a presentable way.  \<close>

section \<open> Constant Declarations \<close>

text \<open>These are the constants of our ANN semantics, the constants we have specified in Z in the translation rules
      for ANN components, see the RoboSapiens D1.1 report, Rule 3 in Section 3.4. 
      We omit layerInput here because we don't require this constant for verification. \<close>

subsection \<open> Basic ANN Constants \<close>

consts layerSizeC :: "nat \<Rightarrow> nat" 
       insizeC :: nat 
       outsizeC :: nat
       layerStructureC :: "nat list"
       layerNoC :: nat 
       weightsC :: "real list list list"
       biasesC :: "real list list" 


definition layerSize :: "nat \<Rightarrow> nat" where
"layerSize x = x"

definition insize :: "nat" where
"insize = 2"

definition outsize :: "nat" where
"outsize = 1"

definition layerstructure :: "nat list" where
"layerstructure = [1,1]"

definition layerNo :: "nat"  where
"layerNo = 2"

definition maxSize :: "nat" where
"maxSize = 1"

definition weights :: "real list list list" where
"weights = [[[1.22838,0.132874]], [[0.744636]]]"

definition biases :: "real list list" where 
"biases = [[0.125424], [-0.107753]]"

definition inRanges :: "(real \<times> real) list" where
"inRanges = [(-30,30), (-250,250)]" 

definition outRanges :: "(real \<times> real) list" where
"outRanges = [(-1950, 1950)]" 

definition annRange :: "(real \<times> real)" where
"annRange = (0,1)" 

fun relu :: "real \<Rightarrow> real" where
"relu x = max x 0"

lemma "x \<ge> 0 \<Longrightarrow> relu x = x" by (simp)
lemma "x < 0 \<Longrightarrow> relu x = 0" by (simp)

subsection \<open> Normalisation \<close>

text \<open> These are the definitions of the functions and constants we need to define normalsiation. This means we 
       can support normalisation defined on the level of RoboChart, enabling a fully automated approach including
       normalisation. While not strictly necesssary for ANN verification, we include these definitions as more of an 
       engineering consideration to build a tool which is simpler to use. \<close>

text \<open> Definition 4 mechanisation (from report) \<close>

(*
locale thm2 =
  fixes inRanges :: "(real \<times> real) list"
  and outRanges :: "(real \<times> real) list"
  and annRange :: "(real \<times> real)"*)

consts inRangesC :: "(real \<times> real) list"
       outRangesC :: "(real \<times> real) list"
       annRangeC :: "(real \<times> real)"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
"norm val oldrange newrange = (((val - fst(oldrange)) / (snd(oldrange) - fst(oldrange))) 
                              * (snd(newrange) - fst(newrange))) + fst(newrange) "

definition normI :: "nat \<Rightarrow> real \<Rightarrow> real" where
"normI i x = (norm x (inRanges(i)) annRange)"

definition normO :: "nat \<Rightarrow> real \<Rightarrow> real" where
"normO i x = (norm x (outRanges(i)) annRange)"

definition denormI :: "nat \<Rightarrow> real \<Rightarrow> real" where
"denormI i x = (norm x annRange (inRanges(i)))"

definition denormO :: "nat \<Rightarrow> real \<Rightarrow> real" where
"denormO i x = (norm x annRange (outRanges(i)))"

text \<open> Lemma 1 mechanisation \<close>

lemma mono_norm: 
  assumes  "(snd(r) > fst(r) \<and> snd(r') > fst(r'))"
  shows "x < y \<Longrightarrow> (norm x r r')  < (norm y r r')"
  apply (simp add: norm_def)
  by (simp add: assms divide_strict_right_mono)

lemma mono_normO: 
  assumes "(snd(outRanges(n)) > fst(outRanges(n)) \<and> snd(annRange) > fst(annRange))"
  shows "x < y \<Longrightarrow> (normO n x)  < (normO n y)"
  using assms apply (simp add: normO_def mono_norm)
  done

lemma mono_normI: 
  assumes "(snd(inRanges(n)) > fst(inRanges(n)) \<and> snd(annRange) > fst(annRange))"
  shows "x < y \<Longrightarrow> (normI n x)  < (normI n y)"
  using assms apply (simp add: normI_def mono_norm)
  done

lemma mono_denormO: 
  assumes "(snd(outRanges(n)) > fst(outRanges(n)) \<and> snd(annRange) > fst(annRange))"
  shows "x < y \<Longrightarrow> (denormO n x)  < (denormO n y)"
  using assms apply (simp add: denormO_def mono_norm)
  done

lemma mono_denormI: 
  assumes "(snd(inRanges(n)) > fst(inRanges(n)) \<and> snd(annRange) > fst(annRange))"
  shows "x < y \<Longrightarrow> (denormI n x)  < (denormI n y)"
  using assms apply (simp add: denormI_def mono_norm)
  done
  
  

text \<open> Lemma 2 mechanisation \<close>

lemma norm_lem_1: "(snd(r) > fst(r) \<and> snd(r') > fst(r'))
       \<Longrightarrow> norm (norm x r r') r' r = x" by (simp add: norm_def)

text \<open> Lemma 3 mechanisation \<close>

lemma output_norm:
  fixes i :: "nat" and x :: "real"
  assumes "\<forall> i . snd(outRanges ! i) > fst(outRanges ! i) \<and> snd(annRange) > fst(annRange)"
  shows "normO i (denormO i x) = x" unfolding denormO_def normO_def
  apply (simp add: assms norm_lem_1)
  done

lemma output_norm_2:
  fixes i :: "nat" and x :: "real"
  assumes "\<forall> i . snd(outRanges ! i) > fst(outRanges ! i) \<and> snd(annRange) > fst(annRange)"
  shows "denormO i (normO i x) = x" unfolding denormO_def normO_def
  apply (simp add: assms norm_lem_1)
  done

text \<open> Lemma 4 mechanisation \<close>

lemma input_norm:
  fixes i :: "nat" and x :: "real"
  assumes "\<forall> i . snd(inRanges ! i) > fst(inRanges ! i) \<and> snd(annRange) > fst(annRange)"
  shows "normI i (denormI i x) = x" unfolding denormI_def normI_def
  apply (simp add: assms norm_lem_1)
  done


lemma input_norm2:
  fixes i :: "nat" and x :: "real"
  assumes "\<forall> i . snd(inRanges ! i) > fst(inRanges ! i) \<and> snd(annRange) > fst(annRange)"
  shows "denormI i (normI i x) = x" unfolding denormI_def normI_def
  apply (simp add: assms norm_lem_1)
  done

text \<open> These distributivity lemmas are not required for theorem 2, and are not on the document, but they could help with 
       enabling automated evaluation of normalisation parameters. \<close>

lemma norm_dist_1 : 
  assumes "(snd(r) > fst(r) \<and> snd(r') > fst(r')) \<and> 
    fst(r) = 0 \<and>
    (x \<ge> fst(r) \<and> x \<le> snd(r)) \<and>
    (y \<ge> fst(r) \<and> y \<le> snd(r))"
    shows "norm (x - y) r r' = ((norm x r r') - (norm y r r')) + fst r'"
  using assms apply (simp add: norm_def)
  by (simp add: diff_divide_distrib left_diff_distrib)

lemma norm_dist_2 : 
  assumes "(snd(r) > fst(r) \<and> snd(r') > fst(r')) \<and> 
fst(r) = 0 \<and>
(x \<ge> fst(r) \<and> x \<le> snd(r)) \<and>
(y \<ge> fst(r) \<and> y \<le> snd(r))"
    shows "norm (x + y) r r' = ((norm x r r') + (norm y r r')) - fst r'"
  using assms apply (simp add: norm_def)
  by (simp add: add_divide_distrib ring_class.ring_distribs(2))


section \<open> ANN Output Function \<close>

text \<open> We present out implementation of annout, Definition 3 in the Segway Conformance Report, below. 
      This is also used in the ANN pattern, but we will work on the patterns after this proof is automated.\<close>

text \<open> These are basic functions needed because we define annout as operating on traces (lists of real numbers)\<close>

fun fun_to_list :: "nat \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'b list" where
"fun_to_list 0 f = []" |
"fun_to_list i f = fun_to_list (i-1) f @ [f (i)]"

lemma len_f2l: "#fun_to_list n f = n" by (induct n ; simp)

fun dotprod :: "(real list \<times> real list) \<Rightarrow> real" where
"dotprod ([], []) = 0" |
"dotprod (x # xs, y # ys) = (x * y) + dotprod(xs, ys)"

fun annout :: "nat \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> real" where
"annout 0 n ins = ins(n)" | 
"annout l n ins = relu( dotprod ( (fun_to_list (layerSize(l-1)) (rel_apply ({(pn, annout (l-1) (pn) (ins)) | pn. pn \<in> {1..layerSize (l-1)}})) ) ,
                       (weights l n) ) + (biases l n))" 

section \<open> AnglePIDANN parameter instantiations \<close>


end
