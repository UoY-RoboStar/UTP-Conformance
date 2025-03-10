theory UTPANN_Proofs
  imports 
    "UTP_ANN_Defs"
begin   

full_exprs


(*Lemma B.1, necessary for Theorem 4.4*)
lemma layeroutput_nodeoutput_link :
  fixes input :: "real list" and l :: "nat" and n :: nat
  shows "layeroutput ((inv dropseq) input) (l,n) = 
      dist_concat (#input) ({ (i, [evparam layerRes (0, i, input(i))]) | i . i \<in> {1..(#input) }  }) @ 
      dist_concat (l-1)  ({ (i, dist_concat (layerSize(i)) ({ (j, [nodeoutput i j input]) | j::nat. j \<in> {1..layerSize(i)} }) ) | i::nat. i \<in> {1..(l-1)} }) @
      dist_concat (n) ({ (i, [nodeoutput l i input]) | i. i \<in> {1..n}})
      " 
  sorry

(*Normalisation lemmas:*)

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
"norm val oldrange newrange = (((val - fst(oldrange)) / (snd(oldrange) - fst(oldrange))) 
                              * (snd(newrange) - fst(newrange))) + fst(newrange) "

lemma mono_norm: 
  assumes  "(snd(r) > fst(r) \<and> snd(r') > fst(r'))"
  shows "x < y \<Longrightarrow> (norm x r r')  < (norm y r r')"
  apply (simp add: norm_def)
  by (simp add: assms divide_strict_right_mono)
  

lemma norm_lem_1: "(snd(r) > fst(r) \<and> snd(r') > fst(r'))
       \<Longrightarrow> norm (norm x r r') r' r = x" by (simp add: norm_def)


value "denormOut 1 (0.085)"

value "denormOut 1 (0.5)"

(*Normalisation distributivity, under subtraction*)

lemma norm_dist_1 : 
  assumes "(snd(r) > fst(r) \<and> snd(r') > fst(r'))
\<and> 
fst(r) = 0 \<and>
(x \<ge> fst(r) \<and> x \<le> snd(r)) \<and>
(y \<ge> fst(r) \<and> y \<le> snd(r))"
    shows "
norm (x - y) r r' = ((norm x r r') - (norm y r r')) + fst r'"
  using assms apply (simp add: norm_def)
  by (simp add: diff_divide_distrib left_diff_distrib)

lemma norm_dist_2 : 
  assumes "(snd(r) > fst(r) \<and> snd(r') > fst(r'))
\<and> 
fst(r) = 0 \<and>
(x \<ge> fst(r) \<and> x \<le> snd(r)) \<and>
(y \<ge> fst(r) \<and> y \<le> snd(r))"
    shows "
norm (x + y) r r' = ((norm x r r') + (norm y r r')) - fst r'"
  using assms apply (simp add: norm_def)
  by (simp add: add_divide_distrib ring_class.ring_distribs(2))



definition inRanges :: "(real \<times> real) list" where
"inRanges = [(-30,30), (-250,250)]" 

definition outRanges :: "(real \<times> real) list" where
"outRanges = [(-1950, 1950)]" 

definition annRange :: "(real \<times> real)" where
"annRange = (0,1)" 

fun normSeq :: "real list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list \<Rightarrow> real list" where
"normSeq [] oldranges newranges = []" |
"normSeq (x#xs) oldranges newranges = (normSeq xs oldranges newranges) @
                                      [norm x (oldranges(#(x#xs))) (newranges(#(x#xs)))] "

fun normInSeq :: "real list \<Rightarrow> real list" where
"normInSeq [] = []" |
"normInSeq (x#xs) = (normInSeq xs) @ [norm x (inRanges(#(x#xs))) annRange] "

fun normOutSeq :: "real list \<Rightarrow> real list" where
"normOutSeq [] = []" |
"normOutSeq (x#xs) = (normOutSeq xs) @ [norm x (outRanges(#(x#xs))) annRange] "

fun denormInSeq :: "real list \<Rightarrow> real list" where
"denormInSeq [] = []" |
"denormInSeq (x#xs) = (denormInSeq xs) @ [norm x annRange (inRanges(#(x#xs)))] "

fun denormOutSeq :: "real list \<Rightarrow> real list" where
"denormOutSeq [] = []" |
"denormOutSeq (x#xs) = (denormOutSeq xs) @ [norm x annRange (outRanges(#(x#xs)))] "

definition normIn :: "nat \<Rightarrow> real \<Rightarrow> real" where
"normIn i x = (norm x (inRanges(i)) annRange)"

definition normOut :: "nat \<Rightarrow> real \<Rightarrow> real" where
"normOut i x = (norm x (outRanges(i)) annRange)"

definition denormIn :: "nat \<Rightarrow> real \<Rightarrow> real" where
"denormIn i x = (norm x annRange (inRanges(i)))"

definition denormOut :: "nat \<Rightarrow> real \<Rightarrow> real" where
"denormOut i x = (norm x annRange (outRanges(i)))"

definition epsilon_marabou :: "real" where 
"epsilon_marabou = ( (denormOut 1 0.017 ) - (outRanges(1).1) )"

value "epsilon_marabou"


lemma 
  fixes i :: "nat"
  assumes "x \<ge> 0 \<and> x \<le> 1"
  shows "\<forall> i \<in> {1,2}. normIn i (denormIn i x) = x"  
  apply (simp add: normIn_def denormIn_def annRange_def outRanges_def)
  apply (rule conjI)
   apply (rule norm_lem_1)
   apply (simp add: inRanges_def annRange_def)
  apply (simp add: annRange_def inRanges_def norm_lem_1)
  done

lemma 
  fixes i :: "nat"
  assumes "i \<le> 2" and "x \<ge> -30 \<and> x \<le> 30"
  shows "\<forall> i \<in> {1,2}. denormIn i (normIn i x) = x"  
  apply (simp add: normIn_def denormIn_def )
  apply (rule conjI)
   apply (rule norm_lem_1)
   apply (simp add: inRanges_def annRange_def)
  apply (simp add: annRange_def inRanges_def norm_lem_1)
  done
  
  

lemma norm_denorm_in:
  fixes x::"real"
  assumes "x \<ge> 0 \<and> x \<le> 1"
  shows "\<forall> i \<in> {1,2}. normIn i (denormIn i x) = denormIn i (normIn i x)"
  by (simp add: annRange_def inRanges_def denormIn_def normIn_def norm_lem_1 nth_Cons_0)


lemma norm_deoutRanges:
  fixes x::"real"
  assumes "x \<ge> 0 \<and> x \<le> 1"
  shows "\<forall> i \<in> {1}. normOut i (denormOut i x) = denormOut i (normOut i x)"
  by (simp add: annRange_def outRanges_def denormOut_def normOut_def norm_lem_1)

consts input :: "ann_ch list"
consts p :: "(real list \<times> real list) \<Rightarrow> bool"

abbreviation "Q\<^sub>2 \<equiv> (peri\<^sub>R (ANNPattern (set (input))))"
abbreviation "Q\<^sub>3 \<equiv> (post\<^sub>R (ANNPattern (set (input))))"
abbreviation "P\<^sub>2 \<equiv> (peri\<^sub>R (CyclicRCController insize outsize p))"
abbreviation "P\<^sub>3 \<equiv> (post\<^sub>R (CyclicRCController insize outsize p))"

definition ANN_rename :: "ann_ch \<leftrightarrow> c" where
"ANN_rename = {(build\<^bsub>layerRes\<^bold>.0\<^esub> (n,x), build\<^bsub>inp\<^esub> (n, (x))) | n x . True} \<union>
            {(build\<^bsub>layerRes\<^bold>.layerNo\<^esub> (n,x), build\<^bsub>out\<^esub> (n, (x))) | n x . True}"

theorem conformance_conditions_anns: 
  shows "(Approx \<epsilon> out P\<^sub>2) \<sqsubseteq> ((Q\<^sub>2 \<Zhide>\<^sub>r (ANNHiddenEvts)) \<lbrakk>ANN_rename\<rbrakk>\<^sub>r ) 
              \<and> 
         (Approx \<epsilon> out P\<^sub>3) \<sqsubseteq> ((Q\<^sub>3 \<Zhide>\<^sub>r (ANNHiddenEvts)) \<lbrakk>ANN_rename\<rbrakk>\<^sub>r ) \<Longrightarrow>
 
         cconf \<epsilon> (((ANNPattern (set (input))) \<Zhide>\<^sub>r (ANNHiddenEvts)) \<lbrakk>ANN_rename\<rbrakk>\<^sub>r) (CyclicRCController insize outsize p)"
  sorry 

lemma vector_link_post: 
  shows "\<not> ( \<exists> inseq. (\<exists> outseq. p (inseq, outseq) \<and> (\<exists> i \<in> {1::nat..outsize}.
            (
              ({ annoutput layerNo i inseq } \<inter> {x | x::real. \<bar>x - outseq(i)\<bar> \<le> \<epsilon>} ) = {}
            )
          ))) \<Longrightarrow> (Approx \<epsilon> out P\<^sub>3) \<sqsubseteq> ((Q\<^sub>3 \<Zhide>\<^sub>r (ANNHiddenEvts)) \<lbrakk>ANN_rename\<rbrakk>\<^sub>r)" sorry

lemma vector_link_peri: 
  shows "\<not> ( \<exists> inseq. (\<exists> outseq. p (inseq, outseq) \<and> (\<exists> i \<in> {1::nat..outsize}.
            (
              ({ annoutput layerNo i inseq } \<inter> {x | x::real. \<bar>x - outseq(i)\<bar> \<le> \<epsilon>} ) = {}
            )
          ))) \<Longrightarrow> (Approx \<epsilon> out P\<^sub>2) \<sqsubseteq> ((Q\<^sub>2 \<Zhide>\<^sub>r (ANNHiddenEvts)) \<lbrakk>ANN_rename\<rbrakk>\<^sub>r )" sorry

(*This is Theorem 4.4 from my Thesis, encoded with the \<le> instead of < because of the new conformance.*)
theorem vector_link:
  fixes \<epsilon> :: "real"
  assumes "\<epsilon> \<ge> 0"
  shows "
        \<not> ( \<exists> inseq. (\<exists> outseq. p (inseq, outseq) \<and> (\<exists> i \<in> {1::nat..outsize}.
            (
              ({ annoutput layerNo i inseq } \<inter> {x | x::real. \<bar>x - outseq(i)\<bar> \<le> \<epsilon>} ) = {}
            )
          )))
          \<Longrightarrow> (Approx \<epsilon> out P\<^sub>2) \<sqsubseteq> ((Q\<^sub>2 \<Zhide>\<^sub>r (ANNHiddenEvts)) \<lbrakk>ANN_rename\<rbrakk>\<^sub>r ) 
              \<and> 
              (Approx \<epsilon> out P\<^sub>3) \<sqsubseteq> ((Q\<^sub>3 \<Zhide>\<^sub>r (ANNHiddenEvts)) \<lbrakk>ANN_rename\<rbrakk>\<^sub>r )"
  by (simp add: vector_link_peri vector_link_post)


(*Definitions: *)

consts \<epsilon> :: "real"

definition ANN :: "(ann_ch, 'a) circus_alpha hrel" where 
"ANN = ((ANNPattern (set (input))) \<Zhide>\<^sub>r (ANNHiddenEvts))"


definition CircANN_rename :: "real list \<Rightarrow> ann_ch \<leftrightarrow> c" where
"CircANN_rename ins = {(build\<^bsub>layerRes\<^bold>.0\<^esub> (n,x), build\<^bsub>inp\<^esub> (n, (x))) | n x . True} \<union>
            {(build\<^bsub>layerRes\<^bold>.layerNo\<^esub> (n,x), 
            build\<^bsub>out\<^esub> (n, (denormOut n (annoutput layerNo n (normInSeq ins))))) | n x . True}"

definition CircANN :: "real list \<Rightarrow> (c, 'a) circus_alpha hrel" where
"CircANN ins = ((ANN) \<lbrakk>CircANN_rename ins\<rbrakk>\<^sub>r)"

(*Theorem 1 from NFM2025 paper: *)
theorem circann_vc:
  fixes ins :: "real list"
assumes "\<epsilon> \<ge> 0" and 
  "(\<forall> inseq. (\<forall> outseq. p (inseq, outseq) \<longrightarrow> (\<forall> i \<in> {1::nat..outsize}.
            (
              ( \<bar>(denormOut i (annoutput layerNo i (normInSeq(inseq))) ) - outseq(i)\<bar> \<le> \<epsilon>) 
            )
          )))"
shows "cconf \<epsilon> (CircANN ins) (CyclicRCController insize outsize p)"
  sorry

(*Theorem 2 : *)
consts c :: "nat" 
       min :: "real"
       max :: "real"

definition min_split :: "nat \<Rightarrow> real" where
"min_split i = min + (i * (max/c))" 

(*Accept a list splits, returns a list of real  *)
fun min_seq :: "nat list \<Rightarrow> real list" where
"min_seq [] = []" | 
"min_seq (x#xs) = [(min_split x)] @ min_seq xs"

definition max_split :: "nat \<Rightarrow> real" where
"max_split i = min + ((i+1) * (max/c))" 

fun max_seq :: "nat list \<Rightarrow> real list" where
"max_seq [] = []" | 
"max_seq (x#xs) = [(max_split x)] @ max_seq xs"

(*Encode all free variables as parameters, i is free, so is a parameter:*)
definition normError :: "nat \<Rightarrow> real" where 
"normError i = (normOut i \<epsilon>) + 
              ((annRange).2 - (annRange).1)*((outRanges(i).1))  
              /
              ((outRanges(i).2) - outRanges(i).1)"

(*Lemma that links constant epsilon to normError*)
lemma epsilon_link: 
  fixes i :: nat
  shows "
  \<epsilon> = (denormOut i (normError i)) + 
  (outRanges(i).2 - outRanges(i).1)*annRange.1  
              /
              (annRange.2 - annRange.1)"
  sorry

(*P relationship, for some relation R that captures p.*)
consts R :: "real list \<leftrightarrow> real list"

lemma P_relationship_general: "\<forall> s :: (real list \<times> real list).   
                                  p s = ((snd(s) \<in> (R ` {fst(s)})))"
  sorry


theorem vc_ann_tools: 
  assumes "\<epsilon> \<ge> 0" and 
  "
  (\<forall> nlist :: nat list. 
      \<forall> n \<in> {1..#nlist}. 
        nlist(n)\<^sub>s \<in> {0..(c-1)} \<longrightarrow>
        (\<forall> inseq :: real list. 
          (\<forall> i \<in> {1..insize}. 
             (min_split (nlist(i))) \<le> inseq(i)\<^sub>s \<and> 
             inseq(i)\<^sub>s \<le>  (max_split (nlist(i))) 
             
          )
          \<longrightarrow>
            (\<forall> outseq :: real list. 
               outseq \<in> R ` {(min_seq nlist)} \<longrightarrow> 
                 (\<forall> outseq' :: real list. 
                    outseq' \<in> R ` {(max_seq nlist)} \<longrightarrow> 
                      ( 
                        \<forall> i \<in> {1..outsize}. 
                          (annoutput layerNo i inseq) \<le>
                            (normOut i (outseq'(i))) + (normError i) \<and> 
                          (annoutput layerNo i inseq) \<ge> 
                            (normOut i (outseq(i))) - (normError i)
                      )
                 )
            )
          )
  )
  "
  shows "(\<forall> inseq. (\<forall> outseq. p (inseq, outseq) \<longrightarrow> (\<forall> i \<in> {1::nat..outsize}.
            (
              ( \<bar>(denormOut i (annoutput layerNo i (normInSeq(inseq))) ) - outseq(i)\<bar> \<le> \<epsilon>) 
            )
          )))"
  sorry


(*Verification Condition for Marabou from NFM2025: *)
consts \<delta> :: "real"

theorem vc_ann_tools: 
  fixes ins :: "real list"
  assumes "\<epsilon> \<ge> 0" and "\<delta> > 0" and
  "
  \<not> (\<exists> nlist :: nat list. 
      \<exists> n \<in> {1..#nlist}. 
        nlist(n)\<^sub>s \<in> {0..(c-1)} \<longrightarrow>
        (\<forall> inseq :: real list. 
          (\<forall> i \<in> {1..insize}. 
             (min_split (nlist(i))) \<le> inseq(i)\<^sub>s \<and> 
             inseq(i)\<^sub>s \<le>  (max_split (nlist(i))) 
             
          )
          \<and>
            (\<exists> outseq :: real list. 
               outseq \<in> R ` {(min_seq nlist)} \<longrightarrow> 
                 (\<exists> outseq' :: real list. 
                    outseq' \<in> R ` {(max_seq nlist)} \<longrightarrow> 
                      ( 
                        \<exists> i \<in> {1..outsize}. 
                          (annoutput layerNo i inseq) >=
                            outseq'(i) + \<epsilon> + \<delta> \<and> 
                          (annoutput layerNo i inseq) \<le> 
                            outseq(i) - \<epsilon> - \<delta>
                      )
                 )
            )
          )
  )
  "
  shows "cconf \<epsilon> (CircANN ins) (CyclicRCController insize outsize p)
  "
  sorry


section Segway_Case_Study


(*This should work, if we can get Marabou and Isabelle to both prove this property, would be nice as well.*)
(*Is the problem annoutput, if we just have another function, can it do this? We can even replace this manually with
the function. *)

definition P_norm where "P_norm = 0.92"
definition D_norm where "D_norm = 0.08"
definition eps_example where "eps_example = 0.5"
definition delta_example where "delta_example = 0.01"

definition P_ex ::"(real list \<times> real list) \<Rightarrow> bool" where 
  "P_ex s = (snd(s)(1) = (Pc * fst(s)(1) + Dc * fst(s)(2)))"

definition P_fun :: "real \<Rightarrow> real \<Rightarrow> real" where
"P_fun = (\<lambda> x y. (Pc * x + Dc * y))"

lemma P_relationship_example: "\<forall> s :: (real list \<times> real list). 
                      P_ex s = ((snd(s)(1) = (P_fun (fst(s)(1)) (fst(s)(2)))))" by (simp add: P_ex_def P_fun_def)



lemma domain_split_example_1: 
  shows "\<not> (\<exists> n\<^sub>1 n\<^sub>2 :: nat. n\<^sub>1 \<in> {0::nat..1} \<and> n\<^sub>2 \<in> {0::nat..1} \<and>
            (\<exists> x\<^sub>1 x\<^sub>2 :: real.  
              (n\<^sub>1 * (0.5)) \<le> x\<^sub>1 \<and> x\<^sub>1 \<le> (n\<^sub>1 + 1)*(0.5) \<and>
              (n\<^sub>2 * (0.5)) \<le> x\<^sub>2 \<and> x\<^sub>2 \<le> (n\<^sub>2 + 1)*(0.5) \<and> 
              (annoutput layerNo 1 [x\<^sub>1, x\<^sub>2] \<le> (P_norm * (n\<^sub>1 * (0.5))) + (D_norm * (n\<^sub>2 * (0.50))) - eps_example - delta_example  \<or> 
               annoutput layerNo 1 [x\<^sub>1, x\<^sub>2] \<ge> (P_norm * (n\<^sub>1+1 * (0.5))) + (D_norm * (n\<^sub>2+1 * (0.50))) + eps_example + delta_example))               
              )" 
  apply (simp add: P_norm_def D_norm_def eps_example_def delta_example_def)
  sorry

lemma domain_split_example_2: 
  shows "\<not> (\<exists> n\<^sub>1 n\<^sub>2 :: nat. n\<^sub>1 \<in> {0::nat..1} \<and> n\<^sub>2 \<in> {0::nat..1} \<and>
            (\<exists> x\<^sub>1 x\<^sub>2 :: real.  
              (n\<^sub>1 * (0.5)) \<le> x\<^sub>1 \<and> x\<^sub>1 \<le> (n\<^sub>1 + 1)*(0.5) \<and>
              (n\<^sub>2 * (0.5)) \<le> x\<^sub>2 \<and> x\<^sub>2 \<le> (n\<^sub>2 + 1)*(0.5) \<and> 
              (0 \<le> (P_norm * (n\<^sub>1 * (0.5))) + (D_norm * (n\<^sub>2 * (0.50))) - eps_example - delta_example  \<or> 
               10 \<ge> (P_norm * (n\<^sub>1+1 * (0.5))) + (D_norm * (n\<^sub>2+1 * (0.50))) + eps_example + delta_example))               
              )" 
  apply (simp add: P_norm_def D_norm_def eps_example_def delta_example_def)
  apply (auto)
  sorry



  
