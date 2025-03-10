theory UTP_ANN_Defs
  imports 
    "conf" 
begin   

(*layerRes and relevant channel instantiation:*)
chantype ann_ch = layerRes :: "nat \<times> nat \<times> real" 

chantype context_ch = anewError :: "real" adiff :: "real" angleOutputE :: "real"


(*Cyclic RoboChart Controller Pattern implementation (Def. 4.4 in Thesis): *)
fun inp_concat :: "nat \<Rightarrow> real list \<Rightarrow> c list" where
"inp_concat 0 ins = []" | 
"inp_concat n ins = inp_concat (n-1) (ins) @ [evparam inp (n, ins(n))]"

fun out_concat :: "nat \<Rightarrow> real list \<Rightarrow> c list" where
"out_concat 0 ins = []" | 
"out_concat n ins = out_concat (n-1) (ins) @ [evparam out (n, ins(n))]"


term "(ins, outs) \<in> p"
definition CyclicRCController :: "nat \<Rightarrow> nat \<Rightarrow> ((real list \<times> real list) \<Rightarrow> bool) \<Rightarrow> (c, 's) caction" where
"CyclicRCController insize outsize p = [true\<^sub>r 
                                        \<turnstile> (\<exists>ins::real list. \<exists>outs::real list.(
                                            (\<guillemotleft>p (ins, outs)\<guillemotright>) \<and> 
                                            (\<exists> i \<in> {1..\<guillemotleft>insize\<guillemotright>}. tt = (inp_concat i ins) \<and> 
                                                                  (evparam inp (i,ins(i))) \<notin> ref\<^sup>>)) \<or>
                                            (\<exists> i \<in> {1..\<guillemotleft>outsize\<guillemotright>}. tt = (out_concat i outs) \<and> (evparam out (i,ins(i))) \<notin> ref\<^sup>>)) | 
                                          (\<exists>ins::real list. \<exists>outs::real list.
                                            (\<guillemotleft>p (ins, outs)\<guillemotright>) \<and> tt = (inp_concat \<guillemotleft>insize\<guillemotright> ins) @ (out_concat \<guillemotleft>outsize\<guillemotright> outs)) ]\<^sub>R"


(*AnglePID Constants:*)
definition Pc :: "real" where "Pc = 60"
definition Dc :: "real" where "Dc = 0.6"


(*AnglePID Reactive Contract: *)

definition AnglePID_UTP :: "(context_ch, unit) caction" where
"AnglePID_UTP = RH(true\<^sub>r \<turnstile> (\<exists>currNewError::real. \<exists>currDiff::real. \<exists>currAngleOut::real.
                 (currAngleOut = (Pc * currNewError + Dc * currDiff) ) \<longrightarrow>
                ((tt = [] \<and> ((evparam anewError (\<guillemotleft>currNewError\<guillemotright>)) \<notin> ref\<^sup>>)) \<or> 
                 (tt = [(evparam anewError (\<guillemotleft>currNewError\<guillemotright>))] \<and> ((evparam adiff (\<guillemotleft>currDiff\<guillemotright>)) \<notin> ref\<^sup>>)) \<or>
                 (tt = [(evparam anewError (\<guillemotleft>currNewError\<guillemotright>)), (evparam adiff (\<guillemotleft>currDiff\<guillemotright>))]
                     \<and> ((evparam angleOutputE (\<guillemotleft>currAngleOut\<guillemotright>)) \<notin> ref\<^sup>>))
                )\<^sub>e 
                \<triangleleft> wait\<^sup>> \<triangleright> 
                  (tt = [(evparam anewError (\<guillemotleft>currNewError\<guillemotright>)), (evparam adiff (\<guillemotleft>currDiff\<guillemotright>)), 
                         (evparam angleOutputE (\<guillemotleft>currAngleOut\<guillemotright>))])\<^sub>e)\<^sub>e)"

definition AnglePID_UTP_out :: "(c, unit) caction" where
"AnglePID_UTP_out = RH(true\<^sub>r \<turnstile> (\<exists>currNewError::real. \<exists>currDiff::real. \<exists>currAngleOut::real.
                 (currAngleOut = (Pc * currNewError + Dc * currDiff) ) \<longrightarrow>
                ((tt = [] \<and> ((evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>)) \<notin> ref\<^sup>>)) \<or> 
                 (tt = [(evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>))] \<and> ((evparam inp (\<guillemotleft>2\<guillemotright>, \<guillemotleft>currDiff\<guillemotright>)) \<notin> ref\<^sup>>)) \<or>
                 (tt = [(evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>)), (evparam inp (\<guillemotleft>2\<guillemotright>, \<guillemotleft>currDiff\<guillemotright>))]
                     \<and> ((evparam out (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currAngleOut\<guillemotright>)) \<notin> ref\<^sup>>))
                )\<^sub>e 
                \<triangleleft> wait\<^sup>> \<triangleright> 
                  (tt = [(evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>)), (evparam inp (\<guillemotleft>2\<guillemotright>, \<guillemotleft>currDiff\<guillemotright>)), 
                         (evparam out (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currAngleOut\<guillemotright>))])\<^sub>e)\<^sub>e)"


definition AnglePID_UTP_out_mod :: "(c, unit) caction" where
"AnglePID_UTP_out_mod = RH(true\<^sub>r \<turnstile> (\<exists>currNewError::real. \<exists>currDiff::real. \<exists>currAngleOut::real.
                 (currAngleOut = (Pc * currNewError + Dc * currDiff) ) \<longrightarrow>
                ((tt = [] \<and> ((evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>)) \<notin> ref\<^sup>>)) \<or> 
                 (tt = [(evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>))] \<and> ((evparam inp (\<guillemotleft>2\<guillemotright>, \<guillemotleft>currDiff\<guillemotright>)) \<notin> ref\<^sup>>)) \<or>
                 (tt = [(evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>)), (evparam inp (\<guillemotleft>2\<guillemotright>, \<guillemotleft>currDiff\<guillemotright>))]
                     \<and> ((evparam out (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currAngleOut\<guillemotright>)) \<notin> ref\<^sup>>))
                )\<^sub>e 
                \<triangleleft> wait\<^sup>> \<triangleright> 
                  (tt = [(evparam inp (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currNewError\<guillemotright>)), (evparam inp (\<guillemotleft>2\<guillemotright>, \<guillemotleft>currDiff\<guillemotright>)), 
                         (evparam out (\<guillemotleft>1\<guillemotright>, \<guillemotleft>currAngleOut + 0.5\<guillemotright>))])\<^sub>e)\<^sub>e)"


definition layerSize_ex :: "nat \<Rightarrow> nat" where
"layerSize_ex x = x"

definition insize_ex :: "nat" where
"insize_ex = 2"

definition outsize_ex :: "nat" where
"outsize_ex = 1"

definition layerstructure_ex :: "nat list" where
"layerstructure_ex = [1,1]"

definition layerNo_ex :: "nat"  where
"layerNo_ex = 2"

definition maxSize_ex :: "nat" where
"maxSize_ex = 1"

(*Example weights and biases: *)
definition weights_ex :: "real list list list" where
"weights_ex = [[[1.22838,0.132874]], [[0.744636]]]"

definition biases_ex :: "real list list" where 
"biases_ex = [[0.125424], [-0.107753]]"

(*Constants of the model:  *)
consts layerSize :: "nat \<Rightarrow> nat" 
       insize :: nat 
       outsize :: nat
       layerStructure :: "nat list"
       layerNo :: nat 
       maxSize :: nat (*Not used but leaving it here for now.*)
       weights :: "real list list list"
       biases :: "real list list" 



fun lastn :: "ann_ch list \<Rightarrow> nat \<Rightarrow> ann_ch list" where
"lastn ls s = take s (rev ls)"

lemma "# ls \<ge> s \<Longrightarrow> # (lastn ls s) = s" by (simp)

fun relu :: "real \<Rightarrow> real" where
"relu x = max x 0"

lemma "x \<ge> 0 \<Longrightarrow> relu x = x" by (simp)
lemma "x < 0 \<Longrightarrow> relu x = 0" by (simp)

(*Assuming that the channel is layerRes.*)
fun dropseq :: "ann_ch list \<Rightarrow> real list" where
"dropseq [] = []" | 
"dropseq (x # xs) = snd (snd (the (match\<^bsub>layerRes\<^esub> x))) # dropseq xs"

fun liftinputseq :: "real list \<Rightarrow> ann_ch list" where
"liftinputseq [] = []" | 
"liftinputseq (x # xs) = build\<^bsub>layerRes\<^esub> (0, # (x # xs), x) # liftinputseq xs"

lemma "#liftinputseq xs = # xs" by (induct xs; simp)
  

lemma "#dropseq xs = # xs" by (induct xs; simp)

fun dotprod :: "(real list \<times> real list) \<Rightarrow> real" where
"dotprod ([], []) = 0" |
"dotprod (x # xs, y # ys) = (x * y) + dotprod(xs, ys)"

fun layercalc :: "(ann_ch list \<times> nat \<times> nat) \<Rightarrow> ann_ch list" where
"layercalc (pl, l, 0) = []" |
"layercalc (pl, l, n) = layercalc(pl, l, (n-1)) @
                        [evparam (chinstn (chinstn layerRes l) n) (relu(dotprod(dropseq(pl), weights(l)(n))) + biases(l)(n))]"

lemma "#layercalc (pl, l, n) = n" by (induct n; simp)

fun layeroutput :: "ann_ch list \<Rightarrow> (nat \<times> nat) \<Rightarrow> ann_ch list" where
"layeroutput input (0, n) = (take n input)" |
"layeroutput input (l, n) = (layeroutput input ((l-1), layerSize(l-1))) @ 
                            layercalc (lastn (layeroutput input ((l-1), layerSize(l-1))) (layerSize (l-1)), l, n)"

fun list_to_f :: "'a list \<Rightarrow> (nat \<leftrightarrow> 'a)" where
"list_to_f [] = {}" | 
"list_to_f (x # xs) = {(( length (x # xs) ), x) } \<union> list_to_f (xs)"

definition list_to_fun :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
"list_to_fun ls = rel_apply (list_to_f ls)"

lemma "list_to_f [1::nat,2] = {(1,2), (2,1)}" by auto

fun fun_to_list :: "nat \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'b list" where
"fun_to_list 0 f = []" |
"fun_to_list i f = fun_to_list (i-1) f @ [f (i)]"


lemma "fun_to_list 1 f = [] @ [f(1)]" by simp

lemma "fun_to_list 2 f = [] @ [f(1)] @ [f(2)]"
  by (metis One_nat_def Suc_1 append_self_conv2 diff_Suc_1 fun_to_list.elims nat.simps(3))

thm "fun_to_list.elims"

lemma len_f2l: "#fun_to_list n f = n" by (induct n ; simp) (*automated induction, *)


fun annoutput :: "nat \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> real" where
"annoutput 0 n ins = ins(n)" | 
"annoutput l n ins = relu( dotprod ( (fun_to_list (layerSize(l-1)) (rel_apply ({(pn, annoutput (l-1) (pn) (ins)) | pn. pn \<in> {1..layerSize (l-1)}})) ) ,
                       (weights l n) ) + (biases l n))" 

(*Definition B.1 in the thesis:*)
definition nodeoutput :: "nat \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> ann_ch" where
"nodeoutput l n ins = evparam layerRes (l, n, (annoutput (l) (n) (ins)))"

lemma layeroutput1:
"n \<le> #input \<Longrightarrow> #layeroutput input (0, n) = n" by (simp)

lemma layeroutput_noinput: 
"layeroutput [] (0,n) = []" by (induct n; simp)

lemma layeroutput2: 
"n \<le> #input \<Longrightarrow> layeroutput input (0,n) = (take n input)" by (simp)

(*instantiation of the input channel, shortcut for input channel definition:*)
definition layerRes0 :: "\<nat> \<times> \<real> \<Longrightarrow>\<^sub>\<triangle> ann_ch" where
"layerRes0 = (chinstn layerRes 0)"


definition dist_concat :: "nat \<Rightarrow> (nat \<leftrightarrow> 'a list) \<Rightarrow> 'a list" where
"dist_concat n R = concat ( fun_to_list n ( rel_apply (R) ) )"


(*ANN pattern, constants are for AnglePIDANN: *)
definition ANNPattern :: "(ann_ch) set \<Rightarrow> (ann_ch, 's) caction" where
"ANNPattern I = 
[true\<^sub>r \<turnstile> ( (#(filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) < insize) \<and> 
         (tt = (filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) \<and> (\<not> ( csbasic (chinstn (layerRes0) (#(filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) + 1)) \<subseteq> ref\<^sup>>))))
         \<or> 
         (#(filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) = insize \<and>
          (\<exists> l \<in> {1..layerNo}. \<exists> n \<in> {1..layerSize(l)}. 
            tt = (butlast (layeroutput (filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) (l, n) ) ) \<and> 
            last (layeroutput (filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) (l, n)) \<notin> ref\<^sup>>
           )
          )
     | #(filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) = insize \<and> (tt = layeroutput (filter (\<lambda>x. x \<in> \<guillemotleft>I\<guillemotright>) tt) (layerNo, layerSize(layerNo)))]\<^sub>R
"

end
