theory conf
  imports 
    Prism_Filter
    "UTP-Stateful-Failure.utp_sf_rdes"
    "Circus_Toolkit.Circus_Toolkit"
begin

type_synonym ('e, 's) caction = "('s, 'e) sfrd hrel"


unbundle UTP_Logic_Syntax 


(*DEFINITIONS: *)

definition approx :: "real \<Rightarrow> real \<Rightarrow> real set" where
"approx eps x = {y | y::real. (x-eps) \<le> y \<and> y \<le> (x+eps)}"

definition seq_approx :: "real \<Rightarrow> real list \<Rightarrow> real list set" where
"seq_approx eps xs = {ys | ys. (#ys = #xs) \<and> (\<forall> i \<in> {1..#xs}. 
                     (ys::real list)(i) \<in> (approx (eps) (xs(i)))) }"

definition set_approx :: "real \<Rightarrow> real set \<Rightarrow> (real set) set" where
"set_approx eps xs = {ys | ys. (#ys = #xs) \<and> 
                (\<forall> e \<in> ys. \<exists> e1 \<in> xs.  
                (e \<in> approx eps e1 ))}"

(*Represent the alphabet of a process: replace with real definition later.*)
consts process_alpha :: "('e, 's) caction \<Rightarrow> 'e set" ("\<alpha>_") 
(*
alphabet ('e, 's) circus_alpha = "('e list, 's) rdes_alpha" +
  ref :: "'e set"

type_synonym ('e, 's) caction = "('e, 's) circus_alpha hrel"
*)

definition Approx :: "real \<Rightarrow> ('b \<times> real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction" where
"Approx eps tc P = R3c(\<exists> t. \<exists> a. P\<lbrakk>\<guillemotleft>t\<guillemotright>, ((\<alpha> \<guillemotleft>P\<guillemotright>) - \<guillemotleft>a\<guillemotright>)/tr\<^sup>>, ref\<^sup>>\<rbrakk> \<and>
               (prism_filter_prod \<guillemotleft>tc\<guillemotright> (tr\<^sup>> - tr\<^sup><)) \<in> seq_approx (\<guillemotleft>eps\<guillemotright>) (prism_filter_prod \<guillemotleft>tc\<guillemotright> (\<guillemotleft>t\<guillemotright> - tr\<^sup><)) \<and>
               (prism_filter_prod_set \<guillemotleft>tc\<guillemotright> a) \<in> (set_approx (\<guillemotleft>eps\<guillemotright>) (prism_filter_prod_set \<guillemotleft>tc\<guillemotright> (((\<alpha> \<guillemotleft>P\<guillemotright>) - ($ref\<^sup>>)))))
               )\<^sub>e"

(*

I don't think we need these conditions, add them if we do: 
(\<forall> i \<in> {1..#((\<guillemotleft>t\<guillemotright> - tr\<^sup><))}. \<not> (matches\<^bsub>\<guillemotleft>tc\<guillemotright>\<^esub> ((\<guillemotleft>t\<guillemotright> - tr\<^sup><)(i))) \<longrightarrow> (\<guillemotleft>t\<guillemotright> - tr\<^sup><)(i) = (tr\<^sup>> - tr\<^sup><)(i)) \<and>
               (\<forall> e \<in> a. \<not> (matches\<^bsub>\<guillemotleft>tc\<guillemotright>\<^esub> (e)) \<longrightarrow> e \<in> ((process_alpha \<guillemotleft>P\<guillemotright>) - ($ref\<^sup>>)))

*)

(*Approx on reactive contracts instead of reactive relations. 
Lemma? Assumption? 
*)


(*Approx could be defined as an operator on contracts, defined as its effect on contracts, 

this could aid in reasoning, what about for the precondition? Nothing, t affects tr' and ref', reactive *)
(*Parameterised conformance, we are calling ZConf. *)
definition conf :: "real \<Rightarrow> ('b \<times> real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction \<Rightarrow> bool" where
"conf eps tc P Q =  (eps \<ge> 0 \<longrightarrow> ((Approx(eps)(tc)(Q) \<sqsubseteq> P)))"

(*CConf, conformance with a given output channel. *)
(*Corresponds to conf defined in the thesis.*)
(*Channels we will use, we will rename into these channels, from the thesis: 

We are taking inp to be a channel, it says a sequence of events, we interpret as a channel with two components:

i for the index, it can be any number of inputs or outputs. 

And to carry the value, the second component. 

We will rename the layerRes.0 and layerRes.layerNo channels into these channels, as we do in the thesis.

This needs to be the channels for the cyclic controller pattern, and we will rename into these. 


*)
chantype c = inp :: "nat \<times> real" out :: "nat \<times> real"

(*The out set, we take to be the out channel, as that is what we will use in proof.*)
definition Out where "Out = out"

(*Only note is the event type is fixed to c, but is polymorphic in its state type.*)
definition cconf :: "real \<Rightarrow> (c, 's) caction \<Rightarrow> (c, 's) caction \<Rightarrow> bool" where
"cconf eps P Q = (conf eps out P Q)"

lemma list_lem:
  fixes xs :: "'e list" and a :: "'e list" 
  shows "length a = length xs \<and> (\<forall>i\<in>{1..length xs}. a(i) \<in> {xs(i)}) \<longleftrightarrow>
    (a = xs)"                
  apply (simp)
  by (metis One_nat_def Suc_le_eq atLeastAtMost_iff diff_Suc_1 le_eq_less_or_eq less_one not_less_eq nth_equalityI)

(*Trivial Approximation: *)
lemma trivial_approx:"approx 0 x = {x}" unfolding approx_def by auto

(*Value self-approximation: *)
lemma approx_any: "eps \<ge> 0 \<Longrightarrow> x \<in> approx eps x" unfolding approx_def by force

(*Trivial Sequence Approximation:*)
lemma seq_approx0 : "seq_approx 0 xs = {xs}" unfolding seq_approx_def
  using trivial_approx
  apply (auto)
  by (metis One_nat_def list_lem)
  

(*LEMMA 4.2: Sequences Self-Approximation mechanisation. *)
lemma seq_approx_mem : 
  fixes eps::"real"
  assumes "eps \<ge> 0"
  shows "xs \<in> seq_approx eps xs" 
  apply (simp add: seq_approx_def approx_def assms)
  done

(*Modified Lemma 4.2, for set approx.*)
lemma set_approx_mem : 
  fixes eps::"real"
  assumes "eps \<ge> 0"
  shows "xs \<in> set_approx eps xs" 
  unfolding set_approx_def approx_def
  using assms by force


end
