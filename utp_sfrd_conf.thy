section \<open> UTP Conformance \<close>

theory utp_sfrd_conf
  imports 
    Prism_Filter
    "UTP-Stateful-Failure.utp_sf_rdes"
    "Circus_Toolkit.Circus_Toolkit"
begin

subsection \<open> Preliminaries \<close>

text \<open> We use caction as a type synonym to represent a Circus action in UTP, with event type 'e and 
     state type 's.
     We define caction as a synonym for the stateful failure reactive designs (sfrd) homogenous relation (hrel).
     We need sfrd specifically because we refer to the refusals of a Circus program, as well as the trace and state.\<close>

type_synonym ('e, 's) caction = "('s, 'e) sfrd hrel"

text \<open> This is needed as we use the UTP overloaded Logic Syntax \<close>
unbundle UTP_Logic_Syntax 

subsection \<open> Definitions \<close>

text \<open> These are implementations of the account of conformance as written by Jim Woodcock
      in RoboSapiens deliverable D1.1 in Section 4, with the refusals (ref) observational variable added. \<close>

definition approx :: "real \<Rightarrow> real \<Rightarrow> real set" where
"approx eps x = {y | y::real. (x-eps) \<le> y \<and> y \<le> (x+eps)}"

definition seq_approx :: "real \<Rightarrow> real list \<Rightarrow> real list set" where
"seq_approx eps xs = {ys | ys. (#ys = #xs) \<and> (\<forall> i \<in> {1..#xs}. 
                     (ys::real list)(i) \<in> (approx (eps) (xs(i)))) }"

definition Approx :: "real \<Rightarrow> ('b \<times> real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction" where
"Approx eps tc P = R3c(\<exists> t. P\<lbrakk>\<guillemotleft>t\<guillemotright> /tr\<^sup>>\<rbrakk> \<and>
               (prism_filter_prod \<guillemotleft>tc\<guillemotright> (tr\<^sup>> - tr\<^sup><)) \<in> seq_approx (\<guillemotleft>eps\<guillemotright>) (prism_filter_prod \<guillemotleft>tc\<guillemotright> (\<guillemotleft>t\<guillemotright> - tr\<^sup><))
               )\<^sub>e"

(*Conformance with a single real valued channel*)
definition Approx_sin :: "real \<Rightarrow> (real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction" where
"Approx_sin eps tc P = R3c(\<exists> t. P\<lbrakk>\<guillemotleft>t\<guillemotright> /tr\<^sup>> \<rbrakk> \<and>
               (prism_filter \<guillemotleft>tc\<guillemotright> (tr\<^sup>> - tr\<^sup><)) \<in> seq_approx (\<guillemotleft>eps\<guillemotright>) (prism_filter \<guillemotleft>tc\<guillemotright> (\<guillemotleft>t\<guillemotright> - tr\<^sup><))
               )\<^sub>e"

(*This is conformance where the type of the prism has a product type, using prism_filter_prod. *)
definition conf :: "real \<Rightarrow> ('b \<times> real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction \<Rightarrow> bool" where
"conf eps tc P Q =  (eps \<ge> 0 \<longrightarrow> ((Approx(eps)(tc)(Q) \<sqsubseteq> P)))"

(*Conformance singular channel type: *)
definition conf_sin :: "real \<Rightarrow> (real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction \<Rightarrow> bool" where
"conf_sin eps tc P Q =  (eps \<ge> 0 \<longrightarrow> ((Approx_sin(eps)(tc)(Q) \<sqsubseteq> P)))"



text \<open> The definition cconf is a conformance shorthand, where we fix the channel types to inp and out, which 
       corresponds to conformance for ANN controllers and patterns of cyclic controllers specifically. \<close>

chantype c = inp :: "nat \<times> real" out :: "nat \<times> real"

definition cconf :: "real \<Rightarrow> (c, 's) caction \<Rightarrow> (c, 's) caction \<Rightarrow> bool" where
"cconf eps P Q = (conf eps out P Q)"

subsection \<open> Conformance Proofs \<close>

text \<open> These are the automations of some proofs of conformance, this section needs to be expanded though. \<close>

text \<open> This lemma is a proof of list equivalence. If we establish that two lists are the same length, and that 
       every element of one list is a member of the singleton set for another list, then the lists themselves are equivalent. 
       This is required to automate the proof of sequence approximation. \<close>
lemma list_lem:
  fixes xs :: "'e list" and a :: "'e list" 
  shows "length a = length xs \<and> (\<forall>i\<in>{1..length xs}. a(i) \<in> {xs(i)}) \<longleftrightarrow>
    (a = xs)"                
  apply (simp)
  by (metis One_nat_def Suc_le_eq atLeastAtMost_iff diff_Suc_1 le_eq_less_or_eq less_one not_less_eq nth_equalityI)

text \<open> Trivial Approximation \<close>
lemma trivial_approx:"approx 0 x = {x}" unfolding approx_def by auto

text \<open> Value Self-Approximation \<close>
lemma approx_any: "eps \<ge> 0 \<Longrightarrow> x \<in> approx eps x" unfolding approx_def by force

text \<open> Trivial Sequence Approximation \<close>
lemma seq_approx0 : "seq_approx 0 xs = {xs}" unfolding seq_approx_def
  using trivial_approx
  apply (auto)
  by (metis One_nat_def list_lem)
  

text \<open> Lemma 4.2 from RoboSapiens D1.1: Sequences Self-Approximation \<close>
lemma seq_approx_mem : 
  fixes eps::"real"
  assumes "eps \<ge> 0"
  shows "xs \<in> seq_approx eps xs" 
  apply (simp add: seq_approx_def approx_def assms)
  done


end
