section \<open> UTP Process Alphabets \<close>
text \<open> This is a mechanisation of an alphabet command in UTP. We need this because we are working with the acceptances
in conformance. This is an in-development file and needs more review. 

This also contains the work on process traces, and work for mechanising the refusals (acceptances) with 
conformance, for review later.  \<close>

theory utp_sfrd_alpha
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

subsection \<open> Process event extraction work: \<close>

definition set_approx :: "real \<Rightarrow> real set \<Rightarrow> (real set) set" where
"set_approx eps xs = {ys | ys. (#ys = #xs) \<and> 
                (\<forall> e \<in> ys. \<exists> e1 \<in> xs.  
                (e \<in> approx eps e1 ))}"


text \<open> We are treating the process alphabet as a constant for now, but see utp_sfrd_alpha for in-development work
       on a real process alphabet operator.  \<close>

term "(tr\<^sup>> - tr\<^sup><)\<^sub>e"

typ "('e, 's) caction"

definition process_events :: "('e, 's) caction \<Rightarrow> 'e set" where
[pred]: "process_events P = \<Union> ((set (tr\<^sup>> - tr\<^sup><))\<^sub>e ` Collect P)"

lemma process_events_nil: "process_events (tr\<^sup>> = tr\<^sup><)\<^sub>e = {}"
  by (pred_simp)

lemma process_events_single: "process_events (tr\<^sup>> = tr\<^sup>< @ [\<guillemotleft>a\<guillemotright>])\<^sub>e = {a}"
  by (pred_simp)

consts process_alpha :: "('e, 's) caction \<Rightarrow> 'e set" ("\<alpha>_") 



subsection \<open> Definitions \<close>

unbundle UTP_Logic_Syntax 

class real_event =
  fixes real_of_ev :: "'a \<Rightarrow> real"
  fixes ev_set :: "'a \<Rightarrow> 'a set"

chantype chan = c :: "integer \<times> real"

instantiation chan :: real_event
begin
  fun real_of_ev_chan :: "chan \<Rightarrow> real" where "real_of_ev_chan (c_C (_, x)) = x"
  fun ev_set_chan :: "chan \<Rightarrow> chan set" where "ev_set_chan _ = range (build\<^bsub>c\<^esub>)"
  instance ..
end


fun trace_alpha :: "'e::real_event list \<Rightarrow> 'e set" where 
"trace_alpha [] = {}" | 
"trace_alpha x = (ev_set (hd x)) \<union> (trace_alpha (tl x))"

chantype chan' = d :: "integer \<times> real"

typ "chan + chan'"

term "Inl (c_C (0, 1)) :: chan + chan'"

term "Inr (Inl x)"

definition set_alpha :: "'e::real_event set \<Rightarrow> 'e set" where
"set_alpha e = \<Union> {ev_set x | x. x \<in> e}"

(*
ev_alpha :: 
('e::real_event, 's) caction \<Rightarrow> 
('e::real_event set)


*)
(*Note: Returns an expression, Cannot be used in e brackets.
Not sure how to implement this to return a HOL type.*)
definition ev_alpha :: "('e::real_event, 's) caction \<Rightarrow> ('e set, (('e, 'b, 'c) circus_alpha_scheme) \<times> ('e, 'b, 'c) circus_alpha_scheme) expr" where 
"ev_alpha P = ( trace_alpha($tr\<^sup>>) \<union> set_alpha($ref\<^sup>>) )\<^sub>e"

end
