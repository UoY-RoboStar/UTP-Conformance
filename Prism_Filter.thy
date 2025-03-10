theory Prism_Filter
  imports "Optics.Optics"
begin

definition prism_filter :: "('a \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> 'c list \<Rightarrow> 'a list" where
"prism_filter c t = map (the \<circ> match\<^bsub>c\<^esub>) (filter matches\<^bsub>c\<^esub> t)"

definition prism_filter_prod :: "('b \<times> 'a \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> 'c list \<Rightarrow> 'a list" where
"prism_filter_prod c t = map (snd \<circ> the \<circ> match\<^bsub>c\<^esub>) (filter matches\<^bsub>c\<^esub> t)"


(*prism_filter defined for sets? Set comprehension? *)

(**)
term "snd  "
definition prism_filter_prod_set :: "('b \<times> 'a \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> 'c set \<Rightarrow> 'a set" where
"prism_filter_prod_set c s = {(snd \<circ> the \<circ> match\<^bsub>c\<^esub>) x | x. x \<in> s \<and> (matches\<^bsub>c\<^esub> x) }"

(*map on every element of a set? *)

(*Prism filter testing, *)
(*Prism filter
Testing with the same channel. 
*)
chantype ann_ev = layerRes :: "nat \<times> nat \<times> real" 
        anewError :: "real" adiff :: "real" angleOutputE :: "real"

definition prism_filter_test :: "('a \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> 'c list \<Rightarrow> 'c list" where
"prism_filter_test c t = (filter matches\<^bsub>c\<^esub> t)"

(*This just filters the list, if any are in the layerRes channel. *)


(*Returns a list of the TYPE OF THE CHANNEL: *)
term "prism_filter layerRes "

term "evparam anewError (0.1)" (*evparam, *)
term "[ (build\<^bsub>layerRes\<^esub> (1,1,0.5)), (build\<^bsub>layerRes\<^esub> (1,2,0.7)), (build\<^bsub>layerRes\<^esub> (2,1,1.25)) ]"

term "prism_filter layerRes [ (build\<^bsub>layerRes\<^esub> (1,1,0.5)), (build\<^bsub>layerRes\<^esub> (1,2,0.7)), (build\<^bsub>layerRes\<^esub> (2,1,1.25)) ]"
value "prism_filter layerRes [ (build\<^bsub>layerRes\<^esub> (1,1,0.5)), (build\<^bsub>layerRes\<^esub> (1,2,0.7)), (build\<^bsub>layerRes\<^esub> (2,1,1.25)) ]"
(*Desired behaviour, we need to get the last component, for checking conformance. 

Do we need the layer and node value? we just need real numbers. 

Then we can check on how we create, the functions on how we create the actual events. 
take the last component? Still is specific to one particular event. 

works with prisms with real numbers, directly, of channel types. 


*)
value "prism_filter_test anewError [ (build\<^bsub>layerRes\<^esub> (1,1,0.5)), (build\<^bsub>layerRes\<^esub> (1,2,0.7)), (build\<^bsub>layerRes\<^esub> (2,1,1.25)) ]"
(*all 3 of the events, unchanged.  *)

(**)

(*list of channels, just with filter, would be a list of event types, that matches. 

*)
(*Maps, to the list, the function, composition, the and match, match gets

the Channel Type. ann_ev,

definition prism_matches :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e \<Rightarrow> bool" ("matches\<index>") where
"prism_matches a e = (match\<^bsub>a\<^esub> e \<noteq> None)"

prism_matches, is, if the match of a for e is not none. 
  *)

term "match\<^bsub>c\<^esub>"
(*function composition, 'b \<Rightarrow> 'a option, composition,  *)

term "the"
(*after you get an option, REMOVES THE OPTION, THIS IS THE CONSTRUCTOR FOR THE 
ALGEBRAIC DATA TYPE, composition of htis, 'a option \<Rightarrow> 'a, after,  *)

end