theory Watched_Literals_Transition_System_Inprocessing
  imports Watched_Literals_Transition_System
begin
text \<open>
  The subsumption is very similar to the PCDCL case.
\<close>
inductive cdcl_twl_subsumed :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
subsumed_II:
  \<open>cdcl_twl_subsumed (M, N + {#C, C'#}, U, D, NE, UE, NS, US, {#}, Q)
     (M, add_mset C N, U, D, NE, UE, add_mset (clause C') NS, US, {#}, Q)\<close>
  if \<open>clause C \<subseteq># clause C'\<close> |
subsumed_RR:
  \<open>cdcl_twl_subsumed (M, N, U + {#C, C'#}, D, NE, UE, NS, US, {#}, Q)
     (M, N, add_mset C U, D, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
  if \<open>clause C \<subseteq># clause C'\<close> |
subsumed_IR:
  \<open>cdcl_twl_subsumed (M, add_mset C N, add_mset C' U, D, NE, UE, NS, US, {#}, Q)
     (M, add_mset C N, U, D, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
  if \<open>clause C \<subseteq># clause C'\<close>

lemma cdcl_twl_subsumed_cdcl_subsumed:
  \<open>cdcl_twl_subsumed S T \<Longrightarrow> cdcl_subsumed (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  apply (induction rule: cdcl_twl_subsumed.induct)
  subgoal by (auto simp: cdcl_subsumed.simps)
  subgoal by (auto simp: cdcl_subsumed.simps)
  subgoal by (auto simp: cdcl_subsumed.simps)
  done

text \<open>
  The lifting from \<^term>\<open>cdcl_subresolution\<close> is a lot more complicated due to the handling of
  unit and nonunit clauses. Basically, we have to split every rule in two. Hence we don't have a
  one-to-one mapping anymore, but need to use \<^term>\<open>cdcl_flush_unit\<close> or rule of that kind.

  We don't support (yet) generation of the empty clause. This is very tricky because we entirely
  leave the CDCL calculus.
\<close>
inductive cdcl_twl_subresolution :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
twl_subresolution_II_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, DD, NE, UE, NS, US, {#}, {#})
    (M, N + {#C, E#}, U, DD, NE, UE, add_mset (clause C') NS, US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>size E \<ge> 2\<close> |
twl_subresolution_II_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, DD, NE, UE, NS, US, {#}, {#})
    (Propagated K {#K#} # M, N + {#C#}, U, DD, add_mset {#K#} NE, UE,
        add_mset (clause C') NS, US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>remdups_mset D' = {#K#}\<close>|

twl_subresolution_LL_nonunit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, DD, NE, UE, NS, US, {#}, {#})
    (M, N, U + {#C, E#}, DD, NE, UE, NS, add_mset (clause C') US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close> \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close>|
twl_subresolution_LL_unit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, DD, NE, UE, NS, US, {#}, {#})
    (Propagated K {#K#} # M, N, U + {#C#}, DD, NE, add_mset {#K#} UE, NS,
       add_mset (clause C') US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close> \<open>\<not>tautology (D + D')\<close> |

twl_subresolution_LI_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, DD, NE, UE, NS, US, {#}, {#})
    (M, N + {#C#}, U + {#E#}, DD, NE, UE, NS, add_mset (clause C') US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close>|
twl_subresolution_LI_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, DD, NE, UE, NS, US, {#}, {#})
    (Propagated K {#K#} # M, N + {#C#}, U, DD, NE, add_mset {#K#} UE, NS,
      add_mset (clause C') US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close> |

twl_subresolution_IL_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, DD, NE, UE, NS, US, {#}, {#})
    (M, N + {#E#}, U + {#C, E#}, DD, NE, UE, add_mset (clause C') NS, US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close> |
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, DD, NE, UE, NS, US, {#}, {#})
    (Propagated K {#K#} # M, N, U + {#C#}, DD, add_mset {#K#} NE, UE,
       add_mset (clause C') NS, US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close>

end