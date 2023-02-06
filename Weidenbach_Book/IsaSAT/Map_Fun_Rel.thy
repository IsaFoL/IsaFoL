theory Map_Fun_Rel
  imports More_Sepref.WB_More_Refinement
begin

subsection \<open>Refinement from function to lists\<close>

text \<open>Throughout our formalization, we often use functions at the most abstract level, that we refine to
lists assuming a known domain.

One thing to remark is that I have changed my mind on how to do things. Before we refined things
directly and kept the domain implicit. Nowadays, I make the domain explicit -- even if this means
that we have to duplicate the information of the domain through all the components of our state.
\<close>
paragraph \<open>Definition\<close>

definition map_fun_rel :: \<open>(nat \<times> 'key) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> ('key \<Rightarrow> 'a)) set\<close> where
  map_fun_rel_def_internal:
    \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

lemma map_fun_rel_def:
  \<open>\<langle>R\<rangle>map_fun_rel D = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>
  unfolding relAPP_def map_fun_rel_def_internal by auto


lemma map_fun_rel_nth:
  \<open>(xs,ys)\<in>\<langle>R\<rangle>map_fun_rel D \<Longrightarrow> (i,j)\<in>D \<Longrightarrow> (xs ! i , ys j) \<in> R\<close>
  unfolding map_fun_rel_def by auto
(*TODO is that really useful here?*)



paragraph \<open>In combination with lists\<close>

definition length_ll_f where
  \<open>length_ll_f W L = length (W L)\<close>

lemma map_fun_rel_length:
  \<open>(xs,ys)\<in>\<langle>\<langle>R\<rangle>list_rel\<rangle>map_fun_rel D \<Longrightarrow> (i,j)\<in>D \<Longrightarrow> (length_ll xs i, length_ll_f ys j) \<in> nat_rel\<close>
  unfolding map_fun_rel_def by (auto simp: length_ll_def length_ll_f_def
    dest!: bspec list_rel_imp_same_length)

(*TODO is this used or is only the definition unfolded*)
definition append_update :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>append_update W L a = W(L:= W (L) @ [a])\<close>

end
