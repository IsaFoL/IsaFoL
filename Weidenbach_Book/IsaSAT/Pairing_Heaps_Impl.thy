theory Pairing_Heaps_Impl
  imports Relational_Pairing_Heaps
    Map_Fun_Rel
begin

section \<open>Imperative Pairing heaps\<close>

type_synonym ('a,'b)pairing_heaps_imp = \<open>('a option list \<times> 'a option list \<times> 'a option list \<times> 'a option list \<times> 'b list \<times> 'a option)\<close>
definition pairing_heaps_rel :: \<open>('a option \<times> nat option) set ⇒ ('b option \<times>'c option) set ⇒
  (('a,'b)pairing_heaps_imp \<times> (nat set \<times> (nat,'c) hp_fun \<times> nat option)) set\<close> where
pairing_heaps_rel_def_internal:
  \<open>pairing_heaps_rel R S = {((prevs', nxts', children', parents', scores', h'), (\<V>, (prevs, nxts, children, parents, scores), h)).
    (h', h) \<in> R \<and>
    (prevs', prevs) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (nxts', nxts) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (children', children) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (parents', parents) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (map Some scores', scores) \<in> \<langle>S\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>)
  }\<close>

lemma pairing_heaps_rel_def:
  \<open>\<langle>R,S\<rangle>pairing_heaps_rel =
{((prevs', nxts', children', parents', scores', h'), (\<V>, (prevs, nxts, children, parents, scores), h)).
    (h', h) \<in> R \<and>
    (prevs', prevs) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (nxts', nxts) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (children', children) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (parents', parents) \<in> \<langle>R\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>) \<and>
    (map Some scores', scores) \<in> \<langle>S\<rangle>map_fun_rel ((\<lambda>a. (a,a))` \<V>)
  }\<close>
  unfolding pairing_heaps_rel_def_internal relAPP_def by auto


definition mop_hp_read_nxt_imp where
  \<open>mop_hp_read_nxt_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length nxts);
      RETURN (nxts ! i)
  })\<close>

fun hp_read_nxt' :: \<open>_\<close> where
  \<open>hp_read_nxt' i (\<V>, arr, h) = hp_read_nxt i arr\<close>

lemma mop_hp_read_nxt_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  mop_hp_read_nxt_imp i xs \<le> SPEC (\<lambda>a. (a, hp_read_nxt' j ys) \<in> R)\<close>
  unfolding mop_hp_read_nxt_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  done

definition mop_hp_read_prev_imp where
  \<open>mop_hp_read_prev_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length prevs);
      RETURN (prevs ! i)
  })\<close>

fun hp_read_prev' :: \<open>_\<close> where
  \<open>hp_read_prev' i (\<V>, arr, h) = hp_read_prev i arr\<close>

lemma mop_hp_read_prev_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  mop_hp_read_prev_imp i xs \<le> SPEC (\<lambda>a. (a, hp_read_prev' j ys) \<in> R)\<close>
  unfolding mop_hp_read_prev_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  done

definition mop_hp_read_child_imp where
  \<open>mop_hp_read_child_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length children);
      RETURN (children ! i)
  })\<close>

fun hp_read_child' :: \<open>_\<close> where
  \<open>hp_read_child' i (\<V>, arr, h) = hp_read_child i arr\<close>

lemma mop_hp_read_child_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  mop_hp_read_child_imp i xs \<le> SPEC (\<lambda>a. (a, hp_read_child' j ys) \<in> R)\<close>
  unfolding mop_hp_read_child_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  done

definition mop_hp_read_parent_imp where
  \<open>mop_hp_read_parent_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length parents);
      RETURN (parents ! i)
  })\<close>

fun hp_read_parent' :: \<open>_\<close> where
  \<open>hp_read_parent' i (\<V>, arr, h) = hp_read_parent i arr\<close>

lemma mop_hp_read_parent_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  mop_hp_read_parent_imp i xs \<le> SPEC (\<lambda>a. (a, hp_read_parent' j ys) \<in> R)\<close>
  unfolding mop_hp_read_parent_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  done

definition mop_hp_read_score_imp where
  \<open>mop_hp_read_score_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length scores);
      RETURN ((scores ! i))
  })\<close>

fun hp_read_score' :: \<open>_\<close> where
  \<open>hp_read_score' i (\<V>, arr, h) = (hp_read_score i arr)\<close>

lemma mop_hp_read_score_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  mop_hp_read_score_imp i xs \<le> SPEC (\<lambda>a. (Some a, hp_read_score' j ys) \<in> S)\<close>
  unfolding mop_hp_read_score_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def dest!: bspec)
  done

fun hp_set_all' where
  \<open>hp_set_all' i p q r s t (\<V>, u, h) = (\<V>, hp_set_all i p q r s t u, h)\<close>

definition mop_hp_set_all_imp :: \<open>nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> ('a,'b)pairing_heaps_imp nres\<close>where
  \<open>mop_hp_set_all_imp = (\<lambda>i p q r s t (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length nxts \<and> i < length prevs \<and> i < length children \<and> i < length scores);
      RETURN (prevs[i := p], nxts[i:=q], children[i:=r], parents[i:=s], scores[i:=t], h)
  })\<close>


lemma mop_hp_set_all_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow> (q',q)\<in>R\<Longrightarrow>(r',r)\<in>R \<Longrightarrow> (s',s)\<in>R\<Longrightarrow> (Some t',t)\<in>S \<Longrightarrow>
  mop_hp_set_all_imp i p' q' r' s' t' xs \<le> SPEC (\<lambda>a. (a, hp_set_all' j p q r s t ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding mop_hp_set_all_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (force simp: pairing_heaps_rel_def map_fun_rel_def hp_set_all_def)
  done

fun update_source_node where
  \<open>update_source_node i (\<V>,arr,_) = (\<V>, arr, i)\<close>
fun source_node :: \<open>(nat set \<times> (nat,'c) hp_fun \<times> nat option) \<Rightarrow> _\<close> where
  \<open>source_node (\<V>,arr,h) = h\<close>

fun update_source_node_impl :: \<open>_ \<Rightarrow> ('a,'b)pairing_heaps_imp  \<Rightarrow> ('a,'b)pairing_heaps_imp\<close> where
  \<open>update_source_node_impl i (prevs, nxts, parents, children, scores,_) = (prevs, nxts, parents, children, scores, i)\<close>

fun source_node_impl :: \<open>('a,'b)pairing_heaps_imp \<Rightarrow> _\<close> where
  \<open>source_node_impl (prevs, nxts, parents, children, scores,h) = h\<close>

lemma update_source_node_impl_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j) \<in> R ⟹
  (update_source_node_impl i xs, update_source_node j ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel›
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

lemma source_node_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow>
  (source_node_impl xs, source_node ys) \<in> R›
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

fun hp_update_parents' where
  \<open>hp_update_parents' i p(\<V>, u, h) = (\<V>, hp_update_parents i p u, h)\<close>

fun hp_update_prev' where
  \<open>hp_update_prev' i p(\<V>, u, h) = (\<V>, hp_update_prev i p u, h)\<close>

fun hp_update_nxt' where
  \<open>hp_update_nxt' i p(\<V>, u, h) = (\<V>, hp_update_nxt i p u, h)\<close>

fun hp_update_score' where
  \<open>hp_update_score' i p(\<V>, u, h) = (\<V>, hp_update_score i p u, h)\<close>

lemma hp_insert_alt_def:
  \<open>hp_insert = (\<lambda>i w arr. do {
  let h = source_node arr;
  if h = None then do {
    ASSERT (i \<in> fst arr);
    RETURN (update_source_node (Some i) (hp_set_all' i None None None None (Some w) arr))
   } else do {
    ASSERT (i \<in> fst arr);
    ASSERT (hp_read_prev' i arr = None);
    ASSERT (hp_read_parent' i arr = None);
    let j = the h;
    ASSERT (j \<in> (fst arr) \<and> j \<noteq> i);
    ASSERT (hp_read_score' j (arr) \<noteq> None);
    ASSERT (hp_read_prev' j arr = None \<and> hp_read_nxt' j arr = None \<and> hp_read_parent' j arr = None);
    let y = (the (hp_read_score' j arr));
    if y < w
    then do {
      let arr = hp_set_all' i None None (Some j) None (Some w) arr;
      let arr = hp_update_parents' j (Some i) arr;
      let nxt = hp_read_nxt' j arr;
      RETURN (update_source_node (Some i) arr)
    }
    else do {
      let child = hp_read_child' j arr;
      let arr = hp_set_all' j None None (Some i) None (Some y) arr;
      let arr = hp_set_all' i None child None (Some j) (Some (w)) arr;
      let arr = (if child = None then arr else hp_update_prev' (the child) (Some i) arr);
      let arr = (if child = None then arr else hp_update_parents' (the child) None arr);
      RETURN arr
    }
   }
        })\<close>
   unfolding hp_insert_def
   by (auto intro!: ext bind_cong[OF refl] simp: Let_def)

(*
definition mop_hp_insert_impl :: \<open>'a \<Rightarrow> 'b::linorder \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> ('a,'b)pairing_heaps_imp nres\<close> where
  \<open>mop_hp_insert_impl = (\<lambda>(i::'a) (w::'b) (\<V>::'a set, arr :: ('a, 'b) hp_fun, h :: 'a option). do {
  if h = None then do {
    ASSERT (i \<in> \<V>);
    RETURN (\<V>, hp_set_all i None None None None (Some w) arr, Some i)
   } else do {
    ASSERT (i \<in> \<V>);
    ASSERT (hp_read_prev i arr = None);
    ASSERT (hp_read_parent i arr = None);
    let (j::'a) = ((the h) :: 'a);
    ASSERT (j \<in> (\<V>::'a set) \<and> j \<noteq> i);
    ASSERT (hp_read_score j (arr :: ('a, 'b) hp_fun) \<noteq> None);
    ASSERT (hp_read_prev j arr = None \<and> hp_read_nxt j arr = None \<and> hp_read_parent j arr = None);
    let y = (the (hp_read_score j arr)::'b);
    if y < w
    then do {
      let arr = hp_set_all i None None (Some j) None (Some (w::'b)) (arr::('a, 'b) hp_fun);
      let arr = hp_update_parents j (Some i) arr;
      let nxt = hp_read_nxt j arr;
      RETURN (\<V>, arr :: ('a, 'b) hp_fun, Some i)
    }
    else do {
      let child = hp_read_child j arr;
      let arr = hp_set_all j None None (Some i) None (Some y) arr;
      let arr = hp_set_all i None child None (Some j) (Some (w::'b)) arr;
      let arr = (if child = None then arr else hp_update_prev (the child) (Some i) arr);
      let arr = (if child = None then arr else hp_update_parents (the child) None arr);
      RETURN (\<V>, arr :: ('a, 'b) hp_fun, h)
    }
   }
  })\<close>
*)
end