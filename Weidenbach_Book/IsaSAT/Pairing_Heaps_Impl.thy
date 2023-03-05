theory Pairing_Heaps_Impl
  imports Relational_Pairing_Heaps
    Map_Fun_Rel
begin


section \<open>Imperative Pairing heaps\<close>

type_synonym ('a,'b)pairing_heaps_imp = \<open>('a option list \<times> 'a option list \<times> 'a option list \<times> 'a option list \<times> 'b list \<times> 'a option)\<close>
definition pairing_heaps_rel :: \<open>('a option \<times> nat option) set \<Rightarrow> ('b option \<times>'c option) set \<Rightarrow>
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


definition op_hp_read_nxt_imp where
  \<open>op_hp_read_nxt_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      (nxts ! i)
  })\<close>
definition mop_hp_read_nxt_imp where
  \<open>mop_hp_read_nxt_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length nxts);
      RETURN (nxts ! i)
  })\<close>

lemma op_hp_read_nxt_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
  (op_hp_read_nxt_imp i xs, hp_read_nxt' j ys) \<in> R\<close>
  unfolding op_hp_read_nxt_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

lemma mop_hp_read_nxt_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
  mop_hp_read_nxt_imp i xs \<le> SPEC (\<lambda>a. (a, hp_read_nxt' j ys) \<in> R)\<close>
  unfolding mop_hp_read_nxt_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  done

definition op_hp_read_prev_imp where
  \<open>op_hp_read_prev_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      prevs ! i
  })\<close>

definition mop_hp_read_prev_imp where
  \<open>mop_hp_read_prev_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length prevs);
      RETURN (prevs ! i)
  })\<close>

lemma op_hp_read_prev_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
  (op_hp_read_prev_imp i xs, hp_read_prev' j ys) \<in> R\<close>
  unfolding op_hp_read_prev_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

lemma mop_hp_read_prev_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
  mop_hp_read_prev_imp i xs \<le> SPEC (\<lambda>a. (a, hp_read_prev' j ys) \<in> R)\<close>
  unfolding mop_hp_read_prev_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  done

definition op_hp_read_child_imp where
  \<open>op_hp_read_child_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      (children ! i)
  })\<close>

definition mop_hp_read_child_imp where
  \<open>mop_hp_read_child_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length children);
      RETURN (children ! i)
  })\<close>

lemma op_hp_read_child_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
  (op_hp_read_child_imp i xs, hp_read_child' j ys) \<in> R\<close>
  unfolding op_hp_read_child_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

lemma mop_hp_read_child_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel  \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
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
definition op_hp_read_parent_imp where
  \<open>op_hp_read_parent_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      (parents ! i)
  })\<close>

lemma op_hp_read_parent_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
  (op_hp_read_parent_imp i xs, hp_read_parent' j ys) \<in> R\<close>
  unfolding op_hp_read_parent_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
 
lemma mop_hp_read_parent_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
  mop_hp_read_parent_imp i xs \<le> SPEC (\<lambda>a. (a, hp_read_parent' j ys) \<in> R)\<close>
  unfolding mop_hp_read_parent_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  done

definition op_hp_read_score_imp :: \<open>nat \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> 'b\<close> where
  \<open>op_hp_read_score_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ((scores ! i))
  })\<close>

definition mop_hp_read_score_imp :: \<open>nat \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> 'b nres\<close> where
  \<open>mop_hp_read_score_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length scores);
      RETURN ((scores ! i))
  })\<close>

lemma mop_hp_read_score_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
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
      ASSERT (i < length nxts \<and> i < length prevs \<and> i < length parents \<and> i < length children \<and> i < length scores);
      RETURN (prevs[i := p], nxts[i:=q], children[i:=r], parents[i:=s], scores[i:=t], h)
  })\<close>


lemma mop_hp_set_all_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow>(i,j)\<in>nat_rel \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow> (q',q)\<in>R\<Longrightarrow>(r',r)\<in>R \<Longrightarrow> (s',s)\<in>R\<Longrightarrow> (Some t',t)\<in>S \<Longrightarrow> j \<in> fst ys \<Longrightarrow> 
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
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
  subgoal
    by (force simp: pairing_heaps_rel_def map_fun_rel_def hp_set_all_def)
  done

lemma fst_hp_set_all'[simp]: \<open>fst (hp_set_all' i p q r s t x) = fst x\<close>
  by (cases x) auto

fun update_source_node_impl :: \<open>_ \<Rightarrow> ('a,'b)pairing_heaps_imp  \<Rightarrow> ('a,'b)pairing_heaps_imp\<close> where
  \<open>update_source_node_impl i (prevs, nxts, parents, children, scores,_) = (prevs, nxts, parents, children, scores, i)\<close>

fun source_node_impl :: \<open>('a,'b)pairing_heaps_imp \<Rightarrow> 'a option\<close> where
  \<open>source_node_impl (prevs, nxts, parents, children, scores,h) = h\<close>

lemma update_source_node_impl_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j) \<in> R \<Longrightarrow>
  (update_source_node_impl i xs, update_source_node j ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel\<close>
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

lemma source_node_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow>
  (source_node_impl xs, source_node ys) \<in> R\<close>
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

lemma hp_insert_alt_def:
  \<open>hp_insert = (\<lambda>i w arr. do {
  let h = source_node arr;
  if h = None then do {
    ASSERT (i \<in> fst arr);
    let arr = (hp_set_all' i None None None None (Some w) arr);
    RETURN (update_source_node (Some i) arr)
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
      ASSERT (j \<in> fst arr);
      let arr = hp_update_parents' j (Some i) arr;
      RETURN (update_source_node (Some i) arr)
    }
    else do {
      let child = hp_read_child' j arr;
      ASSERT (child \<noteq> None \<longrightarrow> the child \<in> fst arr);
      let arr = hp_set_all' j None None (Some i) None (Some y) arr;
      ASSERT (i \<in> fst arr);
      let arr = hp_set_all' i None child None (Some j) (Some (w)) arr;
      ASSERT (child \<noteq> None \<longrightarrow> the child \<in> fst arr);
      let arr = (if child = None then arr else hp_update_prev' (the child) (Some i) arr);
      ASSERT (child \<noteq> None \<longrightarrow> the child \<in> fst arr);
      let arr = (if child = None then arr else hp_update_parents' (the child) None arr);
      RETURN arr
    }
   }
        })\<close> (is \<open>?A = ?B\<close>)
proof -
  have \<open>?A i w arr \<le> \<Down>Id (?B i w arr)\<close> for i w arr
    unfolding hp_insert_def
    by refine_vcg (solves \<open>auto intro!: simp: Let_def\<close>)+
  moreover have \<open>?B i w arr \<le> \<Down>Id (?A i w arr)\<close> for i w arr
    unfolding hp_insert_def
    by refine_vcg (auto intro!: ext bind_cong[OF refl] simp: Let_def)
  ultimately show ?thesis unfolding Down_id_eq apply -
    apply (intro ext)
    apply (rule antisym)
    apply assumption+
    done
qed

definition mop_hp_update_prev'_imp :: \<open>nat \<Rightarrow> 'a option \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> ('a,'b)pairing_heaps_imp nres\<close> where
  \<open>mop_hp_update_prev'_imp = (\<lambda>i v (prevs, nxts, parents, children). do {
    ASSERT (i < length prevs);
    RETURN (prevs[i:=v], nxts, parents, children)
  })\<close>


lemma mop_hp_update_prev'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow>
  mop_hp_update_prev'_imp i p' xs \<le> SPEC (\<lambda>a. (a, hp_update_prev' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding mop_hp_update_prev'_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def hp_update_prev_def)
  subgoal
    by (force simp: pairing_heaps_rel_def map_fun_rel_def hp_update_prev_def)
  done

definition mop_hp_update_parent'_imp :: \<open>nat \<Rightarrow> 'a option \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> ('a,'b)pairing_heaps_imp nres\<close> where
  \<open>mop_hp_update_parent'_imp = (\<lambda>i v (prevs, nxts,children, parents, scores). do {
    ASSERT (i < length parents);
    RETURN (prevs, nxts, children, parents[i:=v], scores)
  })\<close>


lemma mop_hp_update_parent'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow>
  mop_hp_update_parent'_imp i p' xs \<le> SPEC (\<lambda>a. (a, hp_update_parents' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding mop_hp_update_parent'_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def hp_update_parents_def)
  subgoal
    by (force simp: pairing_heaps_rel_def map_fun_rel_def hp_update_parents_def)
  done


definition mop_hp_update_nxt'_imp :: \<open>nat \<Rightarrow> 'a option \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> ('a,'b)pairing_heaps_imp nres\<close> where
  \<open>mop_hp_update_nxt'_imp = (\<lambda>i v (prevs, nxts, parents, children). do {
    ASSERT (i < length nxts);
    RETURN (prevs, nxts[i:=v], parents, children)
  })\<close>


lemma mop_hp_update_nxt'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow>
  mop_hp_update_nxt'_imp i p' xs \<le> SPEC (\<lambda>a. (a, hp_update_nxt' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding mop_hp_update_nxt'_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def hp_update_prev_def)
  subgoal
    by (force simp: pairing_heaps_rel_def map_fun_rel_def hp_update_nxt_def)
  done

definition mop_hp_update_score_imp :: \<open>nat \<Rightarrow> 'b \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> ('a,'b)pairing_heaps_imp nres\<close> where
  \<open>mop_hp_update_score_imp = (\<lambda>i v (prevs, nxts, parents, children, scores, h). do {
    ASSERT (i < length scores);
    RETURN (prevs, nxts, parents, children, scores[i:=v], h)
  })\<close>


lemma mop_hp_update_score_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow>
   (Some p', p)\<in>S \<Longrightarrow>
  mop_hp_update_score_imp i p' xs \<le> SPEC (\<lambda>a. (a, hp_update_score' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding mop_hp_update_score_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def hp_update_prev_def)
  subgoal
    by (force simp: pairing_heaps_rel_def map_fun_rel_def hp_update_score_def)
  done


definition mop_hp_update_child'_imp :: \<open>nat \<Rightarrow> 'a option \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> ('a,'b)pairing_heaps_imp nres\<close> where
  \<open>mop_hp_update_child'_imp = (\<lambda>i v (prevs, nxts, children, parents, scores). do {
    ASSERT (i < length children);
    RETURN (prevs, nxts, children[i:=v], parents, scores)
  })\<close>


lemma mop_hp_update_child'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow>
  mop_hp_update_child'_imp i p' xs \<le> SPEC (\<lambda>a. (a, hp_update_child' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding mop_hp_update_child'_imp_def
  apply refine_vcg
  subgoal
    by (auto simp: pairing_heaps_rel_def map_fun_rel_def hp_update_prev_def)
  subgoal
    by (force simp add: pairing_heaps_rel_def map_fun_rel_def hp_update_child_def)
  done

(*TODO it is kind of unclear whether we should use nat or have a conversion 'a \<Rightarrow> nat as locale*)
definition mop_hp_insert_impl :: \<open>nat \<Rightarrow> 'b::linorder \<Rightarrow> (nat,'b)pairing_heaps_imp \<Rightarrow> (nat,'b)pairing_heaps_imp nres\<close> where
  \<open>mop_hp_insert_impl = (\<lambda>i (w::'b) (arr :: (nat,'b)pairing_heaps_imp). do {
  let h = source_node_impl arr;
  if h = None then do {
    arr \<leftarrow> mop_hp_set_all_imp i None None None None w arr;
    RETURN (update_source_node_impl (Some i) arr)
   } else do {
    ASSERT (op_hp_read_prev_imp i arr = None);
    ASSERT (op_hp_read_parent_imp i arr = None);
    let j = (the h);
    ASSERT (op_hp_read_prev_imp j arr = None \<and> op_hp_read_nxt_imp j arr = None \<and> op_hp_read_parent_imp j arr = None);
    y \<leftarrow> mop_hp_read_score_imp j arr;
    if y < w
    then do {
      arr \<leftarrow> mop_hp_set_all_imp i None None (Some j) None ((w)) (arr);
      arr\<leftarrow> mop_hp_update_parent'_imp j (Some i) arr;
      RETURN (update_source_node_impl (Some i) arr)
    }
    else do {
      child \<leftarrow> mop_hp_read_child_imp j arr;
      arr \<leftarrow> mop_hp_set_all_imp j None None (Some i) None (y) arr;
      arr \<leftarrow> mop_hp_set_all_imp i None child None (Some j) w arr;
      arr \<leftarrow> (if child = None then RETURN arr else mop_hp_update_prev'_imp (the child) (Some i) arr);
      arr \<leftarrow> (if child = None then RETURN arr else mop_hp_update_parent'_imp (the child) None arr);
      RETURN arr
    }
   }
  })\<close>

lemma Some_x_y_option_theD: \<open>(Some x, y) \<in> \<langle>S\<rangle>option_rel \<Longrightarrow> (x, the y) \<in> S\<close>
  by (auto simp: option_rel_def)

context
begin
private lemma in_pairing_heaps_rel_still: \<open>(arra, arr') \<in> \<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>S\<rangle>option_rel\<rangle>pairing_heaps_rel \<Longrightarrow> arr' = arr'' \<Longrightarrow>
    (arra, arr'') \<in> \<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>S\<rangle>option_rel\<rangle>pairing_heaps_rel\<close>
  by auto


lemma mop_hp_insert_impl_spec:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close> \<open>(i,j)\<in>nat_rel\<close> \<open>(w,w')\<in>nat_rel\<close>
  shows \<open>mop_hp_insert_impl i w xs \<le> \<Down>(\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel) (hp_insert j w' ys)\<close>
proof -
  have [refine]: \<open>(Some i, Some j) \<in> \<langle>nat_rel\<rangle>option_rel\<close>
    using assms by auto
  have K: \<open>hp_read_child' (the (source_node ys)) ys \<noteq> None \<longrightarrow>
    the (hp_read_child' (the (source_node ys)) ys) \<in> \<V> \<Longrightarrow> the (source_node ys) \<in> fst ys \<Longrightarrow>
    op_hp_read_child_imp (the (source_node_impl xs)) xs \<noteq> None \<Longrightarrow>
    the (op_hp_read_child_imp (the (source_node ys)) xs) \<in> \<V>\<close> for \<V>
    using op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
      source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] assms
    by auto
  show ?thesis
    using assms
    unfolding mop_hp_insert_impl_def hp_insert_alt_def
    apply (refine_vcg mop_hp_set_all_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_score_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and ys=ys and j=\<open>the (source_node_impl xs)\<close>]
      Some_x_y_option_theD[where S=nat_rel]
      mop_hp_update_parent'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_child_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_update_prev'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and j=\<open>the (hp_read_child' (the (source_node ys)) ys)\<close>])
    subgoal by (auto dest: source_node_spec)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!: update_source_node_impl_spec simp: refl_on_def)
    subgoal by (auto dest!: op_hp_read_prev_imp_spec)
    subgoal by (auto dest!: op_hp_read_parent_imp_spec)
    subgoal
      using op_hp_read_parent_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
        source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      apply auto
      by (metis op_hp_read_prev_imp_spec pair_in_Id_conv)
    subgoal
      using op_hp_read_nxt_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
        source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by auto
    subgoal
      using op_hp_read_parent_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
        source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by auto
    subgoal by auto
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by auto
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by auto
    subgoal by auto
    subgoal by auto
    subgoal using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] by auto
    subgoal by (auto intro!: update_source_node_impl_spec)
    subgoal using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] by auto
    subgoal by (auto intro!: update_source_node_impl_spec)
    subgoal using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal HH
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
        op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
      by auto
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] by auto
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] by auto
    subgoal using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] by auto
    subgoal by auto
    apply (rule in_pairing_heaps_rel_still, assumption)
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal
      using op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by (metis HH option.collapse)
    subgoal
      using HH by auto
    apply (rule in_pairing_heaps_rel_still, assumption)
    subgoal
      by auto
    apply (assumption)
    apply (rule K)
    apply assumption
    subgoal by auto
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
        op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
      by auto
    subgoal
      apply (frule K)
      by auto
       (metis BNF_Greatest_Fixpoint.IdD assms(1) op_hp_read_child_imp_spec option_rel_simp(3) source_node_spec)+
    apply (rule autoref_opt(1))
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
        op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
       by auto
    subgoal by auto
    done
qed

lemma hp_link_alt_def:
   \<open>hp_link = (\<lambda>(i::'a) j arr. do {
    ASSERT (i \<noteq> j);
    ASSERT (i \<in> fst arr);
    ASSERT (j \<in> fst arr);
    ASSERT (hp_read_score' i arr \<noteq> None);
    ASSERT (hp_read_score' j arr \<noteq> None);
    let x = (the (hp_read_score' i arr)::'b::order);
    let y = (the (hp_read_score' j arr)::'b);
    let prev = hp_read_prev' i arr;
    let nxt = hp_read_nxt' j arr;
    ASSERT (nxt \<noteq> Some i \<and> nxt \<noteq> Some j);
    ASSERT (prev \<noteq> Some i \<and> prev \<noteq> Some j);
    let (parent,ch,w\<^sub>p, w\<^sub>c\<^sub>h) = (if y < x then (i, j, x, y) else (j, i, y, x));
    ASSERT (parent \<in> fst arr);
    ASSERT (ch \<in> fst arr);
    let child = hp_read_child' parent arr;
    ASSERT (child \<noteq> Some i \<and> child \<noteq> Some j);
    let child\<^sub>c\<^sub>h = hp_read_child' ch arr;
    ASSERT (child\<^sub>c\<^sub>h \<noteq> Some i \<and> child\<^sub>c\<^sub>h \<noteq> Some j \<and> (child\<^sub>c\<^sub>h \<noteq> None \<longrightarrow> child\<^sub>c\<^sub>h \<noteq> child));
    ASSERT (distinct ([i, j] @ (if child\<^sub>c\<^sub>h \<noteq> None then [the child\<^sub>c\<^sub>h] else [])
      @ (if child \<noteq> None then [the child] else [])
      @ (if prev \<noteq> None then [the prev] else [])
      @ (if nxt \<noteq> None then [the nxt] else []))
      );
    ASSERT (ch \<in> fst arr);
    ASSERT (parent \<in> fst arr);
    ASSERT (child \<noteq> None \<longrightarrow> the child \<in> fst arr);
    ASSERT (nxt \<noteq> None \<longrightarrow> the nxt \<in> fst arr);
    ASSERT (prev \<noteq> None \<longrightarrow> the prev \<in> fst arr);
    let arr = hp_set_all' parent prev nxt (Some ch) None (Some (w\<^sub>p::'b)) arr;
    let arr = hp_set_all' ch None child child\<^sub>c\<^sub>h (Some parent) (Some (w\<^sub>c\<^sub>h::'b)) arr;
    let arr = (if child = None then arr else hp_update_prev' (the child) (Some ch) arr);
    let arr = (if nxt = None then arr else hp_update_prev' (the nxt) (Some parent) arr);
    let arr = (if prev = None then arr else hp_update_nxt' (the prev) (Some parent) arr);
    let arr = (if child = None then arr else hp_update_parents' (the child) None arr);
    RETURN (arr, parent)
 })\<close> (is \<open>?A = ?B\<close>)
proof -
  define f where \<open>f i j x y \<equiv> (if y < x then (i::'a, j::'a, x::'b, y::'b) else (j, i, y, x))\<close> for i j x y
  have \<open>?A i j arr \<le> \<Down>Id (?B i j arr)\<close> for i arr j
    unfolding hp_link_def f_def[symmetric]
    apply refine_vcg
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by simp (metis option.simps(2))
    done
  moreover have \<open>?B i j arr \<le> \<Down>Id (?A i j arr)\<close> for i j arr
    unfolding hp_link_def case_prod_beta f_def[symmetric]
    apply refine_vcg
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: f_def)
    subgoal by (auto simp: f_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (cases arr) simp
    done
  ultimately show ?thesis unfolding Down_id_eq apply -
    apply (intro ext)
    apply (rule antisym)
    apply assumption+
    done
qed


definition maybe_mop_hp_update_prev'_imp where
  \<open>maybe_mop_hp_update_prev'_imp child ch arr =
     (if child = None then RETURN arr else mop_hp_update_prev'_imp (the child) ch arr)\<close>

definition maybe_mop_hp_update_nxt'_imp where
  \<open>maybe_mop_hp_update_nxt'_imp child ch arr =
     (if child = None then RETURN arr else mop_hp_update_nxt'_imp (the child) ch arr)\<close>

definition maybe_mop_hp_update_child'_imp where
  \<open>maybe_mop_hp_update_child'_imp child ch arr =
     (if child = None then RETURN arr else mop_hp_update_child'_imp (the child) ch arr)\<close>

definition maybe_mop_hp_update_parent'_imp where
  \<open>maybe_mop_hp_update_parent'_imp child ch arr =
     (if child = None then RETURN arr else mop_hp_update_parent'_imp (the child) ch arr)\<close>

lemma maybe_mop_hp_update_prev'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>\<langle>nat_rel\<rangle>option_rel \<Longrightarrow> (j \<noteq> None \<Longrightarrow> the j \<in> fst ys) \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow>
  maybe_mop_hp_update_prev'_imp i p' xs \<le> SPEC (\<lambda>a. (a, maybe_hp_update_prev' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding maybe_mop_hp_update_prev'_imp_def maybe_hp_update_prev'_def
  by (refine_vcg mop_hp_update_prev'_imp_spec) auto

lemma maybe_mop_hp_update_nxt'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>\<langle>nat_rel\<rangle>option_rel \<Longrightarrow> (j \<noteq> None \<Longrightarrow> the j \<in> fst ys) \<Longrightarrow> 
   (p',p)\<in>R \<Longrightarrow>
  maybe_mop_hp_update_nxt'_imp i p' xs \<le> SPEC (\<lambda>a. (a, maybe_hp_update_nxt' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding maybe_mop_hp_update_nxt'_imp_def maybe_hp_update_nxt'_def
  by (refine_vcg mop_hp_update_nxt'_imp_spec) auto

lemma maybe_mop_hp_update_parent'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>\<langle>nat_rel\<rangle>option_rel \<Longrightarrow> (j \<noteq> None \<Longrightarrow> the j \<in> fst ys) \<Longrightarrow>
   (p',p)\<in>R \<Longrightarrow>
  maybe_mop_hp_update_parent'_imp i p' xs \<le> SPEC (\<lambda>a. (a, maybe_hp_update_parents' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding maybe_mop_hp_update_parent'_imp_def maybe_hp_update_parents'_def
  by (refine_vcg mop_hp_update_parent'_imp_spec) auto

lemma maybe_mop_hp_update_child'_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> (i,j)\<in>\<langle>nat_rel\<rangle>option_rel \<Longrightarrow> (j \<noteq> None \<Longrightarrow> the j \<in> fst ys) \<Longrightarrow> 
   (p',p)\<in>R \<Longrightarrow>
  maybe_mop_hp_update_child'_imp i p' xs \<le> SPEC (\<lambda>a. (a, maybe_hp_update_child' j p ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel)\<close>
  unfolding maybe_mop_hp_update_child'_imp_def maybe_hp_update_child'_def
  by (refine_vcg mop_hp_update_child'_imp_spec) auto

definition mop_hp_link_imp  :: \<open>nat \<Rightarrow>nat \<Rightarrow>(nat, 'b::ord)pairing_heaps_imp \<Rightarrow> _ nres\<close> where
   \<open>mop_hp_link_imp = (\<lambda>i j arr. do {
    ASSERT (i \<noteq> j);
    x \<leftarrow> mop_hp_read_score_imp i arr;
    y \<leftarrow> mop_hp_read_score_imp j arr;
    prev \<leftarrow> mop_hp_read_prev_imp i arr;
    nxt \<leftarrow> mop_hp_read_nxt_imp j arr;
    let (parent,ch,w\<^sub>p, w\<^sub>c\<^sub>h) = (if y < x then (i, j, x, y) else (j, i, y, x));
    child \<leftarrow> mop_hp_read_child_imp parent arr;
    child\<^sub>c\<^sub>h \<leftarrow> mop_hp_read_child_imp ch arr;
    arr \<leftarrow> mop_hp_set_all_imp parent prev nxt (Some ch) None ((w\<^sub>p)) arr;
    arr \<leftarrow> mop_hp_set_all_imp ch None child child\<^sub>c\<^sub>h (Some parent) ((w\<^sub>c\<^sub>h)) arr;
    arr \<leftarrow> (if child = None then RETURN arr else mop_hp_update_prev'_imp (the child) (Some ch) arr);
    arr \<leftarrow> (if nxt = None then RETURN arr else mop_hp_update_prev'_imp (the nxt) (Some parent) arr);
    arr \<leftarrow> (if prev = None then RETURN arr else mop_hp_update_nxt'_imp (the prev) (Some parent) arr);
    arr \<leftarrow> (if child = None then RETURN arr else mop_hp_update_parent'_imp (the child) None arr);
    RETURN (arr, parent)
      })\<close>

lemma mop_hp_link_imp_spec:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close> \<open>(i,j)\<in>nat_rel\<close> \<open>(w,w')\<in>nat_rel\<close>
  shows \<open>mop_hp_link_imp i w xs \<le> \<Down>(\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<times>\<^sub>r nat_rel) (hp_link j w' ys)\<close>
proof -
  have [refine]: \<open>(Some i, Some j) \<in> \<langle>nat_rel\<rangle>option_rel\<close>
    using assms by auto
  define f where \<open>f i j x y \<equiv> RETURN (if y < x then (i::nat, j::nat, x::nat, y::nat) else (j, i, y, x))\<close> for i j x y
  have Hf: \<open>do {let (parent, ch, w\<^sub>p, w\<^sub>c\<^sub>h) = (if y < x then (i, j, x, y) else (j, i, y, x)); P parent ch w\<^sub>p w\<^sub>c\<^sub>h} =
    do {(parent, ch, w\<^sub>p, w\<^sub>c\<^sub>h) \<leftarrow> f i j x y; P parent ch w\<^sub>p w\<^sub>c\<^sub>h}\<close> for i j x y w xs P
    unfolding f_def let_to_bind_conv ..

  have K: \<open>hp_read_child' (the (source_node ys)) ys \<noteq> None \<longrightarrow>
    the (hp_read_child' (the (source_node ys)) ys) \<in> \<V> \<Longrightarrow> the (source_node ys) \<in> fst ys \<Longrightarrow>
    op_hp_read_child_imp (the (source_node_impl xs)) xs \<noteq> None \<Longrightarrow>
    the (op_hp_read_child_imp (the (source_node ys)) xs) \<in> \<V>\<close> for \<V>
    using op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
      source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] assms
    by auto
  have [refine]: \<open>(x,x')\<in>nat_rel \<Longrightarrow> (y,y')\<in>nat_rel\<Longrightarrow>
    f i w x y \<le> \<Down> (nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel) (f j w' x' y')\<close> for x' y' x y
   using assms by auto
  show ?thesis
    using assms
      op_hp_read_nxt_imp_spec[OF assms(1) assms(2)]
      op_hp_read_prev_imp_spec[OF assms(1) assms(2)]
      op_hp_read_child_imp_spec[OF assms(1) assms(2)]
      op_hp_read_nxt_imp_spec[OF assms(1) assms(3)]
    unfolding mop_hp_link_imp_def hp_link_alt_def Hf
      maybe_mop_hp_update_parent'_imp_def[symmetric]
      maybe_mop_hp_update_prev'_imp_def[symmetric]
      maybe_mop_hp_update_nxt'_imp_def[symmetric]
      maybe_hp_update_prev'_def[symmetric]
      maybe_hp_update_parents'_def[symmetric]
      maybe_hp_update_nxt'_def[symmetric]
    apply -
    apply (refine_vcg mop_hp_set_all_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_score_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and ys=ys and i=i and j=j]
      mop_hp_read_score_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and ys=ys and i=w and j=w']
      Some_x_y_option_theD[where S=nat_rel]
      mop_hp_update_parent'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_update_prev'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and j=\<open>the (hp_read_child' (the (source_node ys)) ys)\<close>]
      maybe_mop_hp_update_parent'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      maybe_mop_hp_update_prev'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      maybe_mop_hp_update_nxt'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_child_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_prev_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_nxt_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_parent_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>])
    subgoal by (auto dest: source_node_spec)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (solves auto)
    subgoal by auto
    subgoal by auto
    apply (solves auto)
    subgoal by simp
    apply (solves auto)
    apply (solves auto)
    done
qed

lemma vsids_pass\<^sub>1_alt_def:
  \<open>vsids_pass\<^sub>1 = (\<lambda>(arr::'a set \<times> ('a,'c::order) hp_fun \<times> 'a option) (j::'a). do {
  (arr, j, _, n) \<leftarrow> WHILE\<^sub>T(\<lambda>(arr, j,_, _). j \<noteq> None)
  (\<lambda>(arr, j, e::nat, n). do {
    if j = None then RETURN (arr, None, e, n)
    else do {
    let j = the j;
    ASSERT (j \<in> fst arr);
    let nxt = hp_read_nxt' j arr;
    if nxt = None then RETURN (arr, nxt, e+1, j)
    else do {
      ASSERT (nxt \<noteq> None);
      ASSERT (the nxt \<in> fst arr);
      let nnxt = hp_read_nxt' (the nxt) arr;
      (arr, n) \<leftarrow> hp_link j (the nxt) arr;
      RETURN (arr, nnxt, e+2, n)
   }}
  })
  (arr, Some j, 0::nat, j);
  RETURN (arr, n)
        })\<close> (is \<open>?A = ?B\<close>)
proof -
  have K[refine]: \<open>x2 = (x1a, x2a) \<Longrightarrow> i = (x1, x2) \<Longrightarrow>
    (((x1, x1a, x2a), Some arr, 0, arr), i::'a set \<times> ('a,'c::order) hp_fun \<times> 'a option, Some arr, 0::nat, arr)
    \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r Id\<close>
    \<open>\<And>x1 x2 x1a x2a.
    x2 = (x1a, x2a) \<Longrightarrow>
    i = (x1, x2) \<Longrightarrow>
    ((i, Some arr, 0, arr), (x1, x1a, x2a), Some arr, 0, arr)
    \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r Id\<close>

    for x2 x1a x2a arr x1 i
    by auto
  have [refine]: \<open>(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> hp_link a b c \<le>\<Down>Id (hp_link a' b' c')\<close> for a b c a' b' c'
    by auto
  have \<open>?A i arr \<le> \<Down>Id (?B i arr)\<close> for i arr
    unfolding vsids_pass\<^sub>1_def
    by refine_vcg (solves auto)+
  moreover have \<open>?B i arr \<le> \<Down>Id (?A i arr)\<close> for i arr
    unfolding vsids_pass\<^sub>1_def
    by refine_vcg (solves \<open>auto intro!: ext bind_cong[OF refl] simp: Let_def\<close>)+
  ultimately show ?thesis unfolding Down_id_eq apply -
    apply (intro ext)
    apply (rule antisym)
    apply assumption+
    done
qed

definition mop_vsids_pass\<^sub>1_imp :: \<open>(nat, 'b::ord)pairing_heaps_imp \<Rightarrow> nat \<Rightarrow> _ nres\<close> where
  \<open>mop_vsids_pass\<^sub>1_imp = (\<lambda>arr j. do {
  (arr, j, n) \<leftarrow> WHILE\<^sub>T(\<lambda>(arr, j, _). j \<noteq> None)
  (\<lambda>(arr, j, n). do {
    if j = None then RETURN (arr, None, n)
    else do {
    let j = the j;
    nxt \<leftarrow> mop_hp_read_nxt_imp j arr;
    if nxt = None then RETURN (arr, nxt, j)
    else do {
      ASSERT (nxt \<noteq> None);
      nnxt \<leftarrow> mop_hp_read_nxt_imp (the nxt) arr;
      (arr, n) \<leftarrow> mop_hp_link_imp j (the nxt) arr;
      RETURN (arr, nnxt, n)
   }}
  })
  (arr, Some j, j);
  RETURN (arr, n)
 })\<close>


lemma mop_vsids_pass\<^sub>1_imp_spec:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close> \<open>(i,j)\<in>nat_rel\<close>
  shows \<open>mop_vsids_pass\<^sub>1_imp xs i \<le> \<Down>(\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<times>\<^sub>r nat_rel) (vsids_pass\<^sub>1 ys j)\<close>
proof -
  let ?R = \<open>{((arr, j, n), (arr', j', _, n')). (arr, arr') \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<and>
    (j, j') \<in> \<langle>nat_rel\<rangle>option_rel \<and> (n,n')\<in>Id}\<close>
  have K[refine0]: \<open>((xs, Some i, i), ys, Some j, 0, j) \<in> ?R\<close>
    using assms by auto
  show ?thesis
    unfolding mop_vsids_pass\<^sub>1_imp_def vsids_pass\<^sub>1_alt_def
    apply (refine_vcg mop_hp_insert_impl_spec WHILET_refine[where R= ?R]
      mop_hp_read_nxt_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_link_imp_spec)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma vsids_pass\<^sub>2_alt_def:
  \<open>vsids_pass\<^sub>2 = (\<lambda>arr (j::'a). do {
  ASSERT (j \<in> fst arr);
  let nxt = hp_read_prev' j arr;
  (arr, j, leader, _) \<leftarrow> WHILE\<^sub>T(\<lambda>(arr, j, leader, e). j \<noteq> None)
  (\<lambda>(arr, j, leader, e::nat). do {
    if j = None then RETURN (arr, None, leader, e)
    else do {
      let j = the j;
      ASSERT (j \<in> fst arr);
      let nnxt = hp_read_prev' j arr;
      (arr, n) \<leftarrow> hp_link j leader arr;
      RETURN (arr, nnxt, n, e+1)
   }
  })
  (arr, nxt, j, 1::nat);
  RETURN (update_source_node (Some leader) arr)
  })\<close> (is \<open>?A = ?B\<close>)
proof -
  have K[refine]: \<open>(((fst i, fst (snd i), snd (snd i)), hp_read_prev arr (fst (snd i)), arr, 1::nat), i,
  hp_read_prev' arr i, arr, 1::nat)
    \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    \<open>((i, hp_read_prev' arr i, arr, 1), (fst i, fst (snd i), snd (snd i)),
  hp_read_prev arr (fst (snd i)), arr, 1) \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    for i arr
    by auto
  have [refine]: \<open>(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> hp_link a b c \<le>\<Down>Id (hp_link a' b' c')\<close> for a b c a' b' c'
    by auto
  have \<open>?A i arr \<le> \<Down>Id (?B i arr)\<close> for i arr
    unfolding vsids_pass\<^sub>2_def case_prod_beta[of _ i] case_prod_beta[of _ \<open>snd i\<close>]
    by refine_vcg (solves auto)+
  moreover have \<open>?B i arr \<le> \<Down>Id (?A i arr)\<close> for i arr
    unfolding vsids_pass\<^sub>2_def case_prod_beta[of _ i] case_prod_beta[of _ \<open>snd i\<close>]
    by refine_vcg (solves \<open>auto intro!: ext bind_cong[OF refl] simp: Let_def\<close>)+
  ultimately show ?thesis unfolding Down_id_eq apply -
    apply (intro ext)
    apply (rule antisym)
    apply assumption+
    done
qed

definition mop_vsids_pass\<^sub>2_imp where
  \<open>mop_vsids_pass\<^sub>2_imp = (\<lambda>arr (j::nat). do {
  nxt \<leftarrow> mop_hp_read_prev_imp j arr;
  (arr, j, leader) \<leftarrow> WHILE\<^sub>T(\<lambda>(arr, j, leader). j \<noteq> None)
  (\<lambda>(arr, j, leader). do {
    if j = None then RETURN (arr, None, leader)
    else do {
      let j = the j;
      nnxt \<leftarrow> mop_hp_read_prev_imp j arr;
      (arr, n) \<leftarrow> mop_hp_link_imp j leader arr;
      RETURN (arr, nnxt, n)
   }
  })
  (arr, nxt, j);
  RETURN (update_source_node_impl (Some leader) arr)
  })\<close>

lemma mop_vsids_pass\<^sub>2_imp_spec:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close> \<open>(i,j)\<in>nat_rel\<close>
  shows \<open>mop_vsids_pass\<^sub>2_imp xs i \<le> \<Down>(\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel) (vsids_pass\<^sub>2 ys j)\<close>
proof -
  let ?R = \<open>{((arr, j, n), (arr', j', n', _)). (arr, arr') \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<and>
    (j, j') \<in> \<langle>nat_rel\<rangle>option_rel \<and> (n,n')\<in>Id}\<close>
  have K[refine0]: \<open>((xs, Some i, i), ys, Some j, j, 0) \<in> ?R\<close>
    using assms by auto
  show ?thesis
    using assms
    unfolding mop_vsids_pass\<^sub>2_imp_def vsids_pass\<^sub>2_alt_def
    apply (refine_vcg mop_hp_insert_impl_spec WHILET_refine[where R= ?R]
      mop_hp_read_nxt_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_prev_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_link_imp_spec mop_vsids_pass\<^sub>1_imp_spec
      update_source_node_impl_spec)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition mop_merge_pairs_imp where
  \<open>mop_merge_pairs_imp arr j = do {
    (arr, j) \<leftarrow> mop_vsids_pass\<^sub>1_imp arr j;
    mop_vsids_pass\<^sub>2_imp arr j
  }\<close>


lemma mop_merge_pairs_imp_spec:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close> \<open>(i,j)\<in>nat_rel\<close>
  shows \<open>mop_merge_pairs_imp xs i \<le> \<Down>(\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel) (merge_pairs ys j)\<close>
  using assms unfolding mop_merge_pairs_imp_def merge_pairs_def
  by (refine_vcg mop_vsids_pass\<^sub>1_imp_spec mop_vsids_pass\<^sub>2_imp_spec) auto

lemma vsids_pop_min_alt_def:
  \<open>vsids_pop_min = (\<lambda>arr. do {
  let h = source_node arr;
  if h = None then RETURN (None, arr)
  else do {
      ASSERT (the h \<in> fst arr);
      let j = hp_read_child' (the h) arr;
      if j = None then RETURN (h, (update_source_node None arr))
      else do {
        ASSERT (the j \<in> fst arr);
        let arr = hp_update_prev' (the h) None arr;
        let arr = hp_update_child' (the h) None arr;
        let arr = hp_update_parents' (the j) None arr;
        arr \<leftarrow> merge_pairs (update_source_node None arr) (the j);
        RETURN (h, arr)
      }
    }
  })\<close> (is \<open>?A = ?B\<close>)
proof -
  have [simp]: \<open>source_node arr = None \<Longrightarrow> (fst arr, fst (snd arr), None) = arr\<close> for arr
    by (cases arr) auto
  have K[refine]: \<open>((source_node arr, fst arr, fst (snd arr), None), source_node arr,
  update_source_node None arr)
    \<in> Id\<close>
    \<open>((source_node arr, update_source_node None arr), source_node arr, fst arr, fst (snd arr), None)
    \<in> Id\<close>
    for i arr
    by (solves \<open>cases arr; auto\<close>)+
  have [refine]: \<open>merge_pairs
  (fst arr,
   hp_update_parents (the (hp_read_child (the (source_node arr)) (fst (snd arr))))
    None
    (hp_update_child (the (source_node arr)) None
      (hp_update_prev (the (source_node arr)) None (fst (snd arr)))),
   None)
  (the (hp_read_child (the (source_node arr)) (fst (snd arr))))
    \<le> \<Down> Id
    (merge_pairs
      (update_source_node None
     (hp_update_parents' (the (hp_read_child' (the (source_node arr)) arr)) None
       (hp_update_child' (the (source_node arr)) None
      (hp_update_prev' (the (source_node arr)) None arr))))
    (the (hp_read_child' (the (source_node arr)) arr)))\<close>
    \<open>merge_pairs
   (update_source_node None
  (hp_update_parents' (the (hp_read_child' (the (source_node arr)) arr)) None
    (hp_update_child' (the (source_node arr)) None
      (hp_update_prev' (the (source_node arr)) None arr))))
   (the (hp_read_child' (the (source_node arr)) arr))
  \<le> \<Down> Id
  (merge_pairs
    (fst arr,
     hp_update_parents (the (hp_read_child (the (source_node arr)) (fst (snd arr)))) None
      (hp_update_child (the (source_node arr)) None
     (hp_update_prev (the (source_node arr)) None (fst (snd arr)))),
     None)
    (the (hp_read_child (the (source_node arr)) (fst (snd arr)))))\<close> for arr
    by (solves \<open>cases arr; auto\<close>)+
  have K: \<open>snd (snd arr) = source_node arr\<close> for arr
    by (cases arr) auto

  have \<open>?A arr \<le> \<Down>Id (?B arr)\<close> for i arr
    unfolding vsids_pop_min_def case_prod_beta[of _ arr] case_prod_beta[of _ \<open>snd arr\<close>]
      K
    by refine_vcg (solves auto)+
  moreover have \<open>?B arr \<le> \<Down>Id (?A arr)\<close> for i arr
    unfolding vsids_pop_min_def case_prod_beta[of _ arr] case_prod_beta[of _ \<open>snd arr\<close>] K
    by refine_vcg (solves \<open>auto intro!: ext bind_cong[OF refl] simp: Let_def\<close>)+
  ultimately show ?thesis unfolding Down_id_eq apply -
    apply (intro ext)
    apply (rule antisym)
    apply assumption+
    done
qed


definition mop_vsids_pop_min_impl where
    \<open>mop_vsids_pop_min_impl = (\<lambda>arr. do {
  let h = source_node_impl arr;
  if h = None then RETURN (None, arr)
  else do {
      j \<leftarrow> mop_hp_read_child_imp (the h) arr;
      if j = None then RETURN (h, update_source_node_impl None arr)
      else do {
        arr \<leftarrow> mop_hp_update_prev'_imp (the h) None arr;
        arr \<leftarrow> mop_hp_update_child'_imp (the h) None arr;
        arr \<leftarrow> mop_hp_update_parent'_imp (the j) None arr;
        arr \<leftarrow> mop_merge_pairs_imp (update_source_node_impl None arr) (the j);
        RETURN (h, arr)
      }
    }
  })\<close>


lemma mop_vsids_pop_min_impl:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close>
  shows \<open>mop_vsids_pop_min_impl xs \<le> \<Down>(\<langle>nat_rel\<rangle>option_rel \<times>\<^sub>r \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel) (vsids_pop_min ys)\<close>
proof -
  let ?R = \<open>{((arr, j, n), (arr', j', n', _)). (arr, arr') \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<and>
    (j, j') \<in> \<langle>nat_rel\<rangle>option_rel \<and> (n,n')\<in>Id}\<close>
  have K[refine0]: \<open>(the (source_node_impl xs), the (source_node ys)) \<in> nat_rel\<close>
    if \<open>source_node ys \<noteq> None\<close>
    using source_node_spec[OF assms] by auto
  show ?thesis
    using assms source_node_spec[OF assms]
    unfolding mop_vsids_pop_min_impl_def vsids_pop_min_alt_def
    apply (refine_vcg mop_hp_insert_impl_spec WHILET_refine[where R= ?R]
      mop_hp_read_nxt_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_read_prev_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_link_imp_spec mop_vsids_pass\<^sub>1_imp_spec
      mop_merge_pairs_imp_spec
      mop_hp_read_child_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_update_prev'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_update_child'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_update_parent'_imp_spec[where R=\<open>\<langle>nat_rel\<rangle>option_rel\<close> and S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>])
   subgoal by auto
   subgoal by auto
   subgoal by auto
   subgoal by (auto intro!: update_source_node_impl_spec)
   subgoal by auto
   subgoal by auto
   subgoal by auto
   subgoal by auto
   subgoal by auto
   subgoal by auto
   subgoal by (auto intro!: update_source_node_impl_spec)
   subgoal by auto
   subgoal by auto
   done
qed

definition mop_unroot_hp_tree where
  \<open>mop_unroot_hp_tree arr h = do {
    let a = source_node_impl arr;
    nnext \<leftarrow> mop_hp_read_nxt_imp h arr;
    parent \<leftarrow> mop_hp_read_parent_imp h arr;
    prev \<leftarrow> mop_hp_read_prev_imp h arr;
    if prev = None \<and> parent = None \<and> Some h \<noteq> a then RETURN (update_source_node_impl None arr)
    else if Some h = a then RETURN (update_source_node_impl None arr)
    else do {
      ASSERT (a \<noteq> None);
      let a' = the a;
      arr \<leftarrow>  maybe_mop_hp_update_child'_imp parent nnext arr;
      arr \<leftarrow>  maybe_mop_hp_update_nxt'_imp prev nnext arr;
      arr \<leftarrow>  maybe_mop_hp_update_prev'_imp nnext prev arr;
      arr \<leftarrow>  maybe_mop_hp_update_parent'_imp nnext parent arr;

      arr \<leftarrow>  mop_hp_update_nxt'_imp h None arr;
      arr \<leftarrow>  mop_hp_update_prev'_imp h None arr;
      arr \<leftarrow>  mop_hp_update_parent'_imp h None arr;

      arr \<leftarrow>  mop_hp_update_nxt'_imp h (Some a') arr;
      arr \<leftarrow>  mop_hp_update_prev'_imp a' (Some h) arr;
      RETURN (update_source_node_impl None arr)
    }
}\<close>

lemma mop_unroot_hp_tree_spec:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close> and \<open>(h,i)\<in>nat_rel\<close>
  shows \<open>mop_unroot_hp_tree xs h \<le> \<Down>(\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel) (unroot_hp_tree ys i)\<close>
proof -
  show ?thesis
    using assms using source_node_spec[OF assms(1)]
    unfolding mop_unroot_hp_tree_def unroot_hp_tree_def
    apply (refine_rcg mop_hp_read_nxt_imp_spec assms
      mop_hp_read_parent_imp_spec mop_hp_read_prev_imp_spec
      update_source_node_impl_spec maybe_mop_hp_update_child'_imp_spec
      maybe_mop_hp_update_nxt'_imp_spec maybe_mop_hp_update_parent'_imp_spec
      maybe_mop_hp_update_prev'_imp_spec
      mop_hp_update_nxt'_imp_spec[where S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_update_prev'_imp_spec[where S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      mop_hp_update_parent'_imp_spec[where S=\<open>\<langle>nat_rel\<rangle>option_rel\<close>])
    subgoal using source_node_spec[OF assms(1)] by auto
    subgoal by auto
    subgoal using source_node_spec[OF assms(1)] by auto
    subgoal by auto
    subgoal using source_node_spec[OF assms(1)] by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition mop_rescale_and_reroot where
  \<open>mop_rescale_and_reroot h w' arr = do {
    nnext \<leftarrow> mop_hp_read_nxt_imp h arr;
    parent \<leftarrow> mop_hp_read_parent_imp h arr;
    prev \<leftarrow> mop_hp_read_prev_imp h arr;
    if source_node_impl arr = None then mop_hp_update_score_imp h w' arr
    else if prev = None \<and> parent = None \<and> Some h \<noteq> source_node_impl arr then mop_hp_update_score_imp h w' arr
    else if Some h = source_node_impl arr then mop_hp_update_score_imp h w' arr
    else do {
       arr \<leftarrow> mop_unroot_hp_tree arr h;
       arr \<leftarrow> mop_hp_update_score_imp h w' arr;
       mop_merge_pairs_imp arr h
   }
}\<close>


lemma mop_rescale_and_reroot_spec:
  assumes \<open>(xs, ys) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<close> and \<open>(h,i)\<in>nat_rel\<close> \<open>(w, w') \<in> nat_rel\<close>
  shows \<open>mop_rescale_and_reroot h w xs \<le> \<Down>(\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel) (rescale_and_reroot i w' ys)\<close>
proof -
  have [refine]: \<open>(Some w, Some w') \<in> \<langle>nat_rel\<rangle>option_rel\<close>
    using assms by auto
  show ?thesis
    using source_node_spec[OF assms(1)] assms(2,3)
    unfolding rescale_and_reroot_def mop_rescale_and_reroot_def
    apply (refine_rcg mop_hp_read_nxt_imp_spec assms mop_hp_read_parent_imp_spec
      mop_hp_read_prev_imp_spec mop_hp_update_score_imp_spec mop_unroot_hp_tree_spec
      mop_merge_pairs_imp_spec)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    done
qed

end
end
