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


definition op_hp_read_nxt_imp where
  \<open>op_hp_read_nxt_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      (nxts ! i)
  })\<close>
definition mop_hp_read_nxt_imp where
  \<open>mop_hp_read_nxt_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length nxts);
      RETURN (nxts ! i)
  })\<close>

fun hp_read_nxt' :: \<open>_\<close> where
  \<open>hp_read_nxt' i (\<V>, arr, h) = hp_read_nxt i arr\<close>

lemma op_hp_read_nxt_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  (op_hp_read_nxt_imp i xs, hp_read_nxt' j ys) \<in> R\<close>
  unfolding op_hp_read_nxt_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

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

definition op_hp_read_prev_imp where
  \<open>op_hp_read_prev_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      prevs ! i
  })\<close>

definition mop_hp_read_prev_imp where
  \<open>mop_hp_read_prev_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length prevs);
      RETURN (prevs ! i)
  })\<close>

fun hp_read_prev' :: \<open>_\<close> where
  \<open>hp_read_prev' i (\<V>, arr, h) = hp_read_prev i arr\<close>

lemma op_hp_read_prev_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  (op_hp_read_prev_imp i xs, hp_read_prev' j ys) \<in> R\<close>
  unfolding op_hp_read_prev_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

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

definition op_hp_read_child_imp where
  \<open>op_hp_read_child_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      (children ! i)
  })\<close>

definition mop_hp_read_child_imp where
  \<open>mop_hp_read_child_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ASSERT (i < length children);
      RETURN (children ! i)
  })\<close>

fun hp_read_child' :: \<open>_\<close> where
  \<open>hp_read_child' i (\<V>, arr, h) = hp_read_child i arr\<close>

lemma op_hp_read_child_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  (op_hp_read_child_imp i xs, hp_read_child' j ys) \<in> R\<close>
  unfolding op_hp_read_child_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)

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
definition op_hp_read_parent_imp where
  \<open>op_hp_read_parent_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      (parents ! i)
  })\<close>

fun hp_read_parent' :: \<open>_\<close> where
  \<open>hp_read_parent' i (\<V>, arr, h) = hp_read_parent i arr\<close>

lemma op_hp_read_parent_imp_spec:
  \<open>(xs, ys) \<in> \<langle>R,S\<rangle>pairing_heaps_rel \<Longrightarrow> j \<in> fst ys \<Longrightarrow> (i,j)\<in>nat_rel \<Longrightarrow>
  (op_hp_read_parent_imp i xs, hp_read_parent' j ys) \<in> R\<close>
  unfolding op_hp_read_parent_imp_def
  by (auto simp: pairing_heaps_rel_def map_fun_rel_def)
 
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

definition op_hp_read_score_imp :: \<open>nat \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> 'b\<close> where
  \<open>op_hp_read_score_imp = (\<lambda>i (prevs, nxts, children, parents, scores, h). do {
      ((scores ! i))
  })\<close>

definition mop_hp_read_score_imp :: \<open>nat \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> 'b nres\<close> where
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

lemma fst_hp_set_all'[simp]: \<open>fst (hp_set_all' i p q r s t x) = fst x\<close>
  by (cases x) auto

fun update_source_node where
  \<open>update_source_node i (\<V>,arr,_) = (\<V>, arr, i)\<close>
fun source_node :: \<open>(nat set \<times> (nat,'c) hp_fun \<times> nat option) \<Rightarrow> _\<close> where
  \<open>source_node (\<V>,arr,h) = h\<close>

fun update_source_node_impl :: \<open>_ \<Rightarrow> ('a,'b)pairing_heaps_imp  \<Rightarrow> ('a,'b)pairing_heaps_imp\<close> where
  \<open>update_source_node_impl i (prevs, nxts, parents, children, scores,_) = (prevs, nxts, parents, children, scores, i)\<close>

fun source_node_impl :: \<open>('a,'b)pairing_heaps_imp \<Rightarrow> 'a option\<close> where
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
  \<open>hp_update_prev' i p (\<V>, u, h) = (\<V>, hp_update_prev i p u, h)\<close>

fun hp_update_nxt' where
  \<open>hp_update_nxt' i p(\<V>, u, h) = (\<V>, hp_update_nxt i p u, h)\<close>

fun hp_update_score' where
  \<open>hp_update_score' i p(\<V>, u, h) = (\<V>, hp_update_score i p u, h)\<close>


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
      let child = op_hp_read_child_imp j arr;
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
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by auto
    subgoal by auto
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
    subgoal by auto
    subgoal using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>] by auto
    subgoal by auto
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
    subgoal by auto
    apply (rule in_pairing_heaps_rel_still, assumption)
    subgoal apply auto
      by (metis op_hp_read_child_imp_spec option.sel option.simps(3) pair_in_Id_conv source_node_spec)
    apply assumption
    subgoal apply auto
      by (metis HH fst_hp_set_all' option.distinct(1) option.sel option_rel_id_simp pair_in_Id_conv)
    subgoal
      using op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
      by (metis HH option.collapse)
    subgoal
      using HH by auto
    apply (rule in_pairing_heaps_rel_still, assumption)
    subgoal
      apply auto
      by (metis HH fst_hp_set_all' option.sel option.simps(2) option_rel_id_simp pair_in_Id_conv)
    apply (assumption)
    apply (rule K)
    apply assumption
    subgoal by auto
    subgoal by auto
    subgoal
      using source_node_spec[of xs ys  \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close>]
        op_hp_read_child_imp_spec[of xs ys \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>\<langle>nat_rel\<rangle>option_rel\<close> \<open>the (source_node ys)\<close> \<open>the (source_node_impl xs)\<close>]
      by auto
    apply (rule autoref_opt(1))
    subgoal
      apply (frule K)
      apply auto
      apply (metis K empty_iff option.distinct(2) option.sel)+
      using K by auto
    subgoal by auto
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

(*TODO next:*)
  term vsids_pass\<^sub>1
  term vsids_pass\<^sub>2
end
