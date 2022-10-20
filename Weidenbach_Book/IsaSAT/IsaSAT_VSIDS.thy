theory IsaSAT_VSIDS
  imports Watched_Literals.WB_Sort IsaSAT_Setup Ordered_Pairing_Heap_List2
  (*  IsaSAT_Literals_LLVM
    Isabelle_LLVM.IICF
    Isabelle_LLVM.LLVM_DS_Open_List
    Isabelle_LLVM.LLVM_DS_Array_List_Pure*)
begin

text \<open>We first tried to use the heapmap, but this attempt was a terrible failure, because as useful
the heapmap is parametrized by the size. This might be useful in some contexts, but I consider this
to be the most terrible idea ever, based on past experience. So instead I went for a modification
of the pairing heaps.

To increase fun, we reuse the trick from VSIDS to represent the pairing heap inside an array in
order to avoid allocation yet another array. As a side effect, it also avoids including the label
inside the node (because per definition, the label is exactly the index).
But maybe pointers are actually better, because by definition in Isabelle no graph is shared.
\<close>


fun mset_nodes :: "('b, 'a) hp \<Rightarrow>'b multiset" where
"mset_nodes (Hp x _ hs) = {#x#} + sum_mset(mset(map mset_nodes hs))"
(*TODO we need a field to say contained or not*)
inductive encoded_pairheap where
  empty: \<open>encoded_pairheap [] {#}\<close> |
  leaf: \<open>encoded_pairheap (arr[n := (x, [])]) (add_mset (Hp n x []) trees)\<close>
  if  \<open>encoded_pairheap arr trees\<close> \<open>n \<notin># \<Sum>\<^sub># (mset_nodes `# trees)\<close> and
    \<open>n < length arr\<close>|
  comb: \<open>encoded_pairheap (arr[n := (fst (arr!n), snd (arr!n)@[m])]) (add_mset (Hp n w\<^sub>n (Hp m w\<^sub>m child\<^sub>m # child\<^sub>n)) trees)\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n (child\<^sub>n)) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close>

lemma encoded_pairheap_distinct_nodes: \<open>encoded_pairheap arr trees \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# trees))\<close>
  by (induction rule: encoded_pairheap.induct)
   (auto simp: ac_simps)

lemma encoded_pairheap_change_irrelevant:
  \<open>encoded_pairheap arr trees \<Longrightarrow> n \<notin># \<Sum>\<^sub># (mset_nodes `# trees) \<Longrightarrow> encoded_pairheap (arr [n := a]) trees\<close>
  apply (induction rule: encoded_pairheap.induct)
  subgoal by (auto intro: encoded_pairheap.intros)
  subgoal for arr trees na x
    using encoded_pairheap.leaf[of \<open>arr[n := a]\<close> trees na x]
    by (auto simp add: list_update_swap)
  subgoal for arr na w\<^sub>n child\<^sub>n m w\<^sub>m child\<^sub>m trees
    using encoded_pairheap.comb[of \<open>arr[n := a]\<close> na w\<^sub>n child\<^sub>n m w\<^sub>m child\<^sub>m trees]
    by (auto simp: list_update_swap)
  done


interpretation VSIDS: pairing_heap where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done

fun nodes where
  \<open>nodes (Hp m w children) = add_mset (Hp m w children) (\<Sum>\<^sub># (nodes `# mset children))\<close>

lemma  encoded_pairheap_le_lengthI: \<open>encoded_pairheap arr trees \<Longrightarrow> m \<in># \<Sum>\<^sub># (mset_nodes `# trees) \<Longrightarrow> m < length arr\<close>
  by (induction arr trees arbitrary:  rule: encoded_pairheap.induct) auto

lemma mset_nodes_nodes: \<open>set_mset (\<Sum>\<^sub># (mset_nodes `# nodes x)) = set_mset (mset_nodes x)\<close>
  by (induction x)  (force simp: in_mset_sum_list_iff)

lemma mset_nodes_nodes_indirect: \<open>nodes x = A \<Longrightarrow> set_mset (mset_nodes x) = set_mset ( \<Sum>\<^sub>#(mset_nodes  `# A))\<close>
  unfolding mset_nodes_nodes[symmetric]
  by simp

lemma in_mset_nodes_iff: \<open>n \<in># mset_nodes x \<Longrightarrow> \<exists>m a. Hp n m a \<in># nodes x\<close>
  by (induction x)
   (fastforce simp: mset_nodes_nodes in_mset_sum_list_iff)


lemma in_sum_mset_nodes_iff: \<open>(\<exists>m a. Hp n m a \<in>#  \<Sum>\<^sub># (nodes `# trees)) \<longleftrightarrow> n \<in># \<Sum>\<^sub># (mset_nodes `# trees)\<close>
  apply (rule iffI)
  subgoal
    apply (induction trees)
    apply (auto simp: mset_nodes_nodes)
    using mset_nodes_nodes apply fastforce
    done
  subgoal
    by (induction trees)
     (auto simp: mset_nodes_nodes dest!: in_mset_nodes_iff)
  done

lemma encoded_pairheap_correct_annot:
  assumes 1: \<open>encoded_pairheap arr trees\<close> and
    \<open>Hp n m a \<in>#  \<Sum>\<^sub># (nodes `# trees)\<close>
  shows \<open>(arr ! n) = (m, rev (map node a))\<close>
proof -
  have 2: \<open>n \<in># \<Sum>\<^sub># (mset_nodes `# trees)\<close>
    by (rule in_sum_mset_nodes_iff[THEN iffD1])
     (use assms(2) in auto)
  show ?thesis
    using 1 assms(2) encoded_pairheap_le_lengthI[OF 1 2] encoded_pairheap_distinct_nodes[OF 1]
    apply (induction arr trees arbitrary:  a rule: encoded_pairheap.induct)
    subgoal by auto
    subgoal for arr trees m' w
      by auto (use in_sum_mset_nodes_iff mset_nodes_nodes in fastforce)+
    subgoal for arr na w\<^sub>n child\<^sub>n ma w\<^sub>m child\<^sub>m trees a
      apply (auto)
      apply fastforce
      apply fastforce
      apply fastforce
      apply (metis (mono_tags, opaque_lifting) add.assoc add.left_commute fst_conv)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (simp add: union_assoc union_lcomm)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (simp add: union_assoc union_lcomm)
      apply (metis (no_types, lifting) fst_conv union_assoc union_lcomm)
      apply (metis image_mset_single in_sum_mset_nodes_iff sum_mset.singleton)
      by (metis (no_types, lifting) union_assoc union_lcomm)
   done
qed

definition vsids_link where
  \<open>vsids_link arr m n = do {
     ASSERT (m < length arr);
     ASSERT (n < length arr);
     if fst (arr ! n) \<le> fst (arr ! m) then RETURN (arr[m := (fst (arr ! m), snd (arr ! m) @ [n])])
     else RETURN (arr [n := (fst (arr ! n), snd (arr ! n) @ [m])])
}\<close>


lemma vsids_link:
  assumes vsids: \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n child\<^sub>n) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close>
  shows \<open>vsids_link arr m n \<le> SPEC (\<lambda>arr'. encoded_pairheap arr' (add_mset (VSIDS.link (Hp n w\<^sub>n child\<^sub>n) (Hp m w\<^sub>m child\<^sub>m)) trees))\<close>
proof -
  show ?thesis
    unfolding vsids_link_def
    apply (refine_vcg if_refine)
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of m] by auto
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of n] by auto
    subgoal
      using encoded_pairheap.comb[OF vsids[unfolded add_mset_commute[of \<open>Hp n _ _\<close>]]]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap.comb[OF vsids]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    done
qed

definition vsids_insert where
  \<open>vsids_insert m n arr = do {
    ASSERT (n < length arr);
    vsids_link (arr[n:= (fst (arr!n), [])]) m n
  }\<close>

lemma vsids_insert:
  assumes \<open>encoded_pairheap arr {#Hp m w\<^sub>m children#}\<close> \<open>n \<notin># mset_nodes (Hp m w\<^sub>m children)\<close> \<open>n < length arr\<close>
  shows \<open>vsids_insert m n arr \<le> SPEC (\<lambda>arr'. encoded_pairheap arr' {#the (VSIDS.insert n (fst (arr!n)) (Some (Hp m w\<^sub>m children)))#}) \<close>
proof -
  have 1: \<open>encoded_pairheap (arr[n:= (fst (arr!n), [])]) {#Hp n (fst (arr!n)) [], Hp m w\<^sub>m children#}\<close>
    using assms encoded_pairheap.leaf[OF assms(1), of n \<open>(fst (arr!n))\<close>]
    by (auto intro!: )
  show ?thesis
    unfolding vsids_insert_def
    apply (refine_vcg vsids_link[OF 1, THEN order_trans])
    subgoal using assms by auto
    subgoal by auto
    done
qed


hide_const (open) NEMonad.ASSERT NEMonad.RETURN


term Node
interpretation VSIDS: pairing_heap where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done
term lseg
term pure_list_assn
find_theorems lseg 
  term os_list_assn
  thm os_list_assn_def
  term "mk_assn"
term \<open>\<upharpoonleft>arl_assn\<close>
lemma [termination_simp]: \<open>size_list size (hps a) < size a\<close>
  by (cases a) auto

term al_assn
fun lseg :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 'b) hp \<Rightarrow> _ \<Rightarrow> ll_assn\<close> and
  lseg_l :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 'b) hp list \<Rightarrow> _ \<Rightarrow> ll_assn\<close>
  where
  "lseg containt_assn score_assn a p = (EXS xn' p'. prod_assn containt_assn score_assn (node a, score a) xn' \<and>* lseg_l containt_assn score_assn (hps a) p')" |
  \<open>lseg_l containt_assn score_assn [] p = \<up>True\<close> |
  \<open>lseg_l containt_assn score_assn (a # as) p = (if p=null then sep_false else (EXS r. lseg containt_assn score_assn a p \<and>* lseg_l containt_assn score_assn as r))\<close>

term "\<upharpoonleft>(mk_assn (λl p. lseg atom_assn word64_assn l p))"
term node.next



partial_function (M) vsids_delete :: "'a::llvm_rep ptr \<Rightarrow> unit llM" where
  "vsids_delete p = doM { 
    if p=null then Mreturn () 
    else doM {
      n \<leftarrow> ll_load p;
      ll_free p;
      vsids_delete (hd(hps n))    }
  }"

lemma os_delete_rule[vcg_rules]: 
  "llvm_htriple (\<upharpoonleft>os_list_assn xs p) (os_delete p) (\<lambda>_. \<box>)"  
proof (induction xs arbitrary: p)
  case Nil
  note [simp] = os_list_assn_simps
  show ?case 
    apply (subst os_delete.simps)
    by vcg
next
  case (Cons a xs)
  
  note [vcg_rules] = Cons.IH
  note [simp] = os_list_assn_simps
  
  interpret llvm_prim_ctrl_setup .
  
  show ?case 
    apply (subst os_delete.simps)
    apply vcg
    done
    
  
qed


fun mset_nodes :: "('b, 'a) hp \<Rightarrow>'b multiset" where
"mset_nodes (Hp x _ hs) = {#x#} + sum_mset(mset(map mset_nodes hs))"

(*TODO: do we need to ensure that there are no cycle already here?*)
inductive encoded_pairheap where
  empty: \<open>encoded_pairheap [] {#}\<close> |
  leaf: \<open>encoded_pairheap (arr[n := (x, [])]) (add_mset (Hp n x []) trees)\<close>
  if  \<open>encoded_pairheap arr trees\<close> \<open>n \<notin># \<Sum>\<^sub># (mset_nodes `# trees)\<close>|
  comb: \<open>encoded_pairheap (arr[n := (x, snd (arr!n)@[m])]) (add_mset (Hp n w\<^sub>n (Hp m w\<^sub>m child\<^sub>m # child\<^sub>n)) trees)\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n (child\<^sub>n)) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close> and
    \<open>n < length arr\<close>

lemma encoded_pairheap_distinct_nodes: \<open>encoded_pairheap arr trees \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# trees))\<close>
  by (induction rule: encoded_pairheap.induct)
   (auto simp: ac_simps)

lemma \<open>encoded_pairheap arr trees \<Longrightarrow> n \<notin># \<Sum>\<^sub># (mset_nodes `# trees) \<Longrightarrow> encoded_pairheap (arr [n := a]) trees\<close>
  apply (induction rule: encoded_pairheap.induct)
  apply (auto intro: encoded_pairheap.intros)

(*
From here we need:
  - how to distinguish empty from no children? \<rightarrow> probably easy: by default only a single tree.
  - the node names are not already present
  - congruence on array
*)
lemma drop_tree:
  assumes \<open>encoded_pairheap arr (add_mset (Hp m w child) trees)\<close>
  shows \<open>encoded_pairheap arr (trees)\<close>
  using assms apply (induction arr "add_mset (Hp m w child) trees" rule: encoded_pairheap.induct)
  apply (auto simp: add_mset_eq_add_mset dest!: multi_member_split
    intro: encoded_pairheap.intros)

term VSIDS.link

type_synonym vsids = \<open>(nat \<Rightarrow> nat option) \<times> nat list\<close>

definition vsids :: \<open>nat multiset \<Rightarrow> (nat, 'a) ann_lits \<Rightarrow> vsids \<Rightarrow> bool\<close> where
  \<open>vsids \<A> M \<equiv> (\<lambda>(x, scores). (\<forall>L\<in>#\<A>. undefined_lit M (Pos L) \<longrightarrow> x L \<noteq> None) \<and> (\<forall>L\<in>#\<A>. L < length scores))\<close>

lemma vsids_push_lit:
  \<open>vsids \<A> M x \<Longrightarrow> vsids \<A> (L # M) x\<close>
  by (auto simp: vsids_def)


definition vsids_push_back_if_needed where
  \<open>vsids_push_back_if_needed L = (\<lambda>(heap, scores). do {
      ASSERT (L < length scores);
     ASSERT (pre_map_contains_key (L, heap));
     if (L \<in> dom heap) then RETURN (heap, scores)
     else RETURN (heap(L\<mapsto>scores!L), scores)
  })\<close>
term VSIDS.hm2_assn
definition vsids_assn where
  \<open>vsids_assn N = VSIDS.hm_assn N \<times>\<^sub>a array_assn (unat_assn' TYPE(32))\<close>

lemma op_map_contains_key[pat_rules]: 
  "op_set_member $ k $ (dom$m) \<equiv> op_map_contains_key$'k$'m"
  by (auto intro!: eq_reflection)

sepref_register op_map_contains_key

find_theorems op_map_contains_key
sepref_def vsids_push_back_if_needed_impl
  is \<open>uncurry vsids_push_back_if_needed\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a (vsids_assn N)\<^sup>k \<rightarrow>\<^sub>a vsids_assn N\<close>
  unfolding vsids_assn_def vsids_push_back_if_needed_def
    op_map_contains_key is_None_def
  supply [sepref_fr_rules] = snatb_hnr
  apply annot_all_atm_idxs
  apply (rewrite at \<open>\<hole> \<in> _\<close> value_of_atm_def[symmetric])
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  unfolding op_map_contains_key
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints

  apply apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
term op_map_contains_key

thm VSIDS.hm12_assn_def
  term VSIDS.hm_assn
term op_map_empty
    term VSIDS.hm_assn
  term mop_map_update
  term VSIDS.hm_pop_min_op
thm VSIDS.hm_pm_peek_min_def
  term mop_pm_peek_min
end