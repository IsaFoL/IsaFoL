theory IsaSAT_VMTF
imports Watched_Literals.WB_Sort IsaSAT_Setup Weidenbach_Book_Base.Explorer
begin


chapter \<open>Decision heuristic\<close>

section \<open>Code generation for the VMTF decision heuristic and the trail\<close>
type_synonym (in -) isa_vmtf_remove_int = \<open>vmtf \<times> (nat list \<times> bool list)\<close>

definition update_next_search where
  \<open>update_next_search L = (\<lambda>((ns, m, fst_As, lst_As, next_search), to_remove).
    ((ns, m, fst_As, lst_As, L), to_remove))\<close>

definition vmtf_enqueue_pre where
  \<open>vmtf_enqueue_pre =
     (\<lambda>((M, L),(ns,m,fst_As,lst_As, next_search)). L < length ns \<and>
       (fst_As \<noteq> None \<longrightarrow> the fst_As < length ns) \<and>
       (fst_As \<noteq> None \<longrightarrow> lst_As \<noteq> None) \<and>
       m+1 \<le> uint64_max)\<close>

definition isa_vmtf_enqueue :: \<open>trail_pol \<Rightarrow> nat \<Rightarrow> vmtf_option_fst_As \<Rightarrow> vmtf nres\<close> where
\<open>isa_vmtf_enqueue = (\<lambda>M L (ns, m, fst_As, lst_As, next_search). do {
  ASSERT(defined_atm_pol_pre M L);
  de \<leftarrow> RETURN (defined_atm_pol M L);
  case fst_As of
    None \<Rightarrow>RETURN ((ns[L := VMTF_Node m fst_As None], m+1, L, L,
            (if de then None else Some L)))
  | Some fst_As \<Rightarrow> do {
      let fst_As' = VMTF_Node (stamp (ns!fst_As)) (Some L) (get_next (ns!fst_As));
      RETURN (ns[L := VMTF_Node (m+1) None (Some fst_As), fst_As := fst_As'],
          m+1, L, the lst_As, (if de then next_search else Some L))
   }})\<close>

lemma vmtf_enqueue_alt_def:
  \<open>RETURN ooo vmtf_enqueue = (\<lambda>M L (ns, m, fst_As, lst_As, next_search). do {
    let de = defined_lit M (Pos L);
    case fst_As of
      None \<Rightarrow> RETURN (ns[L := VMTF_Node m fst_As None], m+1, L, L,
	   (if de then None else Some L))
    | Some fst_As \<Rightarrow>
       let fst_As' = VMTF_Node (stamp (ns!fst_As)) (Some L) (get_next (ns!fst_As)) in
       RETURN (ns[L := VMTF_Node (m+1) None (Some fst_As), fst_As := fst_As'],
	    m+1, L, the lst_As, (if de then next_search else Some L))})\<close>
  unfolding vmtf_enqueue_def Let_def
  by (auto intro!: ext split: option.splits)

lemma isa_vmtf_enqueue:
  \<open>(uncurry2 isa_vmtf_enqueue, uncurry2 (RETURN ooo vmtf_enqueue)) \<in>
     [\<lambda>((M, L), _). L \<in># \<A>]\<^sub>f (trail_pol \<A>) \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have defined_atm_pol: \<open>(defined_atm_pol x1g x2f, defined_lit x1a (Pos x2)) \<in> Id\<close>
    if
      \<open>case y of (x, xa) \<Rightarrow> (case x of (M, L) \<Rightarrow> \<lambda>_. L \<in># \<A>) xa\<close> and
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f Id\<close> and    \<open>x1 = (x1a, x2)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1f = (x1g, x2f)\<close> and
      \<open>x2j = (x1k, x2k)\<close> and
      \<open>x2i = (x1j, x2j)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x2g = (x1h, x2h)\<close> and
      \<open>x = (x1f, x2g)\<close>
     for x y x1 x1a x2 x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x1g x2f x2g x1h x2h
       x1i x2i x1j x2j x1k x2k
  proof -
    have [simp]: \<open>defined_lit x1a (Pos x2) \<longleftrightarrow> defined_atm x1a x2\<close>
      using that by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n trail_pol_def defined_atm_def)

    show ?thesis
      using undefined_atm_code[THEN fref_to_Down, unfolded uncurry_def, of \<A> \<open>(x1a, x2)\<close> \<open>(x1g, x2f)\<close>]
      that by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n RETURN_def)
  qed

  show ?thesis
    unfolding isa_vmtf_enqueue_def vmtf_enqueue_alt_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg)
    subgoal by (rule defined_atm_pol_pre) auto
    apply (rule defined_atm_pol; assumption)
    apply (rule same_in_Id_option_rel)
    subgoal for x y x1 x1a x2 x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x1g x2f x2g x1h x2h
	 x1i x2i x1j x2j x1k x2k
      by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition partition_vmtf_nth :: \<open>nat_vmtf_node list  \<Rightarrow>  nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat) nres\<close> where
  \<open>partition_vmtf_nth ns = partition_main (\<le>) (\<lambda>n. stamp (ns ! n))\<close>

definition partition_between_ref_vmtf :: \<open>nat_vmtf_node list \<Rightarrow>  nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat) nres\<close> where
  \<open>partition_between_ref_vmtf ns = partition_between_ref (\<le>) (\<lambda>n. stamp (ns ! n))\<close>

definition quicksort_vmtf_nth :: \<open>nat_vmtf_node list \<times> 'c \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>quicksort_vmtf_nth = (\<lambda>(ns, _). full_quicksort_ref (\<le>) (\<lambda>n. stamp (ns ! n)))\<close>

definition quicksort_vmtf_nth_ref:: \<open>nat_vmtf_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>quicksort_vmtf_nth_ref ns a b c =
     quicksort_ref (\<le>) (\<lambda>n. stamp (ns ! n)) (a, b, c)\<close>

lemma (in -) partition_vmtf_nth_code_helper:
  assumes \<open>\<forall>x\<in>set ba. x < length a\<close>  and
      \<open>b < length ba\<close> and
     mset: \<open>mset ba = mset a2'\<close>  and
      \<open>a1' < length a2'\<close>
  shows \<open>a2' ! b < length a\<close>
  using nth_mem[of b a2'] mset_eq_setD[OF mset] mset_eq_length[OF mset] assms
  by (auto simp del: nth_mem)



lemma partition_vmtf_nth_code_helper3:
  \<open>\<forall>x\<in>set b. x < length a \<Longrightarrow>
       x'e < length a2' \<Longrightarrow>
       mset a2' = mset b \<Longrightarrow>
       a2' ! x'e < length a\<close>
  using mset_eq_setD nth_mem by blast

definition (in -) isa_vmtf_en_dequeue :: \<open>trail_pol \<Rightarrow> nat \<Rightarrow> vmtf \<Rightarrow> vmtf nres\<close> where
\<open>isa_vmtf_en_dequeue = (\<lambda>M L vm. isa_vmtf_enqueue M L (vmtf_dequeue L vm))\<close>

lemma isa_vmtf_en_dequeue:
  \<open>(uncurry2 isa_vmtf_en_dequeue, uncurry2 (RETURN ooo vmtf_en_dequeue)) \<in>
     [\<lambda>((M, L), _). L \<in># \<A>]\<^sub>f (trail_pol \<A>) \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding isa_vmtf_en_dequeue_def vmtf_en_dequeue_def uncurry_def
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for a aa ab ac ad b ba ae af ag ah bb ai bc aj ak al am bd
    by (rule order.trans,
      rule isa_vmtf_enqueue[of \<A>, THEN fref_to_Down_curry2,
        of ai bc \<open>vmtf_dequeue bc (aj, ak, al, am, bd)\<close>])
      auto
  done

definition isa_vmtf_en_dequeue_pre :: \<open>(trail_pol \<times> nat) \<times> vmtf \<Rightarrow> bool\<close> where
  \<open>isa_vmtf_en_dequeue_pre = (\<lambda>((M, L),(ns,m,fst_As, lst_As, next_search)).
       L < length ns \<and> vmtf_dequeue_pre (L, ns) \<and>
       fst_As < length ns \<and> (get_next (ns ! fst_As) \<noteq> None \<longrightarrow> get_prev (ns ! lst_As) \<noteq> None) \<and>
       (get_next (ns ! fst_As) = None \<longrightarrow> fst_As = lst_As) \<and>
       m+1 \<le> uint64_max)\<close>

lemma isa_vmtf_en_dequeue_preD:
  assumes \<open>isa_vmtf_en_dequeue_pre ((M, ah), a, aa, ab, ac, b)\<close>
  shows \<open>ah < length a\<close> and \<open>vmtf_dequeue_pre (ah, a)\<close>
  using assms by (auto simp: isa_vmtf_en_dequeue_pre_def)


lemma isa_vmtf_en_dequeue_pre_vmtf_enqueue_pre:
   \<open>isa_vmtf_en_dequeue_pre ((M, L), a, st, fst_As, lst_As, next_search) \<Longrightarrow>
       vmtf_enqueue_pre ((M, L), vmtf_dequeue L (a, st, fst_As, lst_As, next_search))\<close>
  unfolding vmtf_enqueue_pre_def
  apply clarify
  apply (intro conjI)
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        ns_vmtf_dequeue_def Let_def isa_vmtf_en_dequeue_pre_def split: option.splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
          isa_vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        Let_def isa_vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        Let_def isa_vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  done

lemma insert_sort_reorder_list:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>(full_quicksort_ref R h, reorder_list vm) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
proof -
  show ?thesis
    apply (intro frefI nres_relI)
    apply (rule full_quicksort_ref_full_quicksort[THEN fref_to_Down, THEN order_trans])
    using assms apply fast
    using assms apply fast
    apply fast
     apply assumption
    using assms
    apply (auto 5 5 simp: reorder_list_def intro!: full_quicksort_correct[THEN order_trans])
    done
qed

lemma quicksort_vmtf_nth_reorder:
   \<open>(uncurry quicksort_vmtf_nth, uncurry reorder_list) \<in>
      Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using insert_sort_reorder_list[unfolded fref_def nres_rel_def, of
     \<open>(\<le>)\<close> \<open>(\<lambda>n. stamp (fst (fst y) ! n) :: nat)\<close> \<open>fst y\<close>]
    by (cases x, cases y)
      (fastforce simp: quicksort_vmtf_nth_def uncurry_def fref_def)
  done

lemma atoms_hash_del_op_set_delete:
  \<open>(uncurry (RETURN oo atoms_hash_del),
    uncurry (RETURN oo Set.remove)) \<in>
     nat_rel \<times>\<^sub>r atoms_hash_rel \<A> \<rightarrow>\<^sub>f \<langle>atoms_hash_rel \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (force simp: atoms_hash_del_def atoms_hash_rel_def)


definition current_stamp where
  \<open>current_stamp vm  = fst (snd vm)\<close>

lemma current_stamp_alt_def:
  \<open>current_stamp = (\<lambda>(_, m, _). m)\<close>
  by (auto simp: current_stamp_def intro!: ext)

lemma vmtf_rescale_alt_def:
\<open>vmtf_rescale = (\<lambda>(ns, m, fst_As, lst_As :: nat, next_search). do {
    (ns, m, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
      (\<lambda>(ns, n, lst_As). lst_As \<noteq>None)
      (\<lambda>(ns, n, a). do {
         ASSERT(a \<noteq> None);
         ASSERT(n+1 \<le> uint32_max);
         ASSERT(the a < length ns);
         let m = the a;
         let c = ns ! m;
         let nc = get_next c;
         let pc = get_prev c;
         RETURN (ns[m := VMTF_Node n pc nc], n + 1, pc)
      })
      (ns, 0, Some lst_As);
    RETURN ((ns, m, fst_As, lst_As, next_search))
  })\<close>
  unfolding update_stamp.simps Let_def vmtf_rescale_def by auto

definition vmtf_reorder_list_raw where
  \<open>vmtf_reorder_list_raw = (\<lambda>vm to_remove. do {
    ASSERT(\<forall>x\<in>set to_remove. x < length vm);
    reorder_list vm to_remove
  })\<close>


definition vmtf_reorder_list :: \<open>vmtf \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>vmtf_reorder_list = (\<lambda>(vm, _) to_remove. do {
    vmtf_reorder_list_raw vm to_remove
  })\<close>

definition isa_vmtf_flush_int :: \<open>trail_pol \<Rightarrow> vmtf \<Rightarrow> _ \<Rightarrow> (vmtf \<times> _) nres\<close> where
\<open>isa_vmtf_flush_int  = (\<lambda>M vm (to_remove, h). do {
    ASSERT(\<forall>x\<in>set to_remove. x < length (fst vm));
    ASSERT(length to_remove \<le> uint32_max);
    to_remove' \<leftarrow> vmtf_reorder_list vm to_remove;
    ASSERT(length to_remove' \<le> uint32_max);
    vm \<leftarrow> (if length to_remove' \<ge> uint64_max - fst (snd vm)
      then vmtf_rescale vm else RETURN vm);
    ASSERT(length to_remove' + fst (snd vm) \<le> uint64_max);
    (_, vm, h) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h). i \<le> length to_remove' \<and> fst (snd vm') = i + fst (snd vm) \<and>
          (i < length to_remove' \<longrightarrow> isa_vmtf_en_dequeue_pre ((M, to_remove'!i), vm'))\<^esup>
      (\<lambda>(i, vm, h). i < length to_remove')
      (\<lambda>(i, vm, h). do {
         ASSERT(i < length to_remove');
	 ASSERT(isa_vmtf_en_dequeue_pre ((M, to_remove'!i), vm));
         vm \<leftarrow> isa_vmtf_en_dequeue M (to_remove'!i) vm;
	 ASSERT(atoms_hash_del_pre (to_remove'!i) h);
         RETURN (i+1, vm, atoms_hash_del (to_remove'!i) h)})
      (0, vm, h);
    RETURN (vm, (emptied_list to_remove', h))
  })\<close>


lemma isa_vmtf_flush_int:
  \<open>(uncurry2 isa_vmtf_flush_int, uncurry2 (vmtf_flush_int \<A>)) \<in> trail_pol (\<A>::nat multiset) \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<times>\<^sub>f Id\<rangle>nres_rel\<close>
proof -
  have vmtf_flush_int_alt_def:
    \<open>vmtf_flush_int \<A>\<^sub>i\<^sub>n = (\<lambda>M vm (to_remove, h). do {
      ASSERT(\<forall>x\<in>set to_remove. x < length (fst vm));
      ASSERT(length to_remove \<le> uint32_max);
      to_remove' \<leftarrow> reorder_list vm to_remove;
      ASSERT(length to_remove' \<le> uint32_max);
      vm \<leftarrow> (if length to_remove' + fst (snd vm) \<ge> uint64_max
	then vmtf_rescale vm else RETURN vm);
      ASSERT(length to_remove' + fst (snd vm) \<le> uint64_max);
      (_, vm, h) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h). i \<le> length to_remove' \<and> fst (snd vm') = i + fst (snd vm) \<and>
	    (i < length to_remove' \<longrightarrow> vmtf_en_dequeue_pre \<A>\<^sub>i\<^sub>n ((M, to_remove'!i), vm'))\<^esup>
	(\<lambda>(i, vm, h). i < length to_remove')
	(\<lambda>(i, vm, h). do {
	   ASSERT(i < length to_remove');
	   ASSERT(to_remove'!i \<in># \<A>\<^sub>i\<^sub>n);
	   ASSERT(atoms_hash_del_pre (to_remove'!i) h);
	   vm \<leftarrow> RETURN(vmtf_en_dequeue M (to_remove'!i) vm);
	   RETURN (i+1, vm, atoms_hash_del (to_remove'!i) h)})
	(0, vm, h);
      RETURN (vm, (emptied_list to_remove', h))
    })\<close> for \<A>\<^sub>i\<^sub>n
    unfolding vmtf_flush_int_def
    by auto

  have reorder_list: \<open>vmtf_reorder_list x2c x1e
    \<le> \<Down> Id
    (reorder_list x2 x1b)\<close>
    if
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1c = (x1d, x2c)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x = (x1c, x2d)\<close> and
      \<open>\<forall>x\<in>set x1b. x < length (fst x2)\<close> and
      \<open>length x1b \<le> uint32_max\<close> and
      \<open>\<forall>x\<in>set x1e. x < length (fst x2c)\<close> and
      \<open>length x1e \<le> uint32_max\<close>
    for x y x1 x1a x2 x2a x1b x2b x1c x1d x2c x2d x1e x2e
    using that unfolding vmtf_reorder_list_def by (cases x2)
      (auto intro!: ASSERT_leI simp: reorder_list_def vmtf_reorder_list_raw_def)

  have vmtf_rescale: \<open>vmtf_rescale x2c
      \<le> \<Down> Id
          (vmtf_rescale x2)\<close>
    if
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1c = (x1d, x2c)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x = (x1c, x2d)\<close> and
      \<open>\<forall>x\<in>set x1b. x < length (fst x2)\<close> and
      \<open>length x1b \<le> uint32_max\<close> and
      \<open>\<forall>x\<in>set x1e. x < length (fst x2c)\<close> and
      \<open>length x1e \<le> uint32_max\<close> and
      \<open>(to_remove', to_remove'a) \<in> Id\<close> and
      \<open>length to_remove'a \<le> uint32_max\<close> and
      \<open>length to_remove' \<le> uint32_max\<close> and
      \<open>uint64_max - fst (snd x2c) \<le> length to_remove'\<close> and
      \<open>uint64_max \<le> length to_remove'a + fst (snd x2)\<close>
    for x y x1 x1a x2 x2a x1b x2b x1c x1d x2c x2d x1e x2e
      to_remove' to_remove'a
    using that by auto
  have loop_rel: \<open>((0, vm, x2e), 0, vma, x2b)
      \<in> Id\<close>
    if 
      True and
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1c = (x1d, x2c)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x = (x1c, x2d)\<close> and
      \<open>\<forall>x\<in>set x1b. x < length (fst x2)\<close> and
      \<open>length x1b \<le> uint32_max\<close> and
      \<open>\<forall>x\<in>set x1e. x < length (fst x2c)\<close> and
      \<open>length x1e \<le> uint32_max\<close> and
      \<open>(to_remove', to_remove'a) \<in> Id\<close> and
      \<open>length to_remove'a \<le> uint32_max\<close> and
      \<open>length to_remove' \<le> uint32_max\<close> and
      \<open>(vm, vma) \<in> Id\<close> and
      \<open>length to_remove'a + fst (snd vma) \<le> uint64_max\<close> and
      \<open>length to_remove' + fst (snd vm) \<le> uint64_max\<close> and
      \<open>case (0, vma, x2b) of
     (i, vm', h) \<Rightarrow>
       i \<le> length to_remove'a \<and>
       fst (snd vm') = i + fst (snd vma) \<and>
       (i < length to_remove'a \<longrightarrow>
        vmtf_en_dequeue_pre \<A> ((x1a, to_remove'a ! i), vm'))\<close>
    for x y x1 x1a x2 x2a x1b x2b x1c x1d x2c x2d x1e x2e
      to_remove' to_remove'a vm vma
    using that by auto

  have isa_vmtf_en_dequeue_pre:
    \<open>vmtf_en_dequeue_pre \<A> ((M, L), x) \<Longrightarrow> isa_vmtf_en_dequeue_pre ((M', L), x)\<close> for x M M' L
    unfolding vmtf_en_dequeue_pre_def isa_vmtf_en_dequeue_pre_def
    by auto

  have isa_vmtf_en_dequeue:
    \<open>isa_vmtf_en_dequeue x1d (to_remove' ! x1h) x1i
      \<le> Refine_Basic.SPEC
          (\<lambda>c. (c, vmtf_en_dequeue x1a (to_remove'a ! x1f) x1g)
               \<in> Id)\<close>
    if
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1c = (x1d, x2c)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x = (x1c, x2d)\<close> and
      \<open>\<forall>x\<in>set x1b. x < length (fst x2)\<close> and
      \<open>length x1b \<le> uint32_max\<close> and
      \<open>\<forall>x\<in>set x1e. x < length (fst x2c)\<close> and
      \<open>length x1e \<le> uint32_max\<close> and
      \<open>(to_remove', to_remove'a) \<in> Id\<close> and
      \<open>length to_remove'a \<le> uint32_max\<close> and
      \<open>length to_remove' \<le> uint32_max\<close> and
      \<open>(vm, vma) \<in> Id\<close> and
      \<open>length to_remove'a + fst (snd vma) \<le> uint64_max\<close> and
      \<open>length to_remove' + fst (snd vm) \<le> uint64_max\<close> and
      \<open>(xa, x') \<in> Id\<close> and
      \<open>case xa of (i, vm, h) \<Rightarrow> i < length to_remove'\<close> and
      \<open>case x' of (i, vm, h) \<Rightarrow> i < length to_remove'a\<close> and
      \<open>case xa of
     (i, vm', h) \<Rightarrow>
       i \<le> length to_remove' \<and>
       fst (snd vm') = i + fst (snd vm) \<and>
       (i < length to_remove' \<longrightarrow>
        isa_vmtf_en_dequeue_pre ((x1d, to_remove' ! i), vm'))\<close> and
      \<open>case x' of
     (i, vm', h) \<Rightarrow>
       i \<le> length to_remove'a \<and>
       fst (snd vm') = i + fst (snd vma) \<and>
       (i < length to_remove'a \<longrightarrow>
        vmtf_en_dequeue_pre \<A> ((x1a, to_remove'a ! i), vm'))\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>x' = (x1f, x2f)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>xa = (x1h, x2h)\<close> and
      \<open>x1f < length to_remove'a\<close> and
      \<open>to_remove'a ! x1f \<in># \<A>\<close> and
      \<open>atoms_hash_del_pre (to_remove'a ! x1f) x2g\<close> and
      \<open>x1h < length to_remove'\<close> and
      \<open>isa_vmtf_en_dequeue_pre ((x1d, to_remove' ! x1h), x1i)\<close>
    for x y x1 x1a x2 x2a x1b x2b x1c x1d x2c x2d x1e
      x2e to_remove' to_remove'a vm vma xa x' x1f x2f x1g
      x2g x1h x2h x1i x2i
    using isa_vmtf_en_dequeue[of \<A>, THEN fref_to_Down_curry2, of x1a \<open>to_remove'a ! x1f\<close> x1g
        x1d \<open>to_remove' ! x1h\<close> x1i] that
    by (auto simp: RETURN_def)

  show ?thesis
   unfolding isa_vmtf_flush_int_def uncurry_def vmtf_flush_int_alt_def
    apply (intro frefI nres_relI)
    apply (refine_rcg)
    subgoal
      by auto
    subgoal
      by auto
      apply (rule reorder_list; assumption)
    subgoal
      by auto
    subgoal
      by auto
    apply (rule vmtf_rescale; assumption)
    subgoal
      by auto
    subgoal
      by auto
    apply (rule loop_rel; assumption)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto intro!: isa_vmtf_en_dequeue_pre)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    apply (rule isa_vmtf_en_dequeue; assumption)
    subgoal for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e to_remove' to_remove'a vm
       vma xa x' x1f x2f x1g x2g x1h x2h x1i x2i vmb vmc
      by auto
    subgoal
      by auto
    subgoal
      by auto
    done
qed


definition atms_hash_insert_pre :: \<open>nat \<Rightarrow> nat list \<times> bool list \<Rightarrow> bool\<close> where
\<open>atms_hash_insert_pre i = (\<lambda>(n, xs). i < length xs \<and> (\<not>xs!i \<longrightarrow> length n < 2 + uint32_max div 2))\<close>

definition atoms_hash_insert :: \<open>nat \<Rightarrow> nat list \<times> bool list \<Rightarrow> (nat list \<times> bool list)\<close> where
\<open>atoms_hash_insert i  = (\<lambda>(n, xs). if xs ! i then (n, xs) else (n @ [i], xs[i := True]))\<close>

lemma bounded_included_le:
   assumes bounded: \<open>isasat_input_bounded \<A>\<close> and \<open>distinct n\<close> and
   \<open>set n \<subseteq> set_mset \<A> \<close>
  shows \<open>length n < uint32_max\<close>  \<open>length n \<le> 1 + uint32_max div 2\<close>
proof -
  have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (Pos `# mset n)\<close> and
    dist: \<open>distinct n\<close>
    using assms
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def distinct_atoms_rel_alt_def inj_on_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
   have dist: \<open>distinct_mset (Pos `# mset n)\<close>
    by (subst distinct_image_mset_inj)
      (use dist in \<open>auto simp: inj_on_def\<close>)
  have tauto: \<open>\<not> tautology (poss (mset n))\<close>
    by (auto simp: tautology_decomp)

  show \<open>length n < uint32_max\<close>  \<open>length n \<le> 1 + uint32_max div 2\<close>
    using simple_clss_size_upper_div2[OF bounded lits dist tauto]
    by (auto simp: uint32_max_def)
qed


lemma atms_hash_insert_pre:
  assumes \<open>L \<in># \<A>\<close> and \<open>(x, x') \<in> distinct_atoms_rel \<A>\<close> and \<open>isasat_input_bounded \<A>\<close>
  shows \<open>atms_hash_insert_pre L x\<close>
  using assms bounded_included_le[OF assms(3), of \<open>L # fst x\<close>]
  by (auto simp:  atoms_hash_insert_def atoms_hash_rel_def distinct_atoms_rel_alt_def
     atms_hash_insert_pre_def)


lemma atoms_hash_del_op_set_insert:
  \<open>(uncurry (RETURN oo atoms_hash_insert),
    uncurry (RETURN oo insert)) \<in>
     [\<lambda>(i, xs). i \<in># \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>]\<^sub>f
     nat_rel \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n \<rightarrow> \<langle>distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: atoms_hash_insert_def atoms_hash_rel_def distinct_atoms_rel_alt_def intro!: ASSERT_leI)


definition (in -) atoms_hash_set_member where
\<open>atoms_hash_set_member i xs =  do {ASSERT(i < length xs); RETURN (xs ! i)}\<close>


definition isa_vmtf_mark_to_rescore
  :: \<open>nat \<Rightarrow> vmtf \<Rightarrow> _ \<Rightarrow> isa_vmtf_remove_int\<close>
where
  \<open>isa_vmtf_mark_to_rescore L = (\<lambda>(ns, m, fst_As, next_search) to_remove.
     ((ns, m, fst_As, next_search), atoms_hash_insert L to_remove))\<close>

definition isa_vmtf_mark_to_rescore_pre where
  \<open>isa_vmtf_mark_to_rescore_pre = (\<lambda>L ((ns, m, fst_As, next_search), to_remove).
     atms_hash_insert_pre L to_remove)\<close>

(*
lemma isa_vmtf_mark_to_rescore_vmtf_mark_to_rescore:
  \<open>(uncurry2 (RETURN oo isa_vmtf_mark_to_rescore), uncurry (RETURN oo vmtf_mark_to_rescore)) \<in>
      [\<lambda>(L, vm). L\<in># \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f Id \<times>\<^sub>f (Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n) \<rightarrow>
      \<langle>Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  unfolding isa_vmtf_mark_to_rescore_def vmtf_mark_to_rescore_def
  by (intro frefI nres_relI)
    (auto intro!: atoms_hash_del_op_set_insert[THEN fref_to_Down_unRET_uncurry])
*)

definition isa_vmtf where
  \<open>isa_vmtf \<A> M =
     ((Id \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>option_rel))\<inverse>
       `` vmtf \<A> M\<close>

lemma vmtf_unset_pre:
  assumes
    \<open>((ns, m, fst_As, lst_As, next_search)) \<in> isa_vmtf \<A> M\<close> and
    \<open>L \<in># \<A>\<close>
  shows \<open>vmtf_unset_pre L ((ns, m, fst_As, lst_As, next_search))\<close>
  using assms vmtf_unset_pre_vmtf[of ns m fst_As lst_As next_search \<A> M L]
  unfolding isa_vmtf_def vmtf_unset_pre_def
  by auto
(*
lemma vmtf_unset_pre':
  assumes
    \<open>vm \<in> vmtf \<A> M\<close> and
    \<open>L \<in># \<A>\<close>
  shows \<open>vmtf_unset_pre L vm\<close>
  using assms by (cases vm) (auto dest: vmtf_unset_pre)
*)
(*
definition isa_vmtf_mark_to_rescore_and_unset :: \<open>nat \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> isa_vmtf_remove_int\<close>
where
  \<open>isa_vmtf_mark_to_rescore_and_unset L M = isa_vmtf_mark_to_rescore L (isa_vmtf_unset L M)\<close>

definition isa_vmtf_mark_to_rescore_and_unset_pre where
  \<open>isa_vmtf_mark_to_rescore_and_unset_pre = (\<lambda>(L, ((ns, m, fst_As, lst_As, next_search), tor)).
      vmtf_unset_pre L ((ns, m, fst_As, lst_As, next_search), tor) \<and>
      atms_hash_insert_pre L tor)\<close>
*)

lemma size_conflict_int_size_conflict:
  \<open>(RETURN o size_conflict_int, RETURN o size_conflict) \<in> [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<A> \<rightarrow>
     \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_int_def size_conflict_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

definition rescore_clause
  :: \<open>nat multiset \<Rightarrow> nat clause_l \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> vmtf \<Rightarrow>
    vmtf nres\<close>
where
  \<open>rescore_clause \<A> C M vm = SPEC (\<lambda>(vm'). vm' \<in> vmtf \<A> M)\<close>


lemma isa_vmtf_unset_vmtf_unset:
  \<open>(uncurry (RETURN oo isa_vmtf_unset), uncurry (RETURN oo vmtf_unset)) \<in>
     nat_rel \<times>\<^sub>f (Id) \<rightarrow>\<^sub>f
     \<langle>(Id)\<rangle>nres_rel\<close>
  unfolding vmtf_unset_def isa_vmtf_unset_def uncurry_def
  by (intro frefI nres_relI) auto

lemma isa_vmtf_unset_isa_vmtf:
  assumes \<open>vm \<in> vmtf \<A> M\<close> and \<open>L \<in># \<A>\<close>
  shows \<open>isa_vmtf_unset L vm \<in> vmtf \<A> M\<close>
proof -
  obtain vm0 to_remove to_remove' where
    vm: \<open>vm = (vm0, to_remove)\<close> and
    vm0: \<open>(vm0, to_remove') \<in> vmtf \<A> M\<close>
    using assms by (cases vm) (auto simp: isa_vmtf_def)

  then show ?thesis
    using assms
      isa_vmtf_unset_vmtf_unset[THEN fref_to_Down_unRET_uncurry, of L vm L vm]
    using
      abs_vmtf_ns_unset_vmtf_unset[of \<open>fst vm\<close> \<open>fst (snd vm)\<close>  \<open>fst (snd (snd vm))\<close>
         \<open>fst (snd (snd (snd vm)))\<close> \<open>snd (snd (snd (snd vm)))\<close> \<A> M L]
    by (auto simp: vm atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n intro: elim!: prod_relE)
qed

lemma isa_vmtf_tl_isa_vmtf:
  assumes \<open>vm \<in> vmtf \<A> M\<close> and \<open>M \<noteq> []\<close> and \<open>lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<open>L = (atm_of (lit_of (hd M)))\<close>
  shows \<open>isa_vmtf_unset L vm \<in> vmtf \<A> (tl M)\<close>
proof -
  let ?L = \<open>atm_of (lit_of (hd M))\<close>
  obtain vm0 to_remove to_remove' where
    vm: \<open>vm = (vm0, to_remove)\<close> and
    vm0: \<open>(vm0, to_remove') \<in> vmtf \<A> M\<close>
    using assms by (cases vm) (auto simp: isa_vmtf_def)

  then show ?thesis
    using assms
      isa_vmtf_unset_vmtf_unset[THEN fref_to_Down_unRET_uncurry, of ?L vm ?L vm]
    using vmtf_unset_vmtf_tl[of \<open>fst vm\<close> \<open>fst (snd vm)\<close>  \<open>fst (snd (snd vm))\<close>
         \<open>fst (snd (snd (snd vm)))\<close> \<open>snd (snd (snd (snd vm)))\<close> \<A> M]
    by (cases M)
     (auto simp: vm atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n elim!: prod_relE)
qed

definition isa_vmtf_find_next_undef :: \<open>vmtf \<Rightarrow> trail_pol \<Rightarrow> (nat option) nres\<close> where
\<open>isa_vmtf_find_next_undef = (\<lambda>(ns, m, fst_As, lst_As, next_search) M. do {
    WHILE\<^sub>T\<^bsup>\<lambda>next_search. next_search \<noteq> None \<longrightarrow> defined_atm_pol_pre M (the next_search)\<^esup>
      (\<lambda>next_search. next_search \<noteq> None \<and> defined_atm_pol M (the next_search))
      (\<lambda>next_search. do {
         ASSERT(next_search \<noteq> None);
         let n = the next_search;
         ASSERT (n < length ns);
         RETURN (get_next (ns!n))
        }
      )
      next_search
  })\<close>


lemma isa_vmtf_find_next_undef_vmtf_find_next_undef:
  \<open>(uncurry isa_vmtf_find_next_undef, uncurry (vmtf_find_next_undef \<A>)) \<in>
      Id \<times>\<^sub>r trail_pol \<A>  \<rightarrow>\<^sub>f \<langle>\<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel \<close>
  unfolding isa_vmtf_find_next_undef_def vmtf_find_next_undef_def uncurry_def
    defined_atm_def[symmetric]
  apply (intro frefI nres_relI)
  apply refine_rcg
  subgoal by auto
  subgoal by (rule defined_atm_pol_pre) (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  subgoal
    by (auto simp: undefined_atm_code[THEN fref_to_Down_unRET_uncurry_Id])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done


end

