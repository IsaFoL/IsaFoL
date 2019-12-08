theory IsaSAT_VMTF
imports Watched_Literals.WB_Sort IsaSAT_Setup
begin


chapter \<open>Decision heuristic\<close>
subsection \<open>Code generation for the VMTF decision heuristic and the trail\<close>

(* TODO used? *)
definition size_conflict_wl :: \<open>nat twl_st_wl \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl S = size (the (get_conflict_wl S))\<close>

definition size_conflict :: \<open>nat clause option \<Rightarrow> nat\<close> where
  \<open>size_conflict D = size (the D)\<close>

definition size_conflict_int :: \<open>conflict_option_rel \<Rightarrow> nat\<close> where
  \<open>size_conflict_int = (\<lambda>(_, n, _). n)\<close>

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
  apply (intro WB_More_Refinement.frefI nres_relI)
  subgoal for x y
    using insert_sort_reorder_list[unfolded fref_def nres_rel_def, of
     \<open>(\<le>)\<close> \<open>(\<lambda>n. stamp (fst (fst y) ! n) :: nat)\<close> \<open>fst y\<close>]
    by (cases x, cases y)
      (fastforce simp: quicksort_vmtf_nth_def uncurry_def WB_More_Refinement.fref_def)
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


definition vmtf_reorder_list where
  \<open>vmtf_reorder_list = (\<lambda>(vm, _) to_remove. do {
    vmtf_reorder_list_raw vm to_remove
  })\<close>

definition isa_vmtf_flush_int :: \<open>trail_pol \<Rightarrow> _ \<Rightarrow> _ nres\<close> where
\<open>isa_vmtf_flush_int  = (\<lambda>M (vm, (to_remove, h)). do {
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
  \<open>(uncurry isa_vmtf_flush_int, uncurry (vmtf_flush_int \<A>)) \<in> trail_pol \<A> \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  have vmtf_flush_int_alt_def:
    \<open>vmtf_flush_int \<A>\<^sub>i\<^sub>n = (\<lambda>M (vm, (to_remove, h)). do {
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

  have reorder_list: \<open>vmtf_reorder_list x1d x1e
	\<le> \<Down> Id
	   (reorder_list x1a x1b)\<close>
    if
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id\<close> and    \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x = (x1c, x2c)\<close> and
      \<open>\<forall>x\<in>set x1b. x < length (fst x1a)\<close> and
      \<open>length x1b \<le> uint32_max\<close> and
      \<open>\<forall>x\<in>set x1e. x < length (fst x1d)\<close> and
      \<open>length x1e \<le> uint32_max\<close>
    for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
    using that unfolding vmtf_reorder_list_def by (cases x1a)
      (auto intro!: ASSERT_leI simp: reorder_list_def vmtf_reorder_list_raw_def)

  have vmtf_rescale: \<open>vmtf_rescale x1d
	\<le> \<Down> Id
	   (vmtf_rescale x1a)\<close>
    if
      \<open>True\<close> and
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id\<close> and    \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x = (x1c, x2c)\<close> and
      \<open>\<forall>x\<in>set x1b. x < length (fst x1a)\<close> and
      \<open>length x1b \<le> uint32_max\<close> and
      \<open>\<forall>x\<in>set x1e. x < length (fst x1d)\<close> and
      \<open>length x1e \<le> uint32_max\<close> and
      \<open>(to_remove', to_remove'a) \<in> Id\<close> and
      \<open>length to_remove'a \<le> uint32_max\<close> and
      \<open>length to_remove' \<le> uint32_max\<close> and
      \<open>uint64_max \<le> length to_remove'a + fst (snd x1a)\<close>
    for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e to_remove' to_remove'a
    using that by auto

  have loop_rel: \<open>((0, vm, x2e), 0, vma, x2b) \<in> Id\<close>
    if
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x = (x1c, x2c)\<close> and
      \<open>\<forall>x\<in>set x1b. x < length (fst x1a)\<close> and
      \<open>length x1b \<le> uint32_max\<close> and
      \<open>\<forall>x\<in>set x1e. x < length (fst x1d)\<close> and
      \<open>length x1e \<le> uint32_max\<close> and
      \<open>(to_remove', to_remove'a) \<in> Id\<close> and
      \<open>length to_remove'a \<le> uint32_max\<close> and
      \<open>length to_remove' \<le> uint32_max\<close> and
      \<open>(vm, vma) \<in> Id\<close> and
      \<open>length to_remove'a + fst (snd vma) \<le> uint64_max\<close>
      \<open>case (0, vma, x2b) of
       (i, vm', h) \<Rightarrow>
	 i \<le> length to_remove'a \<and>
	 fst (snd vm') = i + fst (snd vma) \<and>
	 (i < length to_remove'a \<longrightarrow>
	  vmtf_en_dequeue_pre \<A> ((x1, to_remove'a ! i), vm'))\<close>
    for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e to_remove' to_remove'a vm
       vma
    using that by auto
  have isa_vmtf_en_dequeue_pre:
    \<open>vmtf_en_dequeue_pre \<A> ((M, L), x) \<Longrightarrow> isa_vmtf_en_dequeue_pre ((M', L), x)\<close> for x M M' L
    unfolding vmtf_en_dequeue_pre_def isa_vmtf_en_dequeue_pre_def
    by auto
  have isa_vmtf_en_dequeue: \<open>isa_vmtf_en_dequeue x1c (to_remove' ! x1h) x1i
       \<le> SPEC
	  (\<lambda>c. (c, vmtf_en_dequeue x1 (to_remove'a ! x1f) x1g)
	       \<in> Id)\<close>
   if
     \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id\<close> and
     \<open>\<forall>x\<in>set x1b. x < length (fst x1a)\<close> and
     \<open>length x1b \<le> uint32_max\<close> and
     \<open>\<forall>x\<in>set x1e. x < length (fst x1d)\<close> and
     \<open>length x1e \<le> uint32_max\<close> and
     \<open>length to_remove'a \<le> uint32_max\<close> and
     \<open>length to_remove' \<le> uint32_max\<close> and
     \<open>length to_remove'a + fst (snd vma) \<le> uint64_max\<close> and
     \<open>case xa of (i, vm, h) \<Rightarrow> i < length to_remove'\<close> and
     \<open>case x' of (i, vm, h) \<Rightarrow> i < length to_remove'a\<close> and
     \<open>case xa of
      (i, vm', h) \<Rightarrow>
	i \<le> length to_remove' \<and>
	fst (snd vm') = i + fst (snd vm) \<and>
	(i < length to_remove' \<longrightarrow>
	 isa_vmtf_en_dequeue_pre ((x1c, to_remove' ! i), vm'))\<close> and
     \<open>case x' of
      (i, vm', h) \<Rightarrow>
	i \<le> length to_remove'a \<and>
	fst (snd vm') = i + fst (snd vma) \<and>
	(i < length to_remove'a \<longrightarrow>
	 vmtf_en_dequeue_pre \<A> ((x1, to_remove'a ! i), vm'))\<close> and
     \<open>isa_vmtf_en_dequeue_pre ((x1c, to_remove' ! x1h), x1i)\<close> and
     \<open>x1f < length to_remove'a\<close> and
     \<open>to_remove'a ! x1f \<in># \<A>\<close> and
     \<open>x1h < length to_remove'\<close> and
     \<open>x2a = (x1b, x2b)\<close> and
     \<open>x2 = (x1a, x2a)\<close> and
     \<open>y = (x1, x2)\<close> and
     \<open>x = (x1c, x2c)\<close>  and
     \<open>x2d = (x1e, x2e)\<close> and
     \<open>x2c = (x1d, x2d)\<close> and
     \<open>x2f = (x1g, x2g)\<close> and
     \<open>x' = (x1f, x2f)\<close> and
     \<open>x2h = (x1i, x2i)\<close> and
     \<open>xa = (x1h, x2h)\<close> and
     \<open>(to_remove', to_remove'a) \<in> Id\<close> and
     \<open>(xa, x') \<in> Id\<close> and
     \<open>(vm, vma) \<in> Id\<close>
   for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e to_remove' to_remove'a vm
       vma xa x' x1f x2f x1g x2g x1h x2h x1i and x2i :: \<open>bool list\<close>
  using isa_vmtf_en_dequeue[of \<A>, THEN fref_to_Down_curry2, of x1 \<open>to_remove'a ! x1f\<close> x1g
     x1c \<open>to_remove' ! x1h\<close> x1i] that
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
  :: \<open>nat \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> isa_vmtf_remove_int\<close>
where
  \<open>isa_vmtf_mark_to_rescore L = (\<lambda>((ns, m, fst_As, next_search), to_remove).
     ((ns, m, fst_As, next_search), atoms_hash_insert L to_remove))\<close>

definition isa_vmtf_mark_to_rescore_pre where
  \<open>isa_vmtf_mark_to_rescore_pre = (\<lambda>L ((ns, m, fst_As, next_search), to_remove).
     atms_hash_insert_pre L to_remove)\<close>

lemma isa_vmtf_mark_to_rescore_vmtf_mark_to_rescore:
  \<open>(uncurry (RETURN oo isa_vmtf_mark_to_rescore), uncurry (RETURN oo vmtf_mark_to_rescore)) \<in>
      [\<lambda>(L, vm). L\<in># \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f Id \<times>\<^sub>f (Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n) \<rightarrow>
      \<langle>Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  unfolding isa_vmtf_mark_to_rescore_def vmtf_mark_to_rescore_def
  by (intro frefI nres_relI)
    (auto intro!: atoms_hash_del_op_set_insert[THEN fref_to_Down_unRET_uncurry])

definition (in -) isa_vmtf_unset :: \<open>nat \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> isa_vmtf_remove_int\<close> where
\<open>isa_vmtf_unset = (\<lambda>L ((ns, m, fst_As, lst_As, next_search), to_remove).
  (if next_search = None \<or> stamp (ns ! (the next_search)) < stamp (ns ! L)
  then ((ns, m, fst_As, lst_As, Some L), to_remove)
  else ((ns, m, fst_As, lst_As, next_search), to_remove)))\<close>

definition vmtf_unset_pre where
\<open>vmtf_unset_pre = (\<lambda>L ((ns, m, fst_As, lst_As, next_search), to_remove).
  L < length ns \<and> (next_search \<noteq> None \<longrightarrow> the next_search < length ns))\<close>

lemma vmtf_unset_pre_vmtf:
  assumes
    \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
    \<open>L \<in># \<A>\<close>
  shows \<open>vmtf_unset_pre L ((ns, m, fst_As, lst_As, next_search), to_remove)\<close>
  using assms
  by (auto simp: vmtf_def vmtf_unset_pre_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

lemma vmtf_unset_pre:
  assumes
    \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> isa_vmtf \<A> M\<close> and
    \<open>L \<in># \<A>\<close>
  shows \<open>vmtf_unset_pre L ((ns, m, fst_As, lst_As, next_search), to_remove)\<close>
  using assms vmtf_unset_pre_vmtf[of ns m fst_As lst_As next_search _ \<A> M L]
  unfolding isa_vmtf_def vmtf_unset_pre_def
  by auto

lemma vmtf_unset_pre':
  assumes
    \<open>vm \<in> isa_vmtf \<A> M\<close> and
    \<open>L \<in># \<A>\<close>
  shows \<open>vmtf_unset_pre L vm\<close>
  using assms by (cases vm) (auto dest: vmtf_unset_pre)


definition isa_vmtf_mark_to_rescore_and_unset :: \<open>nat \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> isa_vmtf_remove_int\<close>
where
  \<open>isa_vmtf_mark_to_rescore_and_unset L M = isa_vmtf_mark_to_rescore L (isa_vmtf_unset L M)\<close>

definition isa_vmtf_mark_to_rescore_and_unset_pre where
  \<open>isa_vmtf_mark_to_rescore_and_unset_pre = (\<lambda>(L, ((ns, m, fst_As, lst_As, next_search), tor)).
      vmtf_unset_pre L ((ns, m, fst_As, lst_As, next_search), tor) \<and>
      atms_hash_insert_pre L tor)\<close>


lemma size_conflict_int_size_conflict:
  \<open>(RETURN o size_conflict_int, RETURN o size_conflict) \<in> [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<A> \<rightarrow>
     \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_int_def size_conflict_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

definition rescore_clause
  :: \<open>nat multiset \<Rightarrow> nat clause_l \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
    (vmtf_remove_int) nres\<close>
where
  \<open>rescore_clause \<A> C M vm = SPEC (\<lambda>(vm'). vm' \<in> vmtf \<A> M)\<close>

(* TODO ded-uplicate definitions *)
definition find_decomp_w_ns_pre where
  \<open>find_decomp_w_ns_pre \<A> = (\<lambda>((M, highest), vm).
       no_dup M \<and>
       highest < count_decided M \<and>
       isasat_input_bounded \<A> \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M \<and>
       vm \<in> vmtf \<A> M)\<close>

definition find_decomp_wl_imp
  :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> vmtf_remove_int \<Rightarrow>
       ((nat, nat) ann_lits \<times> vmtf_remove_int) nres\<close>
where
  \<open>find_decomp_wl_imp \<A> = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided M\<^sub>0;
    let M\<^sub>0 = trail_conv_to_no_CS M\<^sub>0;
    let n = length M\<^sub>0;
    pos \<leftarrow> get_pos_of_level_in_trail M\<^sub>0 lev;
    ASSERT((n - pos) \<le> uint32_max);
    ASSERT(n \<ge> pos);
    let target = n - pos;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j \<le> target \<and>
           M = drop j M\<^sub>0 \<and> target \<le> length M\<^sub>0 \<and>
           vm' \<in> vmtf \<A> M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j < target)
         (\<lambda>(j, M, vm). do {
            ASSERT(M \<noteq> []);
            ASSERT(Suc j \<le> uint32_max);
            let L = atm_of (lit_of_hd_trail M);
            ASSERT(L \<in># \<A>);
            RETURN (j + 1, tl M, vmtf_unset L vm)
         })
         (0, M\<^sub>0, vm);
    ASSERT(lev = count_decided M);
    let M = trail_conv_back lev M;
    RETURN (M, vm')
  })\<close>

definition isa_find_decomp_wl_imp
  :: \<open>trail_pol \<Rightarrow> nat \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> (trail_pol \<times> isa_vmtf_remove_int) nres\<close>
where
  \<open>isa_find_decomp_wl_imp = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided_pol M\<^sub>0;
    let M\<^sub>0 = trail_pol_conv_to_no_CS M\<^sub>0;
    ASSERT(isa_length_trail_pre M\<^sub>0);
    let n = isa_length_trail M\<^sub>0;
    pos \<leftarrow> get_pos_of_level_in_trail_imp M\<^sub>0 lev;
    ASSERT((n - pos) \<le> uint32_max);
    ASSERT(n \<ge> pos);
    let target = n - pos;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j \<le> target\<^esup>
         (\<lambda>(j, M, vm). j < target)
         (\<lambda>(j, M, vm). do {
            ASSERT(Suc j \<le> uint32_max);
            ASSERT(case M of (M, _) \<Rightarrow> M \<noteq> []);
            ASSERT(tl_trailt_tr_no_CS_pre M);
            let L = atm_of (lit_of_last_trail_pol M);
            ASSERT(vmtf_unset_pre L vm);
            RETURN (j + 1, tl_trailt_tr_no_CS M, isa_vmtf_unset L vm)
         })
         (0, M\<^sub>0, vm);
    M \<leftarrow> trail_conv_back_imp lev M;
    RETURN (M, vm')
  })\<close>


lemma isa_vmtf_unset_vmtf_unset:
  \<open>(uncurry (RETURN oo isa_vmtf_unset), uncurry (RETURN oo vmtf_unset)) \<in>
     nat_rel \<times>\<^sub>f (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<rightarrow>\<^sub>f
     \<langle>(Id \<times>\<^sub>r distinct_atoms_rel \<A>)\<rangle>nres_rel\<close>
  unfolding vmtf_unset_def isa_vmtf_unset_def uncurry_def
  by (intro frefI nres_relI) auto

lemma isa_vmtf_unset_isa_vmtf:
  assumes \<open>vm \<in> isa_vmtf \<A> M\<close> and \<open>L \<in># \<A>\<close>
  shows \<open>isa_vmtf_unset L vm \<in> isa_vmtf \<A> M\<close>
proof -
  obtain vm0 to_remove to_remove' where
    vm: \<open>vm = (vm0, to_remove)\<close> and
    vm0: \<open>(vm0, to_remove') \<in> vmtf \<A> M\<close> and
    \<open>(to_remove, to_remove') \<in> distinct_atoms_rel \<A>\<close>
    using assms by (cases vm) (auto simp: isa_vmtf_def)

  then show ?thesis
    using assms
      isa_vmtf_unset_vmtf_unset[of \<A>, THEN fref_to_Down_unRET_uncurry, of L vm L \<open>(vm0, to_remove')\<close>]
      abs_vmtf_ns_unset_vmtf_unset[of \<open>fst vm0\<close> \<open>fst (snd vm0)\<close>  \<open>fst (snd (snd vm0))\<close>
         \<open>fst (snd (snd (snd vm0)))\<close> \<open>snd (snd (snd (snd vm0)))\<close> to_remove' \<A> M L to_remove']
    by (auto simp: vm atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n intro: isa_vmtfI elim!: prod_relE)
qed

lemma isa_vmtf_tl_isa_vmtf:
  assumes \<open>vm \<in> isa_vmtf \<A> M\<close> and \<open>M \<noteq> []\<close> and \<open>lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<open>L = (atm_of (lit_of (hd M)))\<close>
  shows \<open>isa_vmtf_unset L vm \<in> isa_vmtf \<A> (tl M)\<close>
proof -
  let ?L = \<open>atm_of (lit_of (hd M))\<close>
  obtain vm0 to_remove to_remove' where
    vm: \<open>vm = (vm0, to_remove)\<close> and
    vm0: \<open>(vm0, to_remove') \<in> vmtf \<A> M\<close> and
    \<open>(to_remove, to_remove') \<in> distinct_atoms_rel \<A>\<close>
    using assms by (cases vm) (auto simp: isa_vmtf_def)

  then show ?thesis
    using assms
      isa_vmtf_unset_vmtf_unset[of \<A>, THEN fref_to_Down_unRET_uncurry, of ?L vm ?L \<open>(vm0, to_remove')\<close>]
      vmtf_unset_vmtf_tl[of \<open>fst vm0\<close> \<open>fst (snd vm0)\<close>  \<open>fst (snd (snd vm0))\<close>
         \<open>fst (snd (snd (snd vm0)))\<close> \<open>snd (snd (snd (snd vm0)))\<close> to_remove' \<A> M]
    by (cases M)
     (auto simp: vm atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n intro: isa_vmtfI elim!: prod_relE)
qed

lemma isa_find_decomp_wl_imp_find_decomp_wl_imp:
  \<open>(uncurry2 isa_find_decomp_wl_imp, uncurry2 (find_decomp_wl_imp \<A>)) \<in>
     [\<lambda>((M, lev), vm). lev < count_decided M]\<^sub>f trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<rightarrow>
     \<langle>trail_pol \<A> \<times>\<^sub>r (Id \<times>\<^sub>r distinct_atoms_rel \<A>)\<rangle>nres_rel\<close>
proof -
  have [intro]: \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow>  (M', M) \<in> trail_pol_no_CS \<A>\<close> for M' M
    by (auto simp: trail_pol_def trail_pol_no_CS_def control_stack_length_count_dec[symmetric])

  have [refine0]: \<open>((0, trail_pol_conv_to_no_CS x1c, x2c),
        0, trail_conv_to_no_CS x1a, x2a)
        \<in> nat_rel \<times>\<^sub>r trail_pol_no_CS \<A> \<times>\<^sub>r (Id \<times>\<^sub>r distinct_atoms_rel \<A>)\<close>
    if
      \<open>case y of
       (x, xa) \<Rightarrow> (case x of (M, lev) \<Rightarrow> \<lambda>_. lev < count_decided M) xa\<close> and
      \<open>(x, y)
       \<in> trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>)\<close> and   \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close> and
      \<open>isa_length_trail_pre (trail_pol_conv_to_no_CS x1c)\<close> and
      \<open>(pos, posa) \<in> nat_rel\<close> and
      \<open>length (trail_conv_to_no_CS x1a) - posa \<le> uint32_max\<close> and
      \<open>isa_length_trail (trail_pol_conv_to_no_CS x1c) - pos \<le> uint32_max\<close> and
      \<open>case (0, trail_conv_to_no_CS x1a, x2a) of
       (j, M, vm') \<Rightarrow>
         j \<le> length (trail_conv_to_no_CS x1a) - posa \<and>
         M = drop j (trail_conv_to_no_CS x1a) \<and>
         length (trail_conv_to_no_CS x1a) - posa
         \<le> length (trail_conv_to_no_CS x1a) \<and>
         vm' \<in> vmtf \<A> M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<close>
     for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa
  proof -
    show ?thesis
      supply trail_pol_conv_to_no_CS_def[simp] trail_conv_to_no_CS_def[simp]
      using that by auto
  qed
  have trail_pol_empty: \<open>(([], x2g), M) \<in> trail_pol_no_CS \<A> \<Longrightarrow> M = []\<close> for M x2g
    by (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def)

  have isa_vmtf: \<open>(x2c, x2a) \<in> Id \<times>\<^sub>f distinct_atoms_rel \<A> \<Longrightarrow>
       (((aa, ab, ac, ad, ba), baa, ca), x2e) \<in> Id \<times>\<^sub>f distinct_atoms_rel \<A> \<Longrightarrow>
       x2e \<in> vmtf \<A> (drop x1d x1a) \<Longrightarrow>
       ((aa, ab, ac, ad, ba), baa, ca) \<in> isa_vmtf \<A> (drop x1d x1a)\<close>
       for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x1h x2g x2h aa ab ac ad ba baa ca
       by (cases x2e)
        (auto 6 6 simp: isa_vmtf_def Image_iff converse_iff prod_rel_iff
         intro!: bexI[of _ x2e])
  have trail_pol_no_CS_last_hd:
    \<open>((x1h, t), M) \<in> trail_pol_no_CS \<A> \<Longrightarrow> M \<noteq> [] \<Longrightarrow> (last x1h) = lit_of (hd M)\<close>
    for x1h t M
    by (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def last_map last_rev)

  have trail_conv_back: \<open>trail_conv_back_imp x2b x1g
        \<le> SPEC
           (\<lambda>c. (c, trail_conv_back x2 x1e)
                \<in> trail_pol \<A>)\<close>
    if
      \<open>case y of (x, xa) \<Rightarrow> (case x of (M, lev) \<Rightarrow> \<lambda>vm. lev < count_decided M) xa\<close> and
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>)\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close> and
      \<open>isa_length_trail_pre (trail_pol_conv_to_no_CS x1c)\<close> and
      \<open>(pos, posa) \<in> nat_rel\<close> and
      \<open>length (trail_conv_to_no_CS x1a) - posa \<le> uint32_max\<close> and
      \<open>isa_length_trail (trail_pol_conv_to_no_CS x1c) - pos \<le> uint32_max\<close> and
      \<open>(xa, x') \<in> nat_rel \<times>\<^sub>f (trail_pol_no_CS \<A> \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>))\<close> and
       \<open>x2d = (x1e, x2e)\<close> and
      \<open>x' = (x1d, x2d)\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>xa = (x1f, x2f)\<close> and
      \<open>x2 = count_decided x1e\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x2g
   apply (rule trail_conv_back[THEN fref_to_Down_curry, THEN order_trans])
   using that by (auto simp: conc_fun_RETURN)


  show ?thesis
    supply trail_pol_conv_to_no_CS_def[simp] trail_conv_to_no_CS_def[simp]
    unfolding isa_find_decomp_wl_imp_def find_decomp_wl_imp_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      id_trail_conv_to_no_CS[THEN fref_to_Down, unfolded comp_def]
      get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail[of \<A>, THEN fref_to_Down_curry])
    subgoal
      by (rule isa_length_trail_pre) auto
    subgoal
      by (auto simp: get_pos_of_level_in_trail_pre_def)
    subgoal
      by auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    apply (assumption+)[10]
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (auto dest!: trail_pol_empty)
    subgoal
      by (auto dest!: trail_pol_empty)
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa
      by (rule tl_trailt_tr_no_CS_pre) auto
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x1h x2g x2h
       by (cases x1g, cases x2h)
         (auto intro!: vmtf_unset_pre[of _ _ _ _ _ _ \<A> \<open>drop x1d x1a\<close>] isa_vmtf
           simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def)
    subgoal
      by (auto simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def
        intro!: tl_trail_tr_no_CS[THEN fref_to_Down_unRET]
          isa_vmtf_unset_vmtf_unset[THEN fref_to_Down_unRET_uncurry])
    apply (rule trail_conv_back; assumption)
    subgoal
      by auto
  done
qed


abbreviation find_decomp_w_ns_prop where
  \<open>find_decomp_w_ns_prop \<A> \<equiv>
     (\<lambda>(M::(nat, nat) ann_lits) highest _.
        (\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = Suc highest \<and> vm \<in> vmtf \<A> M1))\<close>

definition find_decomp_w_ns where
  \<open>find_decomp_w_ns \<A> =
     (\<lambda>(M::(nat, nat) ann_lits) highest vm.
        SPEC(find_decomp_w_ns_prop \<A> M highest vm))\<close>

definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, D, oth)
  })\<close>


definition find_decomp_wl_st_int :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>highest (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats). do{
     (M', vm) \<leftarrow> isa_find_decomp_wl_imp M highest vm;
     RETURN (M', N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats)
  })\<close>


definition vmtf_rescore_body
 :: \<open>nat multiset \<Rightarrow> nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
    (nat \<times> vmtf_remove_int) nres\<close>
where
  \<open>vmtf_rescore_body \<A>\<^sub>i\<^sub>n C _ vm = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm). i \<le> length C  \<and>
            (\<forall>c \<in> set C. atm_of c < length (fst (fst vm)))\<^esup>
           (\<lambda>(i, vm). i < length C)
           (\<lambda>(i, vm). do {
               ASSERT(i < length C);
               ASSERT(atm_of (C!i) \<in># \<A>\<^sub>i\<^sub>n);
               let vm' = vmtf_mark_to_rescore (atm_of (C!i)) vm;
               RETURN(i+1, vm')
             })
           (0, vm)
    }\<close>

definition vmtf_rescore
 :: \<open>nat multiset \<Rightarrow> nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
       (vmtf_remove_int) nres\<close>
where
  \<open>vmtf_rescore \<A>\<^sub>i\<^sub>n C M vm = do {
      (_, vm) \<leftarrow> vmtf_rescore_body \<A>\<^sub>i\<^sub>n C M vm;
      RETURN (vm)
   }\<close>

find_theorems isa_vmtf_mark_to_rescore

definition isa_vmtf_rescore_body
 :: \<open>nat clause_l \<Rightarrow> trail_pol \<Rightarrow> isa_vmtf_remove_int \<Rightarrow>
    (nat \<times> isa_vmtf_remove_int) nres\<close>
where
  \<open>isa_vmtf_rescore_body C _ vm = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm). i \<le> length C  \<and>
            (\<forall>c \<in> set C. atm_of c < length (fst (fst vm)))\<^esup>
           (\<lambda>(i, vm). i < length C)
           (\<lambda>(i, vm). do {
               ASSERT(i < length C);
               ASSERT(isa_vmtf_mark_to_rescore_pre (atm_of (C!i)) vm);
               let vm' = isa_vmtf_mark_to_rescore (atm_of (C!i)) vm;
               RETURN(i+1, vm')
             })
           (0, vm)
    }\<close>

definition isa_vmtf_rescore
 :: \<open>nat clause_l \<Rightarrow> trail_pol \<Rightarrow> isa_vmtf_remove_int \<Rightarrow>
       (isa_vmtf_remove_int) nres\<close>
where
  \<open>isa_vmtf_rescore C M vm = do {
      (_, vm) \<leftarrow> isa_vmtf_rescore_body C M vm;
      RETURN (vm)
    }\<close>

lemma vmtf_rescore_score_clause:
  \<open>(uncurry2 (vmtf_rescore \<A>), uncurry2 (rescore_clause \<A>)) \<in>
     [\<lambda>((C, M), vm). literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C) \<and> vm \<in> vmtf \<A> M]\<^sub>f
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>vmtf_rescore_body \<A> C M vm \<le>
        SPEC (\<lambda>(n :: nat, vm').  vm' \<in> vmtf \<A> M)\<close>
    if M: \<open>vm \<in> vmtf \<A> M\<close> and C: \<open>\<forall>c\<in>set C. atm_of c \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    for C vm \<phi> M
    unfolding vmtf_rescore_body_def vmtf_mark_to_rescore_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
       I' = \<open>\<lambda>(i, vm'). vm' \<in> vmtf \<A> M\<close>])
    subgoal by auto
    subgoal by auto
    subgoal using C M by (auto simp: vmtf_def phase_saving_def)
    subgoal using C M by auto
    subgoal using M by auto
    subgoal using C by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    subgoal using C by auto
    subgoal using C by auto
    subgoal using C by (auto simp: vmtf_append_remove_iff')
    subgoal by auto
    done
  have K: \<open>((a, b),(a', b')) \<in> A \<times>\<^sub>f B \<longleftrightarrow> (a, a') \<in> A \<and> (b, b') \<in> B\<close> for a b a' b' A B
    by auto
  show ?thesis
    unfolding vmtf_rescore_def rescore_clause_def uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule bind_refine_spec)
     prefer 2
     apply (subst (asm) K)
     apply (rule H; auto)
    subgoal
      by (meson atm_of_lit_in_atms_of contra_subsetD in_all_lits_of_m_ain_atms_of_iff
          in_multiset_in_set literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by auto
    done
qed

lemma isa_vmtf_rescore_body:
  \<open>(uncurry2 (isa_vmtf_rescore_body), uncurry2 (vmtf_rescore_body \<A>)) \<in> [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
     (Id \<times>\<^sub>f trail_pol \<A> \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>)) \<rightarrow> \<langle>Id \<times>\<^sub>r (Id \<times>\<^sub>f distinct_atoms_rel \<A>)\<rangle> nres_rel\<close>
proof -
  show ?thesis
    unfolding isa_vmtf_rescore_body_def vmtf_rescore_body_def uncurry_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x1a x1b x2 x2a x2b x1c x1d x1e x2c x1g x2g
      by (cases x2g) auto
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x1a x1b x2 x2a x2b x1c x1d x1e x2c x2d x2e x1g x2g
      unfolding isa_vmtf_mark_to_rescore_pre_def
      by (cases x2e)
        (auto intro!: atms_hash_insert_pre)
    subgoal
      by (auto intro!:  isa_vmtf_mark_to_rescore_vmtf_mark_to_rescore[THEN fref_to_Down_unRET_uncurry])
    done
qed

lemma isa_vmtf_rescore:
  \<open>(uncurry2 (isa_vmtf_rescore), uncurry2 (vmtf_rescore \<A>)) \<in> [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
     (Id \<times>\<^sub>f trail_pol \<A> \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>)) \<rightarrow> \<langle>(Id \<times>\<^sub>f distinct_atoms_rel \<A>)\<rangle> nres_rel\<close>
proof -
  show ?thesis
    unfolding isa_vmtf_rescore_def vmtf_rescore_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg isa_vmtf_rescore_body[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal by auto
    done
qed

lemma
  assumes
    vm: \<open>vm \<in> vmtf \<A> M\<^sub>0\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<^sub>0\<close> and
    target: \<open>highest < count_decided M\<^sub>0\<close> and
    n_d: \<open>no_dup M\<^sub>0\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp \<A> M\<^sub>0 highest vm \<le> find_decomp_w_ns \<A> M\<^sub>0 highest vm\<close>
     (is ?decomp)
proof -
  have length_M0:  \<open>length M\<^sub>0 \<le> uint32_max div 2 + 1\<close>
    using length_trail_uint32_max_div2[of \<A> M\<^sub>0, OF bounded]
      n_d literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of \<A>, OF lits]
    by (auto simp: lits_of_def)
  have 1: \<open>((count_decided x1g, x1g), count_decided x1, x1) \<in> Id\<close>
    if \<open>x1g = x1\<close> for x1g x1 :: \<open>(nat, nat) ann_lits\<close>
    using that by auto
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g :: \<open>(nat, nat) ann_lits\<close>
    by (rule exI[of _ \<open>M' @ (if x2g = [] then [] else [hd x2g])\<close>]) auto
  have butlast_nil_iff: \<open>butlast xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>a. xs = [a])\<close> for xs :: \<open>(nat, nat) ann_lits\<close>
    by (cases xs) auto
  have butlast1: \<open>tl x2g = drop (Suc (length x1) - length x2g) x1\<close> (is \<open>?G1\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    show ?G1
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  have butlast2: \<open>tl x2g = drop (length x1 - (length x2g - Suc 0)) x1\<close> (is \<open>?G2\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> and x2g: \<open>x2g \<noteq> []\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that(1) zero_le)
    have [simp]: \<open>Suc (length x1) - length x2g = length x1 - (length x2g - Suc 0)\<close>
      using x2g by auto
    show ?G2
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  note butlast = butlast1 butlast2

  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply (solves simp)
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have Lin_drop_tl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (drop b M\<^sub>0)) \<Longrightarrow>
      literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (tl (drop b M\<^sub>0)))\<close> for b
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
     apply assumption
    by (cases \<open>drop b M\<^sub>0\<close>) auto

  have highest: \<open>highest = count_decided M\<close> and
     ex_decomp: \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> vmtf \<A> M\<close>
    if
      pos: \<open>pos < length M\<^sub>0 \<and> is_decided (rev M\<^sub>0 ! pos) \<and> get_level M\<^sub>0 (lit_of (rev M\<^sub>0 ! pos)) =
         highest + 1\<close> and
      \<open>length M\<^sub>0 - pos \<le> uint32_max\<close> and
      inv: \<open>case s of (j, M, vm') \<Rightarrow>
         j \<le> length M\<^sub>0 - pos \<and>
         M = drop j M\<^sub>0 \<and>
         length M\<^sub>0 - pos \<le> length M\<^sub>0 \<and>
         vm' \<in> vmtf \<A> M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<close> and
      cond: \<open>\<not> (case s of
         (j, M, vm) \<Rightarrow> j < length M\<^sub>0 - pos)\<close> and
      s: \<open>s = (j, s')\<close> \<open>s' = (M, vm)\<close>
    for pos s j s' M vm
  proof -
    have
      \<open>j = length M\<^sub>0 - pos\<close> and
      M: \<open>M = drop (length M\<^sub>0 - pos) M\<^sub>0\<close> and
      vm: \<open>vm \<in> vmtf \<A> (drop (length M\<^sub>0 - pos) M\<^sub>0)\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (drop (length M\<^sub>0 - pos) M\<^sub>0))\<close>
      using cond inv unfolding s
      by auto
    define M2 and L where \<open>M2 = take (length M\<^sub>0 - Suc pos) M\<^sub>0\<close> and \<open>L = rev M\<^sub>0 ! pos\<close>
    have le_Suc_pos: \<open>length M\<^sub>0 - pos = Suc (length M\<^sub>0 - Suc pos)\<close>
      using pos by auto
    have 1: \<open>take (length M\<^sub>0 - pos) M\<^sub>0 = take (length M\<^sub>0 - Suc pos) M\<^sub>0 @ [rev M\<^sub>0 ! pos]\<close>
      unfolding le_Suc_pos
      apply (subst take_Suc_conv_app_nth)
      using pos by (auto simp: rev_nth)
    have M\<^sub>0: \<open>M\<^sub>0 = M2 @ L # M\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>length M\<^sub>0 - pos\<close>])
      unfolding M L_def M2_def 1
      by auto
    have L': \<open>Decided (lit_of L) = L\<close>
      using pos unfolding L_def[symmetric] by (cases L) auto
    then have M\<^sub>0': \<open>M\<^sub>0 = M2 @ Decided (lit_of L) # M\<close>
      unfolding M\<^sub>0 by auto

    have \<open>highest = count_decided M\<close> and \<open>get_level M\<^sub>0 (lit_of L) = Suc highest\<close> and \<open>is_decided L\<close>
      using n_d pos unfolding L_def[symmetric] unfolding M\<^sub>0
      by (auto simp: get_level_append_if split: if_splits)
    then show
     \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> vmtf \<A> M\<close>
      using get_all_ann_decomposition_ex[of \<open>lit_of L\<close> M M2] vm unfolding M\<^sub>0'[symmetric] M[symmetric]
      by blast
    show \<open>highest = count_decided M\<close>
      using  \<open>highest = count_decided M\<close> .
  qed
  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_w_ns_def trail_conv_to_no_CS_def
      get_pos_of_level_in_trail_def trail_conv_back_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>])
    subgoal using length_M0 unfolding uint32_max_def by simp
    subgoal by auto
    subgoal by auto
    subgoal using target by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by auto
    subgoal by auto
    subgoal using vm by auto
    subgoal using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset by auto
    subgoal for target s j b M vm by simp
    subgoal using length_M0 unfolding uint32_max_def by simp
    subgoal for x s a ab aa bb
      by (cases \<open>drop a M\<^sub>0\<close>)
        (auto simp: lit_of_hd_trail_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal by (auto simp: drop_Suc drop_tl)
    subgoal by auto
    subgoal for s a b aa ba vm x2 x1a x2a
      by (cases vm)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N drop_tl simp: lit_of_hd_trail_def)
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (auto intro: Lin_drop_tl)
    subgoal by auto
    subgoal by (rule highest)
    subgoal by (rule ex_decomp) (assumption+, auto)
    done
qed


lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry2 (find_decomp_wl_imp \<A>), uncurry2 (find_decomp_w_ns \<A>)) \<in>
    [find_decomp_w_ns_pre \<A>]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: find_decomp_w_ns_pre_def simp del: twl_st_of_wl.simps
       intro!: find_decomp_wl_imp_le_find_decomp_wl')


lemma find_decomp_wl_imp_code_conbine_cond:
  \<open>(\<lambda>((b, a), c). find_decomp_w_ns_pre \<A> ((b, a), c) \<and> a < count_decided b) = (\<lambda>((b, a), c).
         find_decomp_w_ns_pre \<A> ((b, a), c))\<close>
  by (auto intro!: ext simp: find_decomp_w_ns_pre_def)



(* TODO use in vmtf_mark_to_rescore_and_unset *)

definition vmtf_mark_to_rescore_clause where
\<open>vmtf_mark_to_rescore_clause \<A>\<^sub>i\<^sub>n arena C vm = do {
    ASSERT(arena_is_valid_clause_idx arena C);
    nfoldli
      ([C..<C + (arena_length arena C)])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length arena);
        ASSERT(arena_lit_pre arena i);
        ASSERT(atm_of (arena_lit arena i) \<in># \<A>\<^sub>i\<^sub>n);
        RETURN (vmtf_mark_to_rescore (atm_of (arena_lit arena i)) vm)
      })
      vm
  }\<close>

definition isa_vmtf_mark_to_rescore_clause where
\<open>isa_vmtf_mark_to_rescore_clause arena C vm = do {
    ASSERT(arena_is_valid_clause_idx arena C);
    nfoldli
      ([C..<C + (arena_length arena C)])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length arena);
        ASSERT(arena_lit_pre arena i);
        ASSERT(isa_vmtf_mark_to_rescore_pre (atm_of (arena_lit arena i)) vm);
        RETURN (isa_vmtf_mark_to_rescore (atm_of (arena_lit arena i)) vm)
      })
      vm
  }\<close>

lemma isa_vmtf_mark_to_rescore_clause_vmtf_mark_to_rescore_clause:
  \<open>(uncurry2 isa_vmtf_mark_to_rescore_clause, uncurry2 (vmtf_mark_to_rescore_clause \<A>)) \<in> [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
    Id \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<rightarrow> \<langle>Id \<times>\<^sub>r distinct_atoms_rel \<A>\<rangle>nres_rel\<close>
  unfolding isa_vmtf_mark_to_rescore_clause_def vmtf_mark_to_rescore_clause_def
    uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg nfoldli_refine[where R = \<open>Id \<times>\<^sub>r distinct_atoms_rel \<A>\<close> and S = Id])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c xi xa si s
    by (cases s)
      (auto simp: isa_vmtf_mark_to_rescore_pre_def
        intro!: atms_hash_insert_pre)
  subgoal
    by (rule isa_vmtf_mark_to_rescore_vmtf_mark_to_rescore[THEN fref_to_Down_unRET_uncurry])
     auto
  done


lemma vmtf_mark_to_rescore_clause_spec:
  \<open>vm \<in> vmtf \<A>  M \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow>
   (\<forall>C \<in> set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow>
    vmtf_mark_to_rescore_clause \<A> arena C vm \<le> RES (vmtf \<A> M)\<close>
  unfolding vmtf_mark_to_rescore_clause_def
  apply (subst RES_SPEC_conv)
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ vm. vm \<in> vmtf \<A> M\<close>])
  subgoal
    unfolding arena_lit_pre_def arena_is_valid_clause_idx_def
    apply (rule exI[of _ N])
    apply (rule exI[of _ vdom])
    apply (fastforce simp: arena_lifting)
    done
  subgoal for x it \<sigma>
    using arena_lifting(7)[of arena N vdom C \<open>x - C\<close>]
    by (auto simp: arena_lifting(1-6) dest!: in_list_in_setD)
  subgoal for x it \<sigma>
    unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
    apply (rule exI[of _ C])
    apply (intro conjI)
    apply (solves \<open>auto dest: in_list_in_setD\<close>)
    apply (rule exI[of _ N])
    apply (rule exI[of _ vdom])
    apply (fastforce simp: arena_lifting dest: in_list_in_setD)
    done
  subgoal for x it \<sigma>
    by fastforce
  subgoal for x it _ \<sigma>
    by (cases \<sigma>)
     (auto intro!: vmtf_mark_to_rescore simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
       dest: in_list_in_setD)
  done

definition vmtf_mark_to_rescore_also_reasons
  :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> arena \<Rightarrow> nat literal list \<Rightarrow> _ \<Rightarrow>_\<close> where
\<open>vmtf_mark_to_rescore_also_reasons \<A> M arena outl vm = do {
    ASSERT(length outl \<le> uint32_max);
    nfoldli
      ([0..<length outl])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length outl); ASSERT(length outl \<le> uint32_max);
        ASSERT(-outl ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
        C \<leftarrow> get_the_propagation_reason M (-(outl ! i));
        case C of
          None \<Rightarrow> RETURN (vmtf_mark_to_rescore (atm_of (outl ! i)) vm)
        | Some C \<Rightarrow> if C = 0 then RETURN vm else vmtf_mark_to_rescore_clause \<A> arena C vm
      })
      vm
  }\<close>

definition isa_vmtf_mark_to_rescore_also_reasons
  :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> nat literal list \<Rightarrow> _ \<Rightarrow>_\<close> where
\<open>isa_vmtf_mark_to_rescore_also_reasons M arena outl vm = do {
    ASSERT(length outl \<le> uint32_max);
    nfoldli
      ([0..<length outl])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length outl); ASSERT(length outl\<le> uint32_max);
        C \<leftarrow> get_the_propagation_reason_pol M (-(outl ! i));
        case C of
          None \<Rightarrow> do {
            ASSERT (isa_vmtf_mark_to_rescore_pre (atm_of (outl ! i)) vm);
            RETURN (isa_vmtf_mark_to_rescore (atm_of (outl ! i)) vm)
	  }
        | Some C \<Rightarrow> if C = 0 then RETURN vm else isa_vmtf_mark_to_rescore_clause arena C vm
      })
      vm
  }\<close>

lemma isa_vmtf_mark_to_rescore_also_reasons_vmtf_mark_to_rescore_also_reasons:
  \<open>(uncurry3 isa_vmtf_mark_to_rescore_also_reasons, uncurry3 (vmtf_mark_to_rescore_also_reasons \<A>)) \<in>
    [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
    trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<rightarrow> \<langle>Id \<times>\<^sub>r distinct_atoms_rel \<A>\<rangle>nres_rel\<close>
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def vmtf_mark_to_rescore_also_reasons_def
    uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg nfoldli_refine[where R = \<open>Id \<times>\<^sub>r distinct_atoms_rel \<A>\<close> and S = Id]
    get_the_propagation_reason_pol[of \<A>, THEN fref_to_Down_curry]
     isa_vmtf_mark_to_rescore_clause_vmtf_mark_to_rescore_clause[of \<A>, THEN fref_to_Down_curry2])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply assumption
  subgoal for x y x1 x1a x1b x2 x2a x2b x1c x1d x1e x2c x2d x2e xi xa si s xb x'
    by (cases s)
     (auto simp: isa_vmtf_mark_to_rescore_pre_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        intro!: atms_hash_insert_pre[of _ \<A>])
  subgoal
    by (rule isa_vmtf_mark_to_rescore_vmtf_mark_to_rescore[THEN fref_to_Down_unRET_uncurry])
      (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  subgoal by auto
  subgoal by auto
  done

lemma vmtf_mark_to_rescore':
 \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow> vm \<in> vmtf \<A> M \<Longrightarrow> vmtf_mark_to_rescore L vm \<in> vmtf \<A> M\<close>
  by (cases vm) (auto intro: vmtf_mark_to_rescore)

lemma vmtf_mark_to_rescore_also_reasons_spec:
  \<open>vm \<in> vmtf \<A> M \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow> length outl \<le> uint32_max \<Longrightarrow>
   (\<forall>L \<in> set outl. L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow>
   (\<forall>L \<in> set outl. \<forall>C. (Propagated (-L) C \<in> set M \<longrightarrow> C \<noteq> 0 \<longrightarrow> (C \<in># dom_m N \<and>
       (\<forall>C \<in> set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)))) \<Longrightarrow>
    vmtf_mark_to_rescore_also_reasons \<A> M arena outl vm \<le> RES (vmtf \<A> M)\<close>
  unfolding vmtf_mark_to_rescore_also_reasons_def
  apply (subst RES_SPEC_conv)
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ vm. vm \<in> vmtf \<A> M\<close>])
  subgoal by (auto dest: in_list_in_setD)
  subgoal for x l1 l2 \<sigma>
    unfolding all_set_conv_nth
    by (auto simp: uminus_\<A>\<^sub>i\<^sub>n_iff dest!: in_list_in_setD)
  subgoal for x l1 l2 \<sigma>
    unfolding get_the_propagation_reason_def
    apply (rule SPEC_rule)
    apply (rename_tac reason, case_tac reason; simp only: option.simps RES_SPEC_conv[symmetric])
    subgoal
      by (auto simp: vmtf_mark_to_rescore'
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric])
    apply (rename_tac D, case_tac \<open>D = 0\<close>; simp)
    subgoal
      by (rule vmtf_mark_to_rescore_clause_spec, assumption, assumption)
       fastforce+
    done
  done

definition isa_vmtf_find_next_undef :: \<open>isa_vmtf_remove_int \<Rightarrow> trail_pol \<Rightarrow> (nat option) nres\<close> where
\<open>isa_vmtf_find_next_undef = (\<lambda>((ns, m, fst_As, lst_As, next_search), to_remove) M. do {
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
      (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<times>\<^sub>r trail_pol \<A>  \<rightarrow>\<^sub>f \<langle>\<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel \<close>
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

