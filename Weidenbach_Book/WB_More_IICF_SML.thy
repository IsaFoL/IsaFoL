theory WB_More_IICF_SML
  imports Refine_Imperative_HOL.IICF WB_More_Refinement WB_More_Refinement_List
begin

no_notation Sepref_Rules.fref ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)
no_notation Sepref_Rules.freft ("_ \<rightarrow>\<^sub>f _" [60,60] 60)
no_notation prod_assn (infixr "\<times>\<^sub>a" 70)
notation prod_assn (infixr "*a" 70)

hide_const Autoref_Fix_Rel.CONSTRAINT

lemma prod_assn_id_assn_destroy:
  fixes R :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close>
  shows \<open>R\<^sup>d *\<^sub>a id_assn\<^sup>d = (R *a id_assn)\<^sup>d\<close>
  by (auto simp: hfprod_def prod_assn_def[abs_def] invalid_assn_def pure_def intro!: ext)

lemma
 shows list_mset_assn_add_mset_Nil:
     \<open>list_mset_assn R (add_mset q Q) [] = false\<close> and
   list_mset_assn_empty_Cons:
    \<open>list_mset_assn R {#} (x # xs) = false\<close>
  unfolding list_mset_assn_def list_mset_rel_def mset_rel_def pure_def p2rel_def
    rel2p_def rel_mset_def br_def
  by (sep_auto simp: Collect_eq_comp)+


lemma list_mset_assn_add_mset_cons_in:
  assumes
    assn: \<open>A \<Turnstile> list_mset_assn R N (ab # list)\<close>
  shows \<open>\<exists>ab'. (ab, ab') \<in> the_pure R \<and> ab' \<in># N \<and> A \<Turnstile> list_mset_assn R (remove1_mset ab' N) (list)\<close>
proof -
  have H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (c = a)) = Id\<close>
    by (auto simp: the_pure_def H)
  have [iff]: \<open>(ab # list, y) \<in> list_mset_rel \<longleftrightarrow> y = add_mset ab (mset list)\<close> for y ab list
    by (auto simp: list_mset_rel_def br_def)
  obtain N' xs where
    N_N': \<open>N = mset N'\<close> and
    \<open>mset xs = add_mset ab (mset list)\<close> and
    \<open>list_all2 (rel2p (the_pure R)) xs N'\<close>
    using assn by (cases A) (auto simp: list_mset_assn_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def)
  then obtain N'' where
    \<open>list_all2 (rel2p (the_pure R)) (ab # list) N''\<close> and
    \<open>mset N'' = mset N'\<close>
    using list_all2_reorder_left_invariance[of \<open>rel2p (the_pure R)\<close> xs N'
          \<open>ab # list\<close>, unfolded eq_commute[of \<open>mset (ab # list)\<close>]] by auto
  then obtain n N''' where
    n: \<open>add_mset n (mset N''') = mset N''\<close> and
    \<open>(ab, n) \<in> the_pure R\<close> and
    \<open>list_all2 (rel2p (the_pure R)) list N'''\<close>
    by (auto simp: list_all2_Cons1 rel2p_def)
  moreover have \<open>n \<in> set N''\<close>
    using n unfolding mset.simps[symmetric] eq_commute[of \<open>add_mset _ _\<close>] apply -
    by (drule mset_eq_setD) auto
  ultimately have \<open>(ab, n) \<in> the_pure R\<close> and
    \<open>n \<in> set N''\<close> and
    \<open>mset list = mset list\<close> and
    \<open>mset N''' = remove1_mset n (mset N'')\<close> and
    \<open>list_all2 (rel2p (the_pure R)) list N'''\<close>
    by (auto dest: mset_eq_setD simp: eq_commute[of \<open>add_mset _ _\<close>])
  show ?thesis
    unfolding list_mset_assn_def mset_rel_def p2rel_def rel_mset_def
      list.rel_eq list_mset_rel_def
      br_def N_N'
    using assn \<open>(ab, n) \<in> the_pure R\<close>  \<open>n \<in> set N''\<close>  \<open>mset N'' = mset N'\<close>
      \<open>list_all2 (rel2p (the_pure R)) list N'''\<close>
        \<open>mset N'' = mset N'\<close> \<open>mset N''' = remove1_mset n (mset N'')\<close>
    by (cases A) (auto simp: list_mset_assn_def mset_rel_def p2rel_def rel_mset_def
        add_mset_eq_add_mset list.rel_eq
        intro!: exI[of _ n]
        dest: mset_eq_setD)
qed

lemma list_mset_assn_empty_nil: \<open>list_mset_assn R {#} [] = emp\<close>
  by (auto simp: list_mset_assn_def list_mset_rel_def mset_rel_def
      br_def p2rel_def rel2p_def Collect_eq_comp rel_mset_def
      pure_def)

lemma is_Nil_is_empty[sepref_fr_rules]:
  \<open>(return o is_Nil, RETURN o Multiset.is_empty) \<in> (list_mset_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi)
    apply (case_tac x)
   by (sep_auto simp: Multiset.is_empty_def list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil
      split: list.splits)+


lemma list_all2_remove:
  assumes
    uniq: \<open>IS_RIGHT_UNIQUE (p2rel R)\<close> \<open>IS_LEFT_UNIQUE (p2rel R)\<close> and
    Ra: \<open>R a aa\<close> and
    all: \<open>list_all2 R xs ys\<close>
  shows
  \<open>\<exists>xs'. mset xs' = remove1_mset a (mset xs) \<and>
            (\<exists>ys'. mset ys' = remove1_mset aa (mset ys) \<and> list_all2 R xs' ys')\<close>
  using all
proof (induction xs ys rule: list_all2_induct)
  case Nil
  then show ?case by auto
next
  case (Cons x y xs ys) note IH = this(3) and p = this(1, 2)

  have ax: \<open>{#a, x#} = {#x, a#}\<close>
    by auto
  have rem1: \<open>remove1_mset a (remove1_mset x M) = remove1_mset x (remove1_mset a M)\<close> for M
    by (auto simp: ax)
  have H: \<open>x = a \<longleftrightarrow> y = aa\<close>
    using uniq Ra p unfolding single_valued_def IS_LEFT_UNIQUE_def p2rel_def by blast

  obtain xs' ys' where
   \<open>mset xs' = remove1_mset a (mset xs)\<close> and
   \<open>mset ys' = remove1_mset aa (mset ys)\<close> and
   \<open>list_all2 R xs' ys'\<close>
   using IH p by auto
  then show ?case
   apply (cases \<open>x \<noteq> a\<close>)
   subgoal
     using p
     by (auto intro!: exI[of _ \<open>x#xs'\<close>] exI[of _ \<open>y#ys'\<close>]
         simp: diff_add_mset_remove1 rem1 add_mset_remove_trivial_If in_remove1_mset_neq H
         simp del: diff_diff_add_mset)
   subgoal
     using p
     by (fastforce simp: diff_add_mset_remove1 rem1 add_mset_remove_trivial_If in_remove1_mset_neq
         remove_1_mset_id_iff_notin H
         simp del: diff_diff_add_mset)
   done
qed

lemma remove1_remove1_mset:
  assumes uniq: \<open>IS_RIGHT_UNIQUE R\<close> \<open>IS_LEFT_UNIQUE R\<close>
  shows \<open>(uncurry (RETURN oo remove1), uncurry (RETURN oo remove1_mset)) \<in>
    R \<times>\<^sub>r (list_mset_rel O \<langle>R\<rangle> mset_rel) \<rightarrow>\<^sub>f
    \<langle>list_mset_rel O \<langle>R\<rangle> mset_rel\<rangle> nres_rel\<close>
  using list_all2_remove[of \<open>rel2p R\<close>] assms
  by (intro frefI nres_relI) (fastforce simp: list_mset_rel_def br_def mset_rel_def p2rel_def
      rel2p_def[abs_def] rel_mset_def Collect_eq_comp)

lemma
  Nil_list_mset_rel_iff:
    \<open>([], aaa) \<in> list_mset_rel \<longleftrightarrow> aaa = {#}\<close> and
  empty_list_mset_rel_iff:
    \<open>(a, {#}) \<in> list_mset_rel \<longleftrightarrow> a = []\<close>
  by (auto simp: list_mset_rel_def br_def)


lemma snd_hnr_pure:
   \<open>CONSTRAINT is_pure B \<Longrightarrow> (return \<circ> snd, RETURN \<circ> snd) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a B\<close>
  apply sepref_to_hoare
  apply sep_auto
  by (metis SLN_def SLN_left assn_times_comm ent_pure_pre_iff_sng ent_refl ent_star_mono
      ent_true is_pure_assn_def is_pure_iff_pure_assn)

text \<open>
  This theorem is useful to debug situation where sepref is not able to synthesize a program (with
  the ``[[unify\_trace\_failure]]'' to trace what fails in rule rule and the \<^text>\<open>to_hnr\<close> to
  ensure the theorem has the correct form).
\<close>
lemma Pair_hnr: \<open>(uncurry (return oo (\<lambda>a b. Pair a b)), uncurry (RETURN oo (\<lambda>a b. Pair a b))) \<in>
    A\<^sup>d *\<^sub>a B\<^sup>d \<rightarrow>\<^sub>a prod_assn A B\<close>
  by sepref_to_hoare sep_auto


text \<open>This version works only for \<^emph>\<open>pure\<close> refinement relations:\<close>
lemma the_hnr_keep:
  \<open>CONSTRAINT is_pure A \<Longrightarrow> (return o the, RETURN o the) \<in> [\<lambda>D. D \<noteq> None]\<^sub>a (option_assn A)\<^sup>k \<rightarrow> A\<close>
  using pure_option[of A]
  by sepref_to_hoare
   (sep_auto simp: option_assn_alt_def is_pure_def split: option.splits)

definition list_rel_mset_rel where list_rel_mset_rel_internal:
\<open>list_rel_mset_rel \<equiv> \<lambda>R. \<langle>R\<rangle>list_rel O list_mset_rel\<close>

lemma list_rel_mset_rel_def[refine_rel_defs]:
  \<open>\<langle>R\<rangle>list_rel_mset_rel = \<langle>R\<rangle>list_rel O list_mset_rel\<close>
  unfolding relAPP_def list_rel_mset_rel_internal ..

lemma list_mset_assn_pure_conv:
  \<open>list_mset_assn (pure R) = pure (\<langle>R\<rangle>list_rel_mset_rel)\<close>
  apply (intro ext)
  using list_all2_reorder_left_invariance
  by (fastforce
    simp: list_rel_mset_rel_def list_mset_assn_def
      mset_rel_def rel2p_def[abs_def] rel_mset_def p2rel_def
      list_mset_rel_def[abs_def] Collect_eq_comp br_def
      list_rel_def Collect_eq_comp_right
    intro!: arg_cong[of _ _ \<open>\<lambda>b. pure b _ _\<close>])

lemma list_assn_list_mset_rel_eq_list_mset_assn:
  assumes p: \<open>is_pure R\<close>
  shows \<open>hr_comp (list_assn R) list_mset_rel = list_mset_assn R\<close>
proof -
  define R' where \<open>R' = the_pure R\<close>
  then have R: \<open>R = pure R'\<close>
    using p by auto
  show ?thesis
    apply (auto simp: list_mset_assn_def
        list_assn_pure_conv
        relcomp.simps hr_comp_pure mset_rel_def br_def
        p2rel_def rel2p_def[abs_def] rel_mset_def R list_mset_rel_def list_rel_def)
      using list_all2_reorder_left_invariance by fastforce
  qed

lemma list_rel_mset_rel_imp_same_length: \<open>(a, b) \<in> \<langle>R\<rangle>list_rel_mset_rel \<Longrightarrow> length a = size b\<close>
  by (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def
      dest: list_rel_imp_same_length)


lemma id_ref: \<open>(return o id, RETURN o id) \<in> R\<^sup>d \<rightarrow>\<^sub>a R\<close>
  by sepref_to_hoare sep_auto

text \<open>This functions deletes all elements of a resizable array, without resizing it.\<close>
definition emptied_arl :: \<open>'a array_list \<Rightarrow> 'a array_list\<close> where
\<open>emptied_arl = (\<lambda>(a, n). (a, 0))\<close>

lemma emptied_arl_refine[sepref_fr_rules]:
  \<open>(return o emptied_arl, RETURN o emptied_list) \<in> (arl_assn R)\<^sup>d \<rightarrow>\<^sub>a arl_assn R\<close>
  unfolding emptied_arl_def emptied_list_def
  by sepref_to_hoare (sep_auto simp: arl_assn_def hr_comp_def is_array_list_def)

lemma bool_assn_alt_def: \<open>bool_assn a b = \<up> (a = b)\<close>
  unfolding pure_def by auto

lemma nempty_list_mset_rel_iff: \<open>M \<noteq> {#} \<Longrightarrow>
  (xs, M) \<in> list_mset_rel \<longleftrightarrow> (xs \<noteq> [] \<and> hd xs \<in># M \<and>
         (tl xs, remove1_mset (hd xs) M) \<in> list_mset_rel)\<close>
  by (cases xs) (auto simp: list_mset_rel_def br_def dest!: multi_member_split)

abbreviation ghost_assn where
  \<open>ghost_assn \<equiv> hr_comp unit_assn virtual_copy_rel\<close>

lemma [sepref_fr_rules]:
 \<open>(return o (\<lambda>_. ()), RETURN o virtual_copy) \<in> R\<^sup>k \<rightarrow>\<^sub>a ghost_assn\<close>
 by sepref_to_hoare (sep_auto simp: virtual_copy_rel_def)


lemma id_mset_list_assn_list_mset_assn:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(return o id, RETURN o mset) \<in> (list_assn R)\<^sup>d \<rightarrow>\<^sub>a list_mset_assn R\<close>
proof -
  obtain R' where R: \<open>R = pure R'\<close>
    using assms is_pure_conv unfolding CONSTRAINT_def by blast
  then have R': \<open>the_pure R = R'\<close>
    unfolding R by auto
  show ?thesis
    apply (subst R)
    apply (subst list_assn_pure_conv)
    apply sepref_to_hoare
    by (sep_auto simp: list_mset_assn_def R' pure_def list_mset_rel_def mset_rel_def
       p2rel_def rel2p_def[abs_def] rel_mset_def br_def Collect_eq_comp list_rel_def)
qed

subsection \<open>Sorting\<close>

text \<open>Remark that we do not \<^emph>\<open>prove\<close> that the sorting in correct, since we do not care about the
 correctness, only the fact that it is reordered. (Based on wikipedia's algorithm.)
Typically \<^term>\<open>R\<close> would be \<^term>\<open>(<)\<close>\<close>
definition insert_sort_inner :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow>  nat \<Rightarrow> 'a list nres\<close> where
  \<open>insert_sort_inner R f xs i = do {
     (j, ys) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(j, ys). j \<ge> 0 \<and> mset xs = mset ys \<and> j < length ys\<^esup>
         (\<lambda>(j, ys). j > 0 \<and> R (f ys j) (f ys (j - 1)))
         (\<lambda>(j, ys). do {
             ASSERT(j < length ys);
             ASSERT(j > 0);
             ASSERT(j-1 < length ys);
             let xs = swap ys j (j - 1);
             RETURN (j-1, xs)
           }
         )
        (i, xs);
     RETURN ys
  }\<close>


(* A check: *)
lemma \<open>RETURN [Suc 0, 2, 0] = insert_sort_inner (<) (\<lambda>remove n. remove ! n) [2::nat, 1, 0] 1\<close>
  by (simp add: WHILEIT_unfold insert_sort_inner_def swap_def)

definition insert_sort :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list nres\<close> where
  \<open>insert_sort R f xs = do {
     (i, ys) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, ys). (ys = [] \<or> i \<le> length ys) \<and> mset xs = mset ys\<^esup>
        (\<lambda>(i, ys). i < length ys)
        (\<lambda>(i, ys). do {
            ASSERT(i < length ys);
            ys \<leftarrow> insert_sort_inner R f ys i;
            RETURN (i+1, ys)
          })
        (1, xs);
     RETURN ys
  }\<close>

lemma insert_sort_inner:
   \<open>(uncurry (insert_sort_inner R f), uncurry (\<lambda>m m'. reorder_list m' m)) \<in>
      [\<lambda>(xs, i). i < length xs]\<^sub>f \<langle>Id:: ('a \<times> 'a) set\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  unfolding insert_sort_inner_def uncurry_def reorder_list_def
  apply (intro frefI nres_relI)
  apply clarify
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, _). i)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto dest: mset_eq_length)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

lemma insert_sort_reorder_list:
  \<open>(insert_sort R f, reorder_list vm) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>ba < length aa \<Longrightarrow> insert_sort_inner R f aa ba \<le> SPEC (\<lambda>m'. mset m' = mset aa)\<close>
    for ba aa
    using insert_sort_inner[unfolded fref_def nres_rel_def reorder_list_def, simplified]
    by fast
  show ?thesis
    unfolding insert_sort_def reorder_list_def
    apply (intro frefI nres_relI)
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, ys). length ys - i)\<close>] H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest: mset_eq_length)
    subgoal by auto
    subgoal by (auto dest!: mset_eq_length)
    subgoal by auto
    done
qed

definition arl_replicate where
 "arl_replicate init_cap x \<equiv> do {
    let n = max init_cap minimum_capacity;
    a \<leftarrow> Array.new n x;
    return (a,init_cap)
  }"

definition \<open>op_arl_replicate = op_list_replicate\<close>
lemma arl_fold_custom_replicate:
  \<open>replicate = op_arl_replicate\<close>
  unfolding op_arl_replicate_def op_list_replicate_def ..

lemma list_replicate_arl_hnr[sepref_fr_rules]:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry arl_replicate, uncurry (RETURN oo op_arl_replicate)) \<in> nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow>\<^sub>a arl_assn R\<close>
proof -
  obtain R' where
     R'[symmetric]: \<open>R' = the_pure R\<close> and
     R_R': \<open>R = pure R'\<close>
    using assms by fastforce
  have [simp]: \<open>pure R' b bi = \<up>((bi, b) \<in> R')\<close> for b bi
    by (auto simp: pure_def)
  have [simp]: \<open>min a (max a 16) = a\<close> for a :: nat
    by auto
  show ?thesis
    using assms unfolding op_arl_replicate_def
    by sepref_to_hoare
      (sep_auto simp: arl_replicate_def arl_assn_def hr_comp_def R' R_R' list_rel_def
        is_array_list_def minimum_capacity_def
        intro!: list_all2_replicate)
qed

lemma option_bool_assn_direct_eq_hnr:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in>
    (option_assn bool_assn)\<^sup>k *\<^sub>a (option_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: option_assn_alt_def split:option.splits)

text \<open>This function does not change the size of the underlying array.\<close>
definition take1 where
  \<open>take1 xs = take 1 xs\<close>

lemma take1_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>(a, _). (a, 1::nat)), RETURN o take1) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (arl_assn R)\<^sup>d \<rightarrow> arl_assn R\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: arl_assn_def hr_comp_def take1_def list_rel_def
      is_array_list_def)
  apply (case_tac b; case_tac x; case_tac l')
   apply (auto)
  done

text \<open>The following two abbreviation are variants from \<^term>\<open>uncurry4\<close> and
   \<^term>\<open>uncurry6\<close>. The problem is that \<^term>\<open>uncurry2 (uncurry2 f)\<close> and
   \<^term>\<open>uncurry (uncurry3 f)\<close> are the same term, but only the latter is folded
   to \<^term>\<open>uncurry4\<close>.\<close>
abbreviation uncurry4' where
  "uncurry4' f \<equiv> uncurry2 (uncurry2 f)"

abbreviation uncurry6' where
  "uncurry6' f \<equiv> uncurry2 (uncurry4' f)"


definition find_in_list_between :: \<open>('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat option nres\<close> where
  \<open>find_in_list_between P a b C = do {
      (x, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> a \<and> i \<le> length C \<and> i \<le> b \<and> (\<forall>j\<in>{a..<i}. \<not>P (C!j)) \<and>
        (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> P (C ! j) \<and> j < b \<and> j \<ge> a))\<^esup>
        (\<lambda>(found, i). found = None \<and> i < b)
        (\<lambda>(_, i). do {
          ASSERT(i < length C);
          if P (C!i) then RETURN (Some i, i) else RETURN (None, i+1)
        })
        (None, a);
      RETURN x
  }\<close>

lemma find_in_list_between_spec:
  assumes \<open>a \<le> length C\<close> and \<open>b \<le> length C\<close> and \<open>a \<le> b\<close>
  shows
    \<open>find_in_list_between P a b C \<le> SPEC(\<lambda>i.
       (i \<noteq> None \<longrightarrow>  P (C ! the i) \<and> the i \<ge> a \<and> the i < b) \<and>
       (i = None \<longrightarrow> (\<forall>j. j \<ge> a \<longrightarrow> j < b \<longrightarrow> \<not>P (C!j))))\<close>
  unfolding find_in_list_between_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(f, i). Suc (length C) - (i + (if f = None then 0 else 1)))\<close>])
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
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
  subgoal by (auto simp: less_Suc_eq)
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

lemma list_assn_map_list_assn: \<open>list_assn g (map f x) xi = list_assn (\<lambda>a c. g (f a) c) x xi\<close>
  apply (induction x arbitrary: xi)
  subgoal by auto
  subgoal for a x xi
    by (cases xi) auto
  done


lemma hfref_imp2: "(\<And>x y. S x y \<Longrightarrow>\<^sub>t S' x y) \<Longrightarrow> [P]\<^sub>a RR \<rightarrow> S \<subseteq> [P]\<^sub>a RR \<rightarrow> S'"
    apply clarsimp
    apply (erule hfref_cons)
    apply (simp_all add: hrp_imp_def)
    done

lemma hr_comp_mono_entails: \<open>B \<subseteq> C \<Longrightarrow> hr_comp a B x y \<Longrightarrow>\<^sub>A hr_comp a C x y\<close>
  unfolding hr_comp_def entails_def
  by auto

lemma hfref_imp_mono_result:
  "B \<subseteq> C \<Longrightarrow> [P]\<^sub>a RR \<rightarrow> hr_comp a B \<subseteq> [P]\<^sub>a RR \<rightarrow> hr_comp a C"
  unfolding hfref_def hn_refine_def
  apply clarify
  subgoal for aa b c aaa
    apply (rule cons_post_rule[of _ _
          \<open>\<lambda>r. snd RR aaa c * (\<exists>\<^sub>Ax. hr_comp a B x r * \<up> (RETURN x \<le> b aaa)) * true\<close>])
     apply (solves auto)
    using hr_comp_mono_entails[of B C a ]
    apply (auto intro!: ent_ex_preI)
    apply (rule_tac x=xa in ent_ex_postI)
    apply (auto intro!: ent_star_mono ac_simps)
    done
  done

lemma hfref_imp_mono_result2:
  "(\<And>x. P L x \<Longrightarrow> B L \<subseteq> C L) \<Longrightarrow> [P L]\<^sub>a RR \<rightarrow> hr_comp a (B L) \<subseteq> [P L]\<^sub>a RR \<rightarrow> hr_comp a (C L)"
  unfolding hfref_def hn_refine_def
  apply clarify
  subgoal for aa b c aaa
    apply (rule cons_post_rule[of _ _
          \<open>\<lambda>r. snd RR aaa c * (\<exists>\<^sub>Ax. hr_comp a (B L) x r * \<up> (RETURN x \<le> b aaa)) * true\<close>])
     apply (solves auto)
    using hr_comp_mono_entails[of \<open>B L\<close> \<open>C L\<close> a ]
    apply (auto intro!: ent_ex_preI)
    apply (rule_tac x=xa in ent_ex_postI)
    apply (auto intro!: ent_star_mono ac_simps)
    done
  done

lemma ex_assn_up_eq2: \<open>(\<exists>\<^sub>Aba. f ba * \<up> (ba = c)) = (f c)\<close>
  by (simp add: ex_assn_def)


lemma ex_assn_pair_split: \<open>(\<exists>\<^sub>Ab. P b) = (\<exists>\<^sub>Aa b. P (a, b))\<close>
  by (subst ex_assn_def, subst (1) ex_assn_def, auto)+

lemma ex_assn_swap: \<open>(\<exists>\<^sub>Aa b. P a b) = (\<exists>\<^sub>Ab a. P a b)\<close>
  by (meson ent_ex_postI ent_ex_preI ent_iffI ent_refl)

lemma ent_ex_up_swap: \<open>(\<exists>\<^sub>Aaa. \<up> (P aa)) = (\<up>(\<exists>aa. P aa))\<close>
  by (smt ent_ex_postI ent_ex_preI ent_iffI ent_pure_pre_iff ent_refl mult.left_neutral)

lemma ex_assn_def_pure_eq_middle3:
  \<open>(\<exists>\<^sub>Aba b bb. f b ba bb * \<up> (ba = h b bb) * P b ba bb) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * P b (h b bb) bb)\<close>
  \<open>(\<exists>\<^sub>Ab ba bb. f b ba bb * \<up> (ba = h b bb) * P b ba bb) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * P b (h b bb) bb)\<close>
  \<open>(\<exists>\<^sub>Ab bb ba. f b ba bb * \<up> (ba = h b bb) * P b ba bb) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * P b (h b bb) bb)\<close>
  \<open>(\<exists>\<^sub>Aba b bb. f b ba bb * \<up> (ba = h b bb \<and> Q b ba bb)) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * \<up>(Q b (h b bb) bb))\<close>
  \<open>(\<exists>\<^sub>Ab ba bb. f b ba bb * \<up> (ba = h b bb \<and> Q b ba bb)) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * \<up>(Q b (h b bb) bb))\<close>
  \<open>(\<exists>\<^sub>Ab bb ba. f b ba bb * \<up> (ba = h b bb \<and> Q b ba bb)) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * \<up>(Q b (h b bb) bb))\<close>
  by (subst ex_assn_def, subst (3) ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_middle2:
  \<open>(\<exists>\<^sub>Aba b. f b ba * \<up> (ba = h b) * P b ba) = (\<exists>\<^sub>Ab . f b (h b) * P b (h b))\<close>
  \<open>(\<exists>\<^sub>Ab ba. f b ba * \<up> (ba = h b) * P b ba) = (\<exists>\<^sub>Ab . f b (h b) * P b (h b))\<close>
  \<open>(\<exists>\<^sub>Ab ba. f b ba * \<up> (ba = h b \<and> Q b ba)) = (\<exists>\<^sub>Ab. f b (h b) * \<up>(Q b (h b)))\<close>
  \<open>(\<exists>\<^sub>A ba b. f b ba * \<up> (ba = h b \<and> Q b ba)) = (\<exists>\<^sub>Ab. f b (h b) * \<up>(Q b (h b)))\<close>
  by (subst ex_assn_def, subst (2) ex_assn_def, auto)+

lemma ex_assn_skip_first2:
  \<open>(\<exists>\<^sub>Aba bb. f bb * \<up>(P ba bb)) = (\<exists>\<^sub>Abb. f bb * \<up>(\<exists>ba. P ba bb))\<close>
  \<open>(\<exists>\<^sub>Abb ba. f bb * \<up>(P ba bb)) = (\<exists>\<^sub>Abb. f bb * \<up>(\<exists>ba. P ba bb))\<close>
  apply (subst ex_assn_swap)
  by (subst ex_assn_def, subst (2) ex_assn_def, auto)+

lemma fr_refl': \<open>A \<Longrightarrow>\<^sub>A B \<Longrightarrow> C * A \<Longrightarrow>\<^sub>A C * B\<close>
  unfolding assn_times_comm[of C]
  by (rule Automation.fr_refl)

lemma hrp_comp_Id2[simp]: \<open>hrp_comp A Id = A\<close>
  unfolding hrp_comp_def by auto

lemma hn_ctxt_prod_assn_prod:
  \<open>hn_ctxt (R *a S) (a, b) (a', b') = hn_ctxt R a a' * hn_ctxt S b b'\<close>
  unfolding hn_ctxt_def
  by auto


lemma hfref_weaken_change_pre:
  assumes "(f,h) \<in> hfref P R S"
  assumes "\<And>x. P x \<Longrightarrow> (fst R x, snd R x) = (fst R' x, snd R' x)"
  assumes "\<And>y x. S y x \<Longrightarrow>\<^sub>t S' y x"
  shows "(f,h) \<in> hfref P R' S'"
proof -
  have \<open>(f,h) \<in> hfref P R' S\<close>
    using assms
    by (auto simp: hfref_def)
  then show ?thesis
    using hfref_imp2[of S S' P R'] assms(3) by auto
qed


lemma norm_RETURN_o[to_hnr_post]:
  "\<And>f. (RETURN oooo f)$x$y$z$a = (RETURN$(f$x$y$z$a))"
  "\<And>f. (RETURN ooooo f)$x$y$z$a$b = (RETURN$(f$x$y$z$a$b))"
  "\<And>f. (RETURN oooooo f)$x$y$z$a$b$c = (RETURN$(f$x$y$z$a$b$c))"
  "\<And>f. (RETURN ooooooo f)$x$y$z$a$b$c$d = (RETURN$(f$x$y$z$a$b$c$d))"
  "\<And>f. (RETURN oooooooo f)$x$y$z$a$b$c$d$e = (RETURN$(f$x$y$z$a$b$c$d$e))"
  "\<And>f. (RETURN ooooooooo f)$x$y$z$a$b$c$d$e$g = (RETURN$(f$x$y$z$a$b$c$d$e$g))"
  "\<And>f. (RETURN oooooooooo f)$x$y$z$a$b$c$d$e$g$h= (RETURN$(f$x$y$z$a$b$c$d$e$g$h))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>1 f)$x$y$z$a$b$c$d$e$g$h$i= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>2 f)$x$y$z$a$b$c$d$e$g$h$i$j= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>3 f)$x$y$z$a$b$c$d$e$g$h$i$j$l= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>4 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>5 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>6 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>7 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>8 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>9 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t))"
  "\<And>f. (RETURN \<circ>\<^sub>2\<^sub>0 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u))"
  by auto

lemma norm_return_o[to_hnr_post]:
  "\<And>f. (return oooo f)$x$y$z$a = (return$(f$x$y$z$a))"
  "\<And>f. (return ooooo f)$x$y$z$a$b = (return$(f$x$y$z$a$b))"
  "\<And>f. (return oooooo f)$x$y$z$a$b$c = (return$(f$x$y$z$a$b$c))"
  "\<And>f. (return ooooooo f)$x$y$z$a$b$c$d = (return$(f$x$y$z$a$b$c$d))"
  "\<And>f. (return oooooooo f)$x$y$z$a$b$c$d$e = (return$(f$x$y$z$a$b$c$d$e))"
  "\<And>f. (return ooooooooo f)$x$y$z$a$b$c$d$e$g = (return$(f$x$y$z$a$b$c$d$e$g))"
  "\<And>f. (return oooooooooo f)$x$y$z$a$b$c$d$e$g$h= (return$(f$x$y$z$a$b$c$d$e$g$h))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>1 f)$x$y$z$a$b$c$d$e$g$h$i= (return$(f$x$y$z$a$b$c$d$e$g$h$i))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>2 f)$x$y$z$a$b$c$d$e$g$h$i$j= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>3 f)$x$y$z$a$b$c$d$e$g$h$i$j$l= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>4 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>5 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>6 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>7 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>8 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>9 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t))"
  "\<And>f. (return \<circ>\<^sub>2\<^sub>0 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u))"
    by auto


lemma nfoldli_cong2:
  assumes
    le: \<open>length l = length l'\<close> and
    \<sigma>: \<open>\<sigma> = \<sigma>'\<close> and
    c: \<open>c = c'\<close> and
    H: \<open>\<And>\<sigma> x. x < length l \<Longrightarrow> c' \<sigma> \<Longrightarrow> f (l ! x) \<sigma> = f' (l' ! x) \<sigma>\<close>
  shows \<open>nfoldli l c f \<sigma> = nfoldli l' c' f' \<sigma>'\<close>
proof -
  show ?thesis
    using le H unfolding c[symmetric] \<sigma>[symmetric]
  proof (induction l arbitrary: l' \<sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons a l l'') note IH=this(1) and le = this(2) and H = this(3)
    show ?case
      using le H[of \<open>Suc _\<close>] H[of 0] IH[of \<open>tl l''\<close> \<open>_\<close>]
      by (cases l'')
        (auto intro: bind_cong_nres)
  qed
qed

lemma nfoldli_nfoldli_list_nth:
  \<open>nfoldli xs c P a = nfoldli [0..<length xs] c (\<lambda>i. P (xs ! i)) a\<close>
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by auto
next
  case (Cons x xs) note IH = this(1)
  have 1: \<open>[0..<length (x # xs)] = 0 # [1..<length (x#xs)]\<close>
    by (subst upt_rec)  simp
  have 2: \<open>[1..<length (x#xs)] = map Suc [0..<length xs]\<close>
    by (induction xs) auto
  have AB: \<open>nfoldli [0..<length (x # xs)] c (\<lambda>i. P ((x # xs) ! i)) a =
      nfoldli (0 # [1..<length (x#xs)]) c (\<lambda>i. P ((x # xs) ! i)) a\<close>
      (is \<open>?A = ?B\<close>)
    unfolding 1 ..
  {
    assume [simp]: \<open>c a\<close>
    have \<open>nfoldli (0 # [1..<length (x#xs)]) c (\<lambda>i. P ((x # xs) ! i)) a =
       do {
         \<sigma> \<leftarrow> (P x a);
         nfoldli [1..<length (x#xs)] c (\<lambda>i. P ((x # xs) ! i)) \<sigma>
        }\<close>
      by simp
    moreover have \<open>nfoldli [1..<length (x#xs)] c (\<lambda>i. P ((x # xs) ! i)) \<sigma>  =
       nfoldli [0..<length xs] c (\<lambda>i. P (xs ! i)) \<sigma>\<close> for \<sigma>
      unfolding 2
      by (rule nfoldli_cong2) auto
    ultimately have \<open>?A = do {
         \<sigma> \<leftarrow> (P x a);
         nfoldli [0..<length xs] c (\<lambda>i. P (xs ! i))  \<sigma>
        }\<close>
      using AB
      by (auto intro: bind_cong_nres)
  }
  moreover {
    assume [simp]: \<open>\<not>c a\<close>
    have \<open>?B = RETURN a\<close>
      by simp
  }
  ultimately show ?case by (auto simp: IH intro: bind_cong_nres)
qed



lemma list_rel_update:
  fixes R :: \<open>'a \<Rightarrow> 'b :: {heap}\<Rightarrow> assn\<close>
  assumes rel: \<open>(xs, ys) \<in> \<langle>the_pure R\<rangle>list_rel\<close> and
   h: \<open>h \<Turnstile> A * R b bi\<close> and
   p: \<open>is_pure R\<close>
  shows \<open>(list_update xs ba bi, list_update ys ba b) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(bi, b) \<in> the_pure R\<close>
    using h p by (auto simp: mod_star_conv R R')
  have \<open>length xs = length ys\<close>
    using assms list_rel_imp_same_length by blast

  then show ?thesis
    using rel
    by (induction xs ys arbitrary: ba rule: list_induct2) (auto split: nat.splits)
qed

end