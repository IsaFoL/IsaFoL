theory CDCL_Two_Watched_Literals_List_Watched_Domain
  imports CDCL_Two_Watched_Literals_List_Watched Array_Array_List Array_List_Array
    WB_Word_Assn
begin

text \<open>We refine the implementation by adding a \<^emph>\<open>domain\<close> on the literals\<close>

no_notation Ref.update ("_ := _" 62)

subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym clauses_to_update_ll = \<open>nat list\<close>
type_synonym lit_queue_l = \<open>nat list\<close>
type_synonym nat_trail = \<open>(nat \<times> nat option) list\<close>
type_synonym clause_wl = \<open>nat array\<close>
type_synonym unit_lits_wl = \<open>nat list list\<close>

type_synonym watched_wl = \<open>(nat array_list) array\<close>

notation prod_assn (infixr "*assn" 90)


subsubsection \<open>Refinement of the Watched Function\<close>

definition map_fun_rel :: "(nat \<times> nat literal) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> (nat literal \<Rightarrow> 'a)) set" where
  map_fun_rel_def_internal: \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

lemma map_fun_rel_def:
  \<open>\<langle>R\<rangle>map_fun_rel D = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>
  unfolding relAPP_def map_fun_rel_def_internal by auto

definition map_fun_rel_assn :: "(nat \<times> nat literal) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> (nat literal \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>map_fun_rel_assn D R = pure (\<langle>the_pure R\<rangle>map_fun_rel D)\<close>

lemma [safe_constraint_rules]: \<open>is_pure (map_fun_rel_assn D R)\<close>
  unfolding map_fun_rel_assn_def by auto


subsection \<open>Literals as Natural Numbers\<close>

lemma Pos_div2_iff: \<open>Pos (bb div 2) = b \<longleftrightarrow> is_pos b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close> for bb :: nat
  by (cases b) auto
lemma Neg_div2_iff: \<open>Neg (bb div 2) = b \<longleftrightarrow> is_neg b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close> for bb :: nat
  by (cases b) auto

text \<open>
  Modeling \<^typ>\<open>nat literal\<close> via the transformation associating \<^term>\<open>2*n\<close> or \<^term>\<open>2*n+1\<close>
  has some advantages over the transformation to positive or negative integers: 0 is not an issue.\<close>
fun nat_of_lit :: \<open>nat literal \<Rightarrow> nat\<close> where
  \<open>nat_of_lit (Pos L) = 2*L\<close>
| \<open>nat_of_lit (Neg L) = 2*L + 1\<close>

lemma nat_of_lit_def: \<open>nat_of_lit L = (if is_pos L then 2*atm_of L else 2*atm_of L + 1)\<close>
  by (cases L) auto

fun literal_of_nat :: \<open>nat \<Rightarrow> nat literal\<close> where
  \<open>literal_of_nat n = (if even n then Pos (n div 2) else Neg (n div 2))\<close>

lemma lit_of_nat_nat_of_lit[simp]: \<open>literal_of_nat (nat_of_lit L) = L\<close>
  by (cases L) auto

lemma nat_of_lit_lit_of_nat[simp]: \<open>nat_of_lit (literal_of_nat n) = n\<close>
  by auto

lemma atm_of_lit_of_nat: \<open>atm_of (literal_of_nat n) = n div 2\<close>
  by auto

text \<open>There is probably a more ``closed'' form from the following theorem, but it is unclear if
  that is useful or not.\<close>
lemma uminus_lit_of_nat:
  \<open>- (literal_of_nat n) = (if even n then literal_of_nat (n+1) else literal_of_nat (n-1))\<close>
  by (auto elim!: oddE)

lemma literal_of_nat_literal_of_nat_eq[iff]: \<open>literal_of_nat x = literal_of_nat xa \<longleftrightarrow> x = xa\<close>
  by auto presburger+

definition lit_of_natP where
  \<open>lit_of_natP L L' \<longleftrightarrow> literal_of_nat L = L'\<close>

definition nat_lit_rel :: "(nat \<times> nat literal) set" where
  \<open>nat_lit_rel \<equiv> {(n, L). lit_of_natP n L}\<close>

abbreviation nat_lit_assn :: "nat literal \<Rightarrow> nat \<Rightarrow> assn" where
  \<open>nat_lit_assn \<equiv> pure nat_lit_rel\<close>

fun pair_of_ann_lit :: "('a, 'b) ann_lit \<Rightarrow> 'a literal \<times> 'b option" where
  \<open>pair_of_ann_lit (Propagated L D) = (L, Some D)\<close>
| \<open>pair_of_ann_lit (Decided L) = (L, None)\<close>

fun ann_lit_of_pair :: "'a literal \<times> 'b option \<Rightarrow> ('a, 'b) ann_lit" where
  \<open>ann_lit_of_pair (L, Some D) = Propagated L D\<close>
| \<open>ann_lit_of_pair (L, None) = Decided L\<close>

lemma ann_lit_of_pair_pair_of_ann_lit: \<open>ann_lit_of_pair (pair_of_ann_lit L) = L\<close>
  by (cases L) auto

lemma pair_of_ann_lit_ann_lit_of_pair: \<open>pair_of_ann_lit (ann_lit_of_pair L) = L\<close>
  by (cases L; cases \<open>snd L\<close>) auto


lemma literal_of_neq_eq_nat_of_lit_eq_iff: \<open>literal_of_nat b = L \<longleftrightarrow> b = nat_of_lit L\<close>
  by (auto simp del: literal_of_nat.simps)

lemma nat_of_lit_eq_iff[iff]: \<open>nat_of_lit xa = nat_of_lit x \<longleftrightarrow> x = xa\<close>
  apply (cases x; cases xa) by auto presburger+

lemma lit_of_natP_nat_of_lit_iff: \<open>lit_of_natP c a \<longleftrightarrow> c = nat_of_lit a\<close>
  by (cases a) (auto simp: lit_of_natP_def)

term \<open>\<lambda>R R'. {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>

definition ann_lit_rel:: "('a \<times> nat) set \<Rightarrow> ('b \<times> nat option) set \<Rightarrow>
    (('a \<times> 'b) \<times> (nat, nat) ann_lit) set" where
  ann_lit_rel_internal_def:
  \<open>ann_lit_rel R R' = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>

type_synonym ann_lit_wl = \<open>nat \<times> nat option\<close>
type_synonym ann_lits_wl = \<open>ann_lit_wl list\<close>
term \<open> \<langle>uint32_nat_rel\<rangle>option_rel\<close>

definition nat_ann_lit_rel :: "(ann_lit_wl \<times> (nat, nat) ann_lit) set" where
  nat_ann_lit_rel_internal_def: \<open>nat_ann_lit_rel = \<langle>nat_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>ann_lit_rel\<close>

lemma ann_lit_rel_def:
  \<open>\<langle>R, R'\<rangle>ann_lit_rel = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>
  unfolding nat_ann_lit_rel_internal_def ann_lit_rel_internal_def relAPP_def ..

lemma nat_ann_lit_rel_def:
  \<open>nat_ann_lit_rel = {(a, b). b = ann_lit_of_pair ((\<lambda>(a,b). (literal_of_nat a, b)) a)}\<close>
  unfolding nat_ann_lit_rel_internal_def ann_lit_rel_def
  apply (auto simp: option_rel_def ex_disj_distrib uint32_nat_rel_def br_def)
   apply (case_tac b)
    apply auto
   apply (case_tac b)
   apply auto
  done

definition nat_ann_lits_rel :: "(ann_lits_wl \<times> (nat, nat) ann_lits) set" where
  \<open>nat_ann_lits_rel = \<langle>nat_ann_lit_rel\<rangle>list_rel\<close>

abbreviation pair_nat_ann_lit_assn :: "(nat, nat) ann_lit \<Rightarrow> ann_lit_wl \<Rightarrow> assn" where
  \<open>pair_nat_ann_lit_assn \<equiv> pure (nat_ann_lit_rel)\<close>

abbreviation pair_nat_ann_lits_assn :: "(nat, nat) ann_lits \<Rightarrow> ann_lits_wl \<Rightarrow> assn" where
  \<open>pair_nat_ann_lits_assn \<equiv> list_assn (pair_nat_ann_lit_assn)\<close>

lemma nat_ann_lits_rel_Cons[iff]:
  \<open>(x # xs, y # ys) \<in> nat_ann_lits_rel \<longleftrightarrow> (x, y) \<in> nat_ann_lit_rel \<and> (xs, ys) \<in> nat_ann_lits_rel\<close>
  by (auto simp: nat_ann_lits_rel_def)

lemma lit_of_natP_same_rightD: \<open>lit_of_natP bi b \<Longrightarrow> lit_of_natP bi a \<Longrightarrow> a = b\<close>
  by (auto simp: p2rel_def lit_of_natP_def)

lemma lit_of_natP_same_leftD: \<open>lit_of_natP bi b \<Longrightarrow> lit_of_natP ai b \<Longrightarrow> ai = bi\<close>
  apply (auto simp: p2rel_def lit_of_natP_def split: if_splits)
  apply presburger
  apply presburger
  done


subsection \<open>Refinement\<close>

text \<open>We start in a context where we have an initial set of literals. \<close>
locale twl_array_code_ops =
  fixes N\<^sub>0 :: \<open>nat list\<close>
begin

text \<open>This is the \<^emph>\<open>completion\<close> of \<^term>\<open>N\<^sub>0\<close>, containing the positive and the negation of every
  literal of \<^term>\<open>N\<^sub>0\<close>:\<close>
definition N\<^sub>0' where \<open>N\<^sub>0' = map literal_of_nat N\<^sub>0\<close>
definition N\<^sub>0'' where \<open>N\<^sub>0'' = mset N\<^sub>0'\<close>

definition N\<^sub>1 where \<open>N\<^sub>1 = N\<^sub>0'' + uminus `# N\<^sub>0''\<close>

definition is_N\<^sub>1 :: "nat literal multiset \<Rightarrow> bool" where
  \<open>is_N\<^sub>1 S \<longleftrightarrow> set_mset S = set_mset N\<^sub>1\<close>

abbreviation literals_are_N\<^sub>0 where
  \<open>literals_are_N\<^sub>0 S \<equiv>
     is_N\<^sub>1 (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S))))\<close>

definition literals_are_in_N\<^sub>0 :: \<open>nat clause \<Rightarrow> bool\<close> where
  \<open>literals_are_in_N\<^sub>0 C \<longleftrightarrow> set_mset (lits_of_atms_of_m C) \<subseteq> set_mset N\<^sub>1\<close>

lemma lits_of_atms_of_m_subset_lits_of_atms_of_mmD:
  \<open>a \<in># b \<Longrightarrow> set_mset (lits_of_atms_of_m a) \<subseteq> set_mset (lits_of_atms_of_mm b)\<close>
  by (auto simp: lits_of_atms_of_m_def lits_of_atms_of_mm_def)

lemma literals_are_in_N\<^sub>0_nth:
  fixes C :: nat
  assumes \<open>C < length N\<close> and \<open>C > 0\<close> and \<open>literals_are_N\<^sub>0 (M, N, U, D', NP, UP, Q, W)\<close>
  shows \<open>literals_are_in_N\<^sub>0 (mset (N!C))\<close>
proof -
  have \<open>(N!C) \<in> set (tl N)\<close>
    using assms(1,2) by (auto intro!: nth_in_set_tl)
  then have \<open>mset (N!C) \<in># cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D', NP, UP, Q, W)))\<close>
    using assms(1,2)
    by (subst (asm) append_take_drop_id[symmetric, of \<open>tl N\<close> U], subst (asm) set_append,
        subst (asm) Un_iff, subst (asm) drop_Suc[symmetric])
      (auto simp: clauses_def mset_take_mset_drop_mset')
  from lits_of_atms_of_m_subset_lits_of_atms_of_mmD[OF this] show ?thesis
    using assms(3) unfolding is_N\<^sub>1_def literals_are_in_N\<^sub>0_def by blast
qed

lemma in_N\<^sub>1_atm_of_in_atms_of_iff: \<open>x \<in># N\<^sub>1 \<longleftrightarrow> atm_of x \<in> atms_of N\<^sub>1\<close>
  by (auto simp: N\<^sub>1_def atms_of_def atm_of_eq_atm_of)

abbreviation D\<^sub>0 :: \<open>(nat \<times> nat literal) set\<close> where
  \<open>D\<^sub>0 \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset N\<^sub>1\<close>

definition length_ll_f where
  \<open>length_ll_f W L = length (W L)\<close>

lemma length_ll_length_ll_f:
  \<open>(uncurry (RETURN oo length_ll), uncurry (RETURN oo length_ll_f)) \<in>
     [\<lambda>(W, L). L \<in> snd ` D\<^sub>0]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r nat_lit_rel) \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding length_ll_def length_ll_f_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def lit_of_natP_def
      nat_lit_rel_def)

abbreviation array_watched_assn :: "(nat literal \<Rightarrow> nat list) \<Rightarrow> (nat array_list) array \<Rightarrow> assn" where
  \<open>array_watched_assn \<equiv> hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)\<close>

lemma ex_list_watched:
  fixes W :: \<open>nat literal \<Rightarrow> nat list\<close>
  shows \<open>\<exists>aa. \<forall>x\<in>#N\<^sub>1. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = W x\<close>
  (is \<open>\<exists>aa. ?P aa\<close>)
proof -
  define D' where \<open>D' = D\<^sub>0\<close>
  define N\<^sub>1' where \<open>N\<^sub>1' = N\<^sub>1\<close>
  define D'' where \<open>D'' = mset_set (snd ` D')\<close>
  let ?f = \<open>(\<lambda>L a. a[nat_of_lit L:= W L])\<close>
  interpret comp_fun_commute ?f
    apply standard
    apply (case_tac \<open>y = x\<close>)
     apply (solves simp)
    apply (intro ext)
    apply (subst (asm) lit_of_nat_nat_of_lit[symmetric])
    apply (subst (asm)(3) lit_of_nat_nat_of_lit[symmetric])
    apply (clarsimp simp only: comp_def intro!: list_update_swap)
    done
  define aa where
    \<open>aa \<equiv> fold_mset ?f (replicate (1+Max (nat_of_lit ` snd ` D')) []) (mset_set (snd ` D'))\<close>
  have length_fold: \<open>length (fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l M) = length l\<close> for l M
    by (induction M) auto
  have length_aa: \<open>length aa = Suc (Max (nat_of_lit ` snd ` D'))\<close>
    unfolding aa_def D''_def[symmetric] by (simp add: length_fold)
  have H: \<open>x \<in># N\<^sub>1 \<Longrightarrow>
      length l \<ge> Suc (Max (nat_of_lit ` set_mset N\<^sub>1)) \<Longrightarrow>
      fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l (remdups_mset N\<^sub>1) ! nat_of_lit x = W x\<close>
    for x l
    unfolding N\<^sub>1'_def[symmetric]
    apply (induction N\<^sub>1' arbitrary: l)
    subgoal by simp
    subgoal for xa Ls l
      apply (case_tac \<open>(nat_of_lit ` set_mset Ls) = {}\<close>)
       apply (solves simp)
      apply (auto simp: less_Suc_eq_le length_fold)
      apply (subst nth_list_update_neq)
       apply (auto simp: less_Suc_eq_le)[]
      apply (auto simp: less_Suc_eq_le)[]
      done
    done
  have H': \<open>aa ! nat_of_lit x = W x\<close> if \<open>x \<in># N\<^sub>1\<close> for x
    using that unfolding aa_def D'_def
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le intro!: H)
  have \<open>?P aa\<close>
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le length_aa H')
  then show ?thesis
    by blast
qed

definition length_aa_u :: \<open>('a::heap array_list) array \<Rightarrow> uint32 \<Rightarrow> nat Heap\<close> where
  \<open>length_aa_u xs i = length_aa xs (nat_of_uint32 i)\<close>

lemma length_aa_u_hnr[sepref_fr_rules]: \<open>(uncurry length_aa_u, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def length_aa_u_def br_def)

lemma length_aa_length_ll_f[sepref_fr_rules]:
  \<open>(uncurry length_aa, uncurry (RETURN oo length_ll_f)) \<in>
   [\<lambda>(W, L). L \<in> snd ` D\<^sub>0]\<^sub>a
     array_watched_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry length_aa, uncurry (RETURN \<circ>\<circ> length_ll_f))
     \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel)
     (\<lambda>(W, L). L \<in> snd ` D\<^sub>0) (\<lambda>_ (xs, i). i < length xs)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     ((arrayO_assn (arl_assn nat_assn))\<^sup>k *\<^sub>a
                      nat_assn\<^sup>k)
                     (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r
                      nat_lit_rel) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_aa_hnr length_ll_length_ll_f] .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    by (fastforce simp: comp_PRE_def prod_rel_def_internal relAPP_def map_fun_rel_def[abs_def]
        p2rel_def lit_of_natP_def literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed

end

text \<open>TODO Move\<close>

lemma list_all2_op_eq_map_right_iff': \<open>list_all2 (\<lambda>L L'. L' = (f L)) a aa \<longleftrightarrow> aa = map f a \<close>
  apply (induction a arbitrary: aa)
   apply (auto; fail)
  by (rename_tac aa, case_tac aa) (auto)

lemma less_upper_bintrunc_id: \<open>n < 2 ^b \<Longrightarrow> n \<ge> 0 \<Longrightarrow> bintrunc b n = n\<close>
  unfolding uint32_of_nat_def
  by (simp add: no_bintr_alt1 semiring_numeral_div_class.mod_less)

locale twl_array_code =
  twl_array_code_ops N\<^sub>0
  for N\<^sub>0 :: \<open>nat list\<close>
begin


lemma list_assn_N\<^sub>0': \<open>list_assn (\<lambda>a c. \<up> ((c, a) \<in> nat_lit_rel)) N\<^sub>0' N\<^sub>0 = emp\<close>
  unfolding  N\<^sub>0'_def
    pure_def[symmetric] list_assn_pure_conv
  by (auto simp: list_rel_def uint32_nat_rel_def br_def pure_def nat_lit_rel_def
        Collect_eq_comp nat_lit_rel_def lit_of_natP_def
      list_all2_op_eq_map_right_iff
      simp del: literal_of_nat.simps )

lemma N_hnr'[sepref_import_param]:
  "(uncurry0 (return N\<^sub>0), uncurry0 (RETURN N\<^sub>0'))\<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn nat_lit_assn"
  by sepref_to_hoare (sep_auto simp: list_assn_N\<^sub>0')

lemma [sepref_import_param]: "(N\<^sub>0, N\<^sub>0) \<in> \<langle>nat_rel\<rangle>list_rel"
  by auto

definition unit_propagation_inner_loop_body_wl_D :: "nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres"  where
  \<open>unit_propagation_inner_loop_body_wl_D K w S = do {
    ASSERT(literals_are_N\<^sub>0 S);
    let (M, N, U, D', NP, UP, Q, W) = S;
    ASSERT(K \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP));
    ASSERT(w < length (watched_by S K));
    ASSERT(K \<in> snd ` D\<^sub>0);
    let C = (W K) ! w;
    ASSERT(C > 0);
    ASSERT(no_dup M);
    ASSERT(C < length N);
    ASSERT(0 < length (N!C));
    let i = (if (N!C) ! 0 = K then 0 else 1);
    ASSERT(i < length (N!C));
    ASSERT(1-i < length (N!C));
    let L = K;
    let L' = (N!C) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    ASSERT(L' \<in> snd ` D\<^sub>0);
    val_L' \<leftarrow> RETURN (valued M L');
    if val_L' = Some True
    then RETURN (w+1, (M, N, U, D', NP, UP, Q, W))
    else do {
      ASSERT(literals_are_in_N\<^sub>0 (mset (N!C)));
      f \<leftarrow> find_unwatched M (N!C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (w+1, (M, N, U, Some (mset (N!C)), NP, UP, {#}, W))}
        else do {
          ASSERT(undefined_lit M L');
          RETURN (w+1, (Propagated L' C # M, N, U, D', NP, UP, add_mset (-L') Q, W))}
      else do {
        ASSERT(snd f < length (N!C));
        let K' = (N!C) ! (snd f);
        ASSERT(K' \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP));
        ASSERT(K' \<in> snd ` D\<^sub>0);
        let N' = list_update N C (swap (N!C) i (snd f));
        let W = W(L := delete_index_and_swap (W L) w);
        let W = W(K':= W K' @ [C]);
        ASSERT(K \<noteq> K');
        RETURN (w, (M, N', U, D', NP, UP, Q, W))
      }
    }
   }
\<close>

lemma mset_tl_update_swap:
  \<open>i < length xs \<Longrightarrow> j < length (xs ! i) \<Longrightarrow> k < length (xs ! i) \<Longrightarrow>
  mset `# mset (tl (xs [i := swap (xs ! i) j k])) = mset `# mset (tl xs)\<close>
  apply (cases i)
  subgoal by (cases xs) auto
  subgoal for i'
    apply (subgoal_tac \<open>(xs ! Suc i') \<in># (mset (tl xs))\<close>)
     defer
     apply (solves \<open>auto simp: nth_in_set_tl\<close>)
    apply (auto simp: tl_update_swap mset_update nth_tl)[]
    by (metis image_mset_add_mset insert_DiffM set_mset_mset)
  done

lemma unit_propagation_inner_loop_body_wl_D_spec:
  assumes
    K: \<open>K \<in> snd ` D\<^sub>0\<close> and
    N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>unit_propagation_inner_loop_body_wl_D K w S \<le>
      \<Down> {((n', T'), (n, T)). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}
        (unit_propagation_inner_loop_body_wl K w S)\<close>
proof -
  obtain M N U D NP UP Q W where
    S: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
    by (cases S)

  have valued: \<open>(valued M L,
     valued M' L') \<in>
    {(val, val'). val = val' \<and>
       val = (if undefined_lit M L then None else if L \<in> lits_of_l M then Some True else Some False)}\<close>
    if \<open>M = M'\<close> and \<open>L = L'\<close>
    for M M' :: \<open>(nat literal, nat literal, nat) annotated_lit list\<close> and L L'
    using that by (auto simp: valued_def)
  have find_unwatched: \<open>find_unwatched M (N ! (W K ! w))
    \<le> \<Down> Id (find_unwatched M' (N' ! (W' K ! w)))\<close>
    if \<open>N=N'\<close> and \<open>M = M'\<close> and \<open>W = W'\<close>
    for N N' :: \<open>nat literal list list\<close> and
      M M' :: \<open>(nat literal, nat literal, nat) annotated_lit list\<close> and W W'
    by (auto simp: that)
  have \<open>mset `# mset (take n (tl xs)) +
    mset `# mset (drop (Suc n) xs) =
    mset `# mset (tl xs)\<close> for n :: nat and xs :: \<open>'a list list\<close>
    unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc
      append_take_drop_id ..
  then have m: \<open>(mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b)) =
         (mset `# mset (tl xs)) + a + b\<close>
    for a b and xs :: \<open>'a list list\<close> and n :: nat
    by auto
  have in_lits_of_atms_S: \<open>N' ! a ! b
    \<in># lits_of_atms_of_mm
         (cdcl\<^sub>W_restart_mset.clauses
           (state\<^sub>W_of (twl_st_of_wl None S)))\<close>
    if \<open>a > 0\<close> and \<open>a < length N\<close> and \<open>b < length (N ! a)\<close> and \<open>N' = N\<close>
    for a b :: nat and N'
  proof -
    have \<open>atm_of (N ! a ! b) \<in> atms_of_ms (mset ` set (tl N))\<close>
    using that by (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff clauses_def S mset_take_mset_drop_mset
        atms_of_ms_def drop_Suc atms_of_def nth_in_set_tl intro!: bexI[of _ \<open>N!a\<close>] )
    then show ?thesis
      using that
      by (simp add: S clauses_def mset_take_mset_drop_mset' m in_lits_of_atms_of_mm_ain_atms_of_iff)
  qed
  show ?thesis
    unfolding unit_propagation_inner_loop_body_wl_D_def unit_propagation_inner_loop_body_wl_def S
      watched_by.simps
    supply [[goals_limit=1]]
    apply (refine_vcg valued find_unwatched)
    subgoal using assms unfolding S by fast
    subgoal by simp
    subgoal using K .
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal for M'' x2 N'' x2a U'' x2b D'' x2c NP'' x2d UP'' x2e WS'' Q'' M' x2g
      N' x2h U' x2i D' x2j NP' x2k UP' x2l WS' Q'
      apply (subgoal_tac \<open>N' ! (Q' K ! w) ! (1 - (if N' ! (Q' K ! w) ! 0 = K then 0 else 1)) \<in>#
        lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S)))\<close>)
      subgoal using eq_commute[THEN iffD1, OF N\<^sub>0[unfolded is_N\<^sub>1_def]]
        by (auto simp: image_image S clauses_def mset_take_mset_drop_mset' m is_N\<^sub>1_def
            lits_of_atms_of_mm_union)[]
      subgoal
        by (rule in_lits_of_atms_S) auto
      done
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m)
    subgoal by (rule literals_are_in_N\<^sub>0_nth) fast+
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m)
    subgoal by (auto split: if_splits)
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m)
    subgoal by simp
    subgoal by simp
    subgoal
      using N\<^sub>0 unfolding S
      by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
          clauses_def image_image m lits_of_atms_of_mm_union is_N\<^sub>1_def)
    subgoal by simp
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m mset_tl_update_swap)
    done
qed

lemma
  shows unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry2 unit_propagation_inner_loop_body_wl_D, uncurry2 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>((K, w), S). literals_are_N\<^sub>0 S \<and> K \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r {(T', T).
       T = T' \<and> literals_are_N\<^sub>0 T}\<rangle> nres_rel\<close> (is \<open>?G1\<close>) and
  unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D_weak:
   \<open>(uncurry2 unit_propagation_inner_loop_body_wl_D, uncurry2 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>((K, w), S). literals_are_N\<^sub>0 S \<and> K \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
   (is \<open>?G2\<close>)
proof -
  have 1: \<open>nat_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} =
     {((n', T'), n, T). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}\<close>
    by auto
  show ?G1
    unfolding fref_def 1 by (auto simp add: nres_rel_def uncurry_def simp del: twl_st_of_wl.simps
        intro!: unit_propagation_inner_loop_body_wl_D_spec)
  moreover have \<open> \<langle>nat_rel \<times>\<^sub>r
              {(T', T).
               T = T' \<and>
               is_N\<^sub>1
                (lits_of_atms_of_mm
                  (cdcl\<^sub>W_restart_mset.clauses
                    (state\<^sub>W_of
                      (twl_st_of None (st_l_of_wl None T)))))}\<rangle>nres_rel \<subseteq> \<langle>Id\<rangle> nres_rel\<close>
    (is \<open>\<langle>?R\<rangle> nres_rel \<subseteq> _\<close>)
    using "weaken_\<Down>"[of ?R Id]
    by (auto simp: nres_rel_def prod_rel_def)
  ultimately show ?G2
    unfolding fref_def by (auto 11 0)
qed

definition unit_propagation_inner_loop_wl_loop_D :: "nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres" where
  \<open>unit_propagation_inner_loop_wl_loop_D L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(w, S). twl_struct_invs (twl_st_of_wl (Some (L, w)) S) \<and>
        twl_stgy_invs (twl_st_of_wl (Some (L, w)) S) \<and>
         additional_WS_invs (st_l_of_wl (Some (L, w)) S) \<and>
        correct_watching S \<and> w \<le> length (watched_by S L) \<and>
        literals_are_N\<^sub>0 S \<and> L \<in> snd ` D\<^sub>0\<^esup>
      (\<lambda>(w, (M, N, U, D, NP, UP, Q, W)). w < length (W L) \<and> D = None)
      (\<lambda>(w, S). do {
        unit_propagation_inner_loop_body_wl_D L w S
      })
      (0, S\<^sub>0)
  }
  \<close>

lemma unit_propagation_inner_loop_wl_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and K: \<open>K \<in> snd ` local.D\<^sub>0\<close>
  shows \<open>unit_propagation_inner_loop_wl_loop_D K S \<le>
     \<Down> {((n', T'), n, T). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}
       (unit_propagation_inner_loop_wl_loop K S)\<close>
proof -
  have u: \<open>unit_propagation_inner_loop_body_wl_D K w S \<le>
         \<Down> {((n', T'), n, T). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}
           (unit_propagation_inner_loop_body_wl K' w' S')\<close>
  if \<open>K \<in> snd ` local.D\<^sub>0\<close> and \<open>literals_are_N\<^sub>0 S\<close> and
    \<open>K = K'\<close> and \<open>w = w'\<close> and \<open>S = S'\<close> for S S' and w w' and K K'
    using unit_propagation_inner_loop_body_wl_D_spec[of K S w] that by auto
  have \<open>mset `# mset (take n (tl xs)) + mset `# mset (drop (Suc n) xs) = mset `# mset (tl xs)\<close>
    for n :: nat and xs :: \<open>'a list list\<close>
    unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc
      append_take_drop_id ..
  then have m: \<open>(mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b)) =
         (mset `# mset (tl xs)) + a + b\<close>
    for a b and xs :: \<open>'a list list\<close> and n :: nat
    by auto

  show ?thesis
    unfolding unit_propagation_inner_loop_wl_loop_D_def unit_propagation_inner_loop_wl_loop_def
    apply (refine_vcg u)
    subgoal using N\<^sub>0 by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using K by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition unit_propagation_inner_loop_wl_D :: "nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>unit_propagation_inner_loop_wl_D L S\<^sub>0 = do {
     wS \<leftarrow> unit_propagation_inner_loop_wl_loop_D L S\<^sub>0;
     RETURN (snd wS)
  }\<close>

lemma unit_propagation_inner_loop_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and K: \<open>K \<in> snd ` local.D\<^sub>0\<close>
  shows \<open>unit_propagation_inner_loop_wl_D K S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (unit_propagation_inner_loop_wl K S)\<close>
proof -
  show ?thesis
    unfolding unit_propagation_inner_loop_wl_D_def unit_propagation_inner_loop_wl_def
    apply (refine_vcg unit_propagation_inner_loop_wl_spec)
    subgoal using N\<^sub>0 .
    subgoal using K .
    subgoal by auto
    done
qed

definition unit_propagation_outer_loop_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>unit_propagation_outer_loop_wl_D S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      correct_watching S \<and> additional_WS_invs (st_l_of_wl None S)\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S))));
        unit_propagation_inner_loop_wl_D L S'
      })
      (S\<^sub>0 :: nat twl_st_wl)\<close>

lemma unit_propagation_outer_loop_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>unit_propagation_outer_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (unit_propagation_outer_loop_wl S)\<close>
proof -
  have select: \<open>select_and_remove_from_literals_to_update_wl S \<le>
    \<Down> {((T', L'), (T, L)). T = T' \<and> L = L' \<and>  T = set_literals_to_update_wl (literals_to_update_wl S - {#L#}) S}
       (select_and_remove_from_literals_to_update_wl S')\<close>
    if \<open>S = S'\<close> for S S' :: \<open>nat twl_st_wl\<close>
    unfolding select_and_remove_from_literals_to_update_wl_def select_and_remove_from_literals_to_update_def
    apply (rule RES_refine)
    using that unfolding select_and_remove_from_literals_to_update_wl_def by blast
  have unit_prop: \<open>literals_are_N\<^sub>0 S \<Longrightarrow>
          K \<in> snd ` D\<^sub>0 \<Longrightarrow>
          unit_propagation_inner_loop_wl_D K S
          \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} (unit_propagation_inner_loop_wl K' S')\<close>
    if \<open>K = K'\<close> and \<open>S = S'\<close> for K K' and S S' :: \<open>nat twl_st_wl\<close>
    unfolding that by (rule unit_propagation_inner_loop_wl_D_spec)
  show ?thesis
    unfolding unit_propagation_outer_loop_wl_D_def unit_propagation_outer_loop_wl_def
    apply (refine_vcg select unit_prop)
    subgoal using N\<^sub>0 by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S T'L' TL T' L' T L by (cases S') auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S T'L' TL T' L' T L using N\<^sub>0 by (cases S') auto
    subgoal by (auto simp: is_N\<^sub>1_def)
    done
qed


definition skip_and_resolve_loop_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>skip_and_resolve_loop_wl_D S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (H, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S).
           skip_and_resolve_loop_inv (twl_st_of_wl None S\<^sub>0) (brk, twl_st_of_wl None S) \<and>
           additional_WS_invs (st_l_of_wl None S) \<and> correct_watching S \<and> literals_are_N\<^sub>0 S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, Q, W) = S in
          do {
            ASSERT(M \<noteq> []);
            ASSERT(get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None);
            let D' = the (get_conflict_wl (M, N, U, D, NP, UP, Q, W));
            ASSERT(is_proped (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W))));
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)));
            ASSERT(C < length N);
            ASSERT(literals_are_in_N\<^sub>0 D');
            ASSERT(\<forall>L\<in># D'. defined_lit M L);
            if -L \<notin># D' then
              do {RETURN (False, (tl M, N, U, Some D', NP, UP, Q, W))}
            else do {
              if get_maximum_level M (remove1_mset (-L) D') = count_decided M
              then do {
                let E = remove1_mset (-L) D';
                ASSERT(C > 0 \<longrightarrow> N!C \<noteq> []);
                let F = (if C = 0 then {#} else (remove1_mset L (mset (N!C))));
                ASSERT(distinct_mset F);
                ASSERT(distinct_mset E);
                let G = E \<union># F;
                RETURN (G = {#}, (tl M, N, U, Some G, NP, UP, Q, W))}
              else
                do {RETURN (True, (M, N, U, Some D', NP, UP, Q, W))}
          }}
        )
        (get_conflict_wl S\<^sub>0 = Some {#}, S\<^sub>0);
      RETURN S
    }
  \<close>

context
begin
text \<open>Auxiliary definition: it helps to prove refinements. Once the \<^term>\<open>RETURN\<close> is removed,
  the invariants form the \<^term>\<open>WHILE\<close>--loop are not dropped.\<close>
private definition skip_and_resolve_loop_wl_D' :: "nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres" where
  \<open>skip_and_resolve_loop_wl_D' S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, S).
           skip_and_resolve_loop_inv (twl_st_of_wl None S\<^sub>0) (brk, twl_st_of_wl None S) \<and>
           additional_WS_invs (st_l_of_wl None S) \<and> correct_watching S \<and> literals_are_N\<^sub>0 S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, Q, W) = S in
          do {
            ASSERT(M \<noteq> []);
            ASSERT(get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None);
            let D' = the (get_conflict_wl (M, N, U, D, NP, UP, Q, W));
            ASSERT(is_proped (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W))));
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)));
            ASSERT(C < length N);
            ASSERT(literals_are_in_N\<^sub>0 D');
            ASSERT(\<forall>L\<in># D'. defined_lit M L);
            if -L \<notin># D' then
              do {RETURN (False, (tl M, N, U, Some D', NP, UP, Q, W))}
            else
              if get_maximum_level M (remove1_mset (-L) D') = count_decided M
              then do {
                ASSERT(C > 0 \<longrightarrow> N!C \<noteq> []);
                ASSERT(distinct_mset (if C = 0 then {#} else mset (remove1 L (N!C))));
                ASSERT(distinct_mset (remove1_mset (-L) D'));
                RETURN (remove1_mset (-L) D' \<union># (if C = 0 then {#} else mset (remove1 L (N!C))) = {#},
                   (tl M, N, U, Some (remove1_mset (-L) D' \<union># (if C = 0 then {#} else mset (remove1 L (N!C)))),
                     NP, UP, Q, W))}
              else
                do {RETURN (True, (M, N, U, Some D', NP, UP, Q, W))}
          }
        )
        (get_conflict_wl S\<^sub>0 = Some {#}, S\<^sub>0);
     RETURN S
    }
  \<close>

lemma twl_struct_invs_is_N\<^sub>1_clauses_init_clss:
  fixes S\<^sub>0 :: \<open>nat twl_st_wl\<close>
  defines \<open>S \<equiv> twl_st_of_wl None S\<^sub>0\<close>
  defines \<open>clss \<equiv> (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of S)))\<close>
  defines \<open>init \<equiv> (lits_of_atms_of_mm (init_clss (state\<^sub>W_of S)))\<close>
  assumes invs: \<open>twl_struct_invs (twl_st_of_wl None S\<^sub>0)\<close>
  shows \<open>is_N\<^sub>1 clss \<longleftrightarrow> is_N\<^sub>1 init\<close>
proof -

  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S)\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S_def
    by fast
  then have
    \<open>set_mset clss = set_mset init\<close>
    unfolding clss_def init_def S_def
    by (cases S\<^sub>0) (auto simp: clauses_def mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state
        cdcl\<^sub>W_restart_mset.no_strange_atm_def in_lits_of_atms_of_mm_ain_atms_of_iff)
  then show \<open>is_N\<^sub>1 clss \<longleftrightarrow> is_N\<^sub>1 init\<close>
    unfolding is_N\<^sub>1_def by blast
qed

lemma cdcl_twl_o_literals_are_N\<^sub>0_invs:
  fixes S :: \<open>nat twl_st_wl\<close>
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<^sub>0\<close> and
    cdcl: \<open>cdcl_twl_o\<^sup>*\<^sup>* (twl_st_of_wl None S\<^sub>0) (twl_st_of_wl None T)\<close> and
    invs: \<open>twl_struct_invs (twl_st_of_wl None S\<^sub>0)\<close>
  shows \<open>literals_are_N\<^sub>0 T\<close>
proof -
  let ?S = \<open>twl_st_of_wl None S\<^sub>0\<close> and ?T = \<open>twl_st_of_wl None T\<close>
  have cdcl_stgy: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of ?S) (state\<^sub>W_of ?T)\<close>
    apply (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy)
    subgoal using rtranclp_cdcl_twl_o_stgyD[OF cdcl] .
    subgoal using invs .
    done
  have init: \<open>init_clss (state\<^sub>W_of ?S) = init_clss (state\<^sub>W_of ?T)\<close>
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_init_clss)
    using cdcl_stgy by (blast dest: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  have invs_T: \<open>twl_struct_invs (twl_st_of_wl None T)\<close>
    using cdcl invs rtranclp_cdcl_twl_o_stgyD rtranclp_cdcl_twl_stgy_twl_struct_invs by blast
  show ?thesis
    using N\<^sub>0
    unfolding twl_struct_invs_is_N\<^sub>1_clauses_init_clss[of S\<^sub>0, OF invs]
      twl_struct_invs_is_N\<^sub>1_clauses_init_clss[of T, OF invs_T] init[symmetric]
    .
qed

lemma set_mset_set_mset_eq_iff: \<open>set_mset A = set_mset B \<longleftrightarrow> (\<forall>a\<in>#A. a \<in># B) \<and> (\<forall>a\<in>#B. a \<in># A)\<close>
  by blast

lemma is_N\<^sub>1_alt_def: \<open>is_N\<^sub>1 (lits_of_atms_of_mm A) \<longleftrightarrow> atms_of_mm A = atms_of N\<^sub>1\<close>
  unfolding set_mset_set_mset_eq_iff is_N\<^sub>1_def Ball_def in_N\<^sub>1_atm_of_in_atms_of_iff
    in_lits_of_atms_of_mm_ain_atms_of_iff
    by auto (metis literal.sel(2))+

lemma skip_and_resolve_loop_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close>
  shows \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto
  have D'\<^sub>1: \<open>skip_and_resolve_loop_wl_D' S \<le> \<Down> {((b, T'), T). T' = T} (skip_and_resolve_loop_wl S)\<close>
    unfolding skip_and_resolve_loop_wl_D'_def skip_and_resolve_loop_wl_def
    apply (refine_vcg 1)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for brk'S' brkS brk' S'
      by (rule cdcl_twl_o_literals_are_N\<^sub>0_invs[of S])
        (use N\<^sub>0 in \<open>auto simp: skip_and_resolve_loop_inv_def\<close>)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for brk'S' brkS brk S brk' S' M x2b N x2c U x2d D x2e NP x2f UP x2g WS
       Q M' x2i N' x2j U' x2k D' x2l NP' x2m UP' x2n WS' Q' L C L' C'
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>)
      subgoal
        apply clarify
        apply (subst (asm) twl_struct_invs_is_N\<^sub>1_clauses_init_clss)
         apply (solves \<open>simp add: skip_and_resolve_loop_inv_def\<close>)
        by (fastforce simp add: literals_are_in_N\<^sub>0_def is_N\<^sub>1_alt_def
            cdcl\<^sub>W_restart_mset.no_strange_atm_def in_N\<^sub>1_atm_of_in_atms_of_iff
            cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset' atms_of_def
            in_lits_of_atms_of_m_ain_atms_of_iff atm_of_eq_atm_of)
      subgoal
        apply (subst (asm) skip_and_resolve_loop_inv_def)
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by force
      done
    subgoal for brk'S' brkS brk S brk' S' M x2b N x2c U x2d D x2e NP x2f UP x2g WS
       Q M' x2i N' x2j U' x2k D' x2l NP' x2m UP' x2n WS' Q' L C L' C'
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close>)
      subgoal
        by (auto simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
            cdcl\<^sub>W_restart_mset_state dest!: true_annots_CNot_definedD)
      subgoal
        apply (subst (asm) skip_and_resolve_loop_inv_def)
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by force
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g
       x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
       x2p x1q x2q
       apply (subgoal_tac \<open>Multiset.Ball
         {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x))
         . x \<in># mset (tl x1c)#}
         struct_wf_twl_cls\<close>)
      subgoal
        apply (subgoal_tac \<open>x1j ! x2q \<in> set (tl x1c)\<close>)
         apply (solves \<open>auto\<close>)
        apply (cases x1b; cases \<open>hd x1b\<close>)
        by (auto intro!: nth_in_set_tl simp: additional_WS_invs_def all_conj_distrib)
      subgoal
        apply (simp del: struct_wf_twl_cls.simps)
        apply (subst (asm)(1) skip_and_resolve_loop_inv_def)
        apply (subst (asm) twl_struct_invs_def)
        apply (simp del: struct_wf_twl_cls.simps)
        apply (subst (asm) twl_st_inv.simps)
        apply (subst (asm) image_mset_union[symmetric])
        apply (subst (asm) mset_take_mset_drop_mset')
        apply (subst (asm) mset_append[symmetric])
        apply (subst (asm)(2) drop_Suc)
        apply (subst (asm) append_take_drop_id)
        apply (simp del: struct_wf_twl_cls.simps)
        done
      done
    subgoal for brk'S' brkS brk S brk' S' M x2b N x2c U x2d D x2e NP x2f UP x2g WS
       Q M' x2i N' x2j U' x2k D' x2l NP' x2m UP' x2n WS' Q' L C L' C'
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close>)
      subgoal
        by (cases M; cases \<open>hd M\<close>) (auto simp add: clauses_def
            cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset')
      subgoal
        apply (subst (asm) skip_and_resolve_loop_inv_def)
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by force
      done
    subgoal for brk'S' brkS brk S brk' S' M x2b N x2c U x2d D x2e NP x2f UP x2g WS
       Q M' x2i N' x2j U' x2k D' x2l NP' x2m UP' x2n WS' Q' L C L' C'
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close>)
      subgoal
        by (cases M; cases \<open>hd M\<close>) (auto simp add: clauses_def
            cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset')
      subgoal
        apply (subst (asm) skip_and_resolve_loop_inv_def)
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by force
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  have H: \<open>do {S \<leftarrow> H; RETURN S} = H\<close> for H :: \<open>'a nres\<close>
    by simp
  have D'\<^sub>2: \<open>skip_and_resolve_loop_wl_D' S \<le>
     \<Down> {((b', T'), (b, T)). b = b' \<and> T' = T \<and> literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl_D' S)\<close>
    unfolding H skip_and_resolve_loop_wl_D'_def
    apply (refine_vcg 1)
    subgoal by auto
    subgoal for b'T' bT b' T' by auto
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
    subgoal by (auto simp: mset_take_mset_drop_mset' clauses_def)
    subgoal by auto
    subgoal by (auto simp: clauses_def)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: mset_take_mset_drop_mset' clauses_def)
    subgoal by auto
    done
  have S: \<open>({((b', T'), b, T). b = b' \<and> T' = T \<and> local.literals_are_N\<^sub>0 T} O Collect (case_prod (\<lambda>(b, y). op = y)))
   = {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T}\<close>
    by auto
  have D'\<^sub>3: \<open>local.skip_and_resolve_loop_wl_D' S \<le> \<Down> {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl S)\<close>
    using conc_trans[OF D'\<^sub>2 D'\<^sub>1] unfolding conc_fun_chain S .
  have D'\<^sub>4: \<open>skip_and_resolve_loop_wl_D S \<le> \<Down> {(T, (b, T')). T' = T} (skip_and_resolve_loop_wl_D' S)\<close>
    unfolding skip_and_resolve_loop_wl_D_def skip_and_resolve_loop_wl_D'_def COPY_def
    op_list_copy_def
    apply (rewrite at \<open>let _ = remove1_mset _ _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = If _ _ _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = _ \<union># _ in _\<close> Let_def)
    apply (rewrite mset_remove1[symmetric])+
    by refine_vcg auto
  have S: \<open>{(T, b, T'). T' = T} O {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T} =
     {(T', T). T = T' \<and> local.literals_are_N\<^sub>0 T}\<close>
    by auto
  show ?thesis
    using conc_trans[OF D'\<^sub>4 D'\<^sub>3] unfolding conc_fun_chain S .
qed

end

definition find_lit_of_max_level_wl' :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
   nat literal nres" where
  \<open>find_lit_of_max_level_wl' M N U D NP UP Q W L =
     find_lit_of_max_level_wl (M, N, U, Some D, NP, UP, Q, W) L\<close>

definition (in -) list_of_mset2 :: "nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause \<Rightarrow> nat clause_l nres" where
  \<open>list_of_mset2 L L' D =
    SPEC (\<lambda>E. mset E = D \<and> E!0 = L \<and> E!1 = L')\<close>

definition (in -) single_of_mset where
  \<open>single_of_mset D = SPEC(\<lambda>L. D = mset [L])\<close>

definition backtrack_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>backtrack_wl_D S\<^sub>0 =
   do {
      let (M, N, U, D, NP, UP, Q, W) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(get_level M L = count_decided M);
        ASSERT(D \<noteq> None);
        ASSERT(D \<noteq> Some {#});
        ASSERT(ex_decomp_of_max_lvl M D L);
        ASSERT(-L \<in># the D);
        ASSERT(twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        let E = the D;
        ASSERT(literals_are_in_N\<^sub>0 E);
        ASSERT(\<forall>L\<in># E. defined_lit M L);
        M1 \<leftarrow> find_decomp_wl (M, N, U, Some E, NP, UP, Q, W) L;

        if size E > 1
        then do {
          ASSERT(\<forall>L' \<in># the D - {#-L#}. get_level M L' = get_level M1 L');
          ASSERT(\<exists>L' \<in># the D - {#-L#}. get_level M L' = get_maximum_level M (the D - {#-L#}));
          ASSERT(\<exists>L' \<in># the D - {#-L#}. get_level M1 L' = get_maximum_level M1 (the D - {#-L#}));
          ASSERT(get_level M L > get_maximum_level M (the D - {#-L#}));
          ASSERT(distinct_mset E);
          L' \<leftarrow> find_lit_of_max_level_wl' M1 N U E NP UP Q W L;
          ASSERT(L \<noteq> -L');
          ASSERT(-L \<in># E);
          ASSERT(L' \<in># E);
          let K = -L;
          D' \<leftarrow> list_of_mset2 K L' E;
          ASSERT(atm_of L \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(atm_of L' \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(-L \<in> snd ` D\<^sub>0);
          ASSERT(L' \<in> snd ` D\<^sub>0);
          ASSERT(undefined_lit M1 (-L));
          let W = W(L':= W L' @ [length N]);
          let W = W(-L:= W (-L) @ [length N]);
          RETURN (Propagated (-L) (length N) # M1, N @ [array_of_arl D'], U,
            None, NP, UP, {#L#}, W)
        }
        else do {
          D' \<leftarrow> single_of_mset E;
          ASSERT(undefined_lit M1 (-L));
          ASSERT(-L \<in> snd ` D\<^sub>0);
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset {#D'#} UP, add_mset L {#}, W)
        }
      }
    }
  \<close>

text \<open>TODO: already present several times\<close>
lemma in_N\<^sub>1_iff: \<open>L \<in># N\<^sub>1 \<longleftrightarrow> atm_of L \<in> atms_of N\<^sub>1\<close>
  by (auto simp: N\<^sub>1_def atms_of_def atm_of_eq_atm_of)

lemma backtrack_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (backtrack_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto
  have 2: \<open>find_decomp_wl S L \<le> \<Down> {(M1, M1'). M1 = M1' \<and>
        (\<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_wl S)))} (find_decomp_wl S' L')\<close>
    if \<open>S = S'\<close> and \<open>L = L'\<close>
    for S S' :: \<open>nat twl_st_wl\<close> and L L'
    using that by (cases S) (fastforce simp: find_decomp_wl_def intro!: SPEC_refine)
  have 3: \<open>find_lit_of_max_level_wl S M \<le>
   \<Down> {(L', L). L' \<in># remove1_mset (-M) (the (get_conflict_wl S)) \<and> L' = L} (find_lit_of_max_level_wl S' M')\<close>
    if \<open>S = S'\<close> and \<open>M = M'\<close>
    for S S' :: \<open>nat twl_st_wl\<close> and M M'
    using that by (cases S; cases S') (auto simp: find_lit_of_max_level_wl_def intro!: RES_refine)
  have H: \<open>mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b) =
   mset `# mset (tl xs) + a + b\<close> for n and xs :: \<open>'a list list\<close> and a b
    apply (subst (2) append_take_drop_id[of n \<open>tl xs\<close>, symmetric])
    apply (subst mset_append)
    by (auto simp: drop_Suc)
  have N\<^sub>1: \<open>set_mset (lits_of_atms_of_mm N) = set_mset N\<^sub>1 \<longleftrightarrow> atms_of_mm N = atms_of N\<^sub>1\<close> for N
    apply (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff atms_of_ms_def atms_of_def
        atm_of_eq_atm_of N\<^sub>1_def in_implies_atm_of_on_atms_of_ms
        image_Un)
    using in_implies_atm_of_on_atms_of_ms in_lits_of_atms_of_mm_ain_atms_of_iff by fastforce
  have list_of_mset: \<open>list_of_mset2 L L' D \<le>
      \<Down> {(E, F). F = [L, L'] @ remove1 L (remove1 L' E) \<and> D = mset E \<and> E!0 = L \<and> E!1 = L' \<and> E=F}
        (list_of_mset D')\<close>
    if \<open>D = D'\<close> and uL_D: \<open>L \<in># D\<close> and L'_D: \<open>L' \<in># D\<close> and L_uL': \<open>L \<noteq> L'\<close> for D D' L L'
    unfolding list_of_mset_def list_of_mset2_def
  proof (rule RES_refine)
    fix s
    assume s: \<open>s \<in> {E. mset E = D \<and> E ! 0 = L \<and> E ! 1 = L'}\<close>
    then show \<open>\<exists>s'\<in>{D'a. D' = mset D'a}.
            (s, s')
            \<in> {(E, F).
                F = [L, L'] @ remove1 L (remove1 L' E) \<and> D = mset E \<and> E ! 0 = L \<and> E ! 1 = L'\<and> E=F}\<close>
      apply (cases s; cases \<open>tl s\<close>)
      using that by (auto simp: diff_single_eq_union diff_diff_add_mset[symmetric]
          simp del: diff_diff_add_mset)
  qed
  have single_of_mset: \<open>single_of_mset D \<le> \<Down> {(L, E). E = [L] \<and> D = mset E} (list_of_mset D')\<close>
    if \<open>D = D'\<close> for D D' :: \<open>'a clause\<close>
    using that by (auto simp: single_of_mset_def list_of_mset_def intro!: RES_refine)
  show ?thesis
    unfolding backtrack_wl_D_def backtrack_wl_def find_lit_of_max_level_wl'_def
      array_of_arl_def
    apply (rewrite at \<open>let _ = the _ in _\<close> Let_def)+
    apply (rewrite at \<open>let _ = - _ in _\<close> Let_def)+
    supply [[goals_limit=1]]
    apply (refine_vcg 1 2 3 list_of_mset single_of_mset)
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None
        (x1, x1a, x1b, x1c, x1d, x1e, x1f, x2f)))\<close>)
      subgoal using N\<^sub>0
        apply clarify
        apply (subst (asm) twl_struct_invs_is_N\<^sub>1_clauses_init_clss)
         apply (solves \<open>simp\<close>)
        by (fastforce simp add: literals_are_in_N\<^sub>0_def is_N\<^sub>1_alt_def
            cdcl\<^sub>W_restart_mset.no_strange_atm_def in_N\<^sub>1_atm_of_in_atms_of_iff
            cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset' atms_of_def
            in_lits_of_atms_of_m_ain_atms_of_iff atm_of_eq_atm_of)
      subgoal
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by force
      done
    subgoal premises p for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (x1, x1a, x1b, x1c, x1d, x1e, x1f, x2f)))\<close>)
      subgoal
        using N\<^sub>0 p(1-18)
        by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
            dest!: true_annots_CNot_definedD)
      subgoal
        using p
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal premises p for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f M x2g x1h x2h x1i x2i x1j x2j x1k x2k
       x1l x2l x1m x2m M1 M1a
    proof -
      have \<open>get_level M `# remove1_mset (- lit_of (hd M)) (the x1j) =
         get_level M1 `# remove1_mset (- lit_of (hd M)) (the x1j)\<close>
        by (rule image_mset_cong) (use p(43) in auto)
      then have \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the x1j))=
          get_maximum_level M1 (remove1_mset (- lit_of (hd M)) (the x1j))\<close>
        unfolding get_maximum_level_def by simp
      then show ?thesis
        using p(37, 40-42) p(1-14) by auto
    qed
    subgoal by auto
    subgoal premises p for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m M1 M1a
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None (x1, x1a, x1b, x1c, x1d, x1e, x1f, x2f)))\<close>)
      subgoal
        using N\<^sub>0 p(1-18)
        by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset_state)
      subgoal
        using p
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      done

    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest: in_diffD)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k
      x1l x2l x1m x2m M1 M1a L' L'a
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state
         (state\<^sub>W_of (twl_st_of_wl None (x1, x1a, x1b, x1c, x1d, x1e, x1f, x2f)))\<close>)
      subgoal premises p
        using p(48-) p(1-19)
        by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset_state
            dest: in_diffD)
      subgoal
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      done
    subgoal by auto
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M1 M1a L' L'a
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M1, N, U, D, NP, UP, WS, W)))\<close>)
      subgoal
        using N\<^sub>0 p(54) p(33) p(1-16)
        apply (cases M1; cases \<open>hd M1\<close>)
         apply fast
         apply fast
        by (simp_all add: twl_struct_invs_is_N\<^sub>1_clauses_init_clss mset_take_mset_drop_mset'
            image_image cdcl\<^sub>W_restart_mset_state clauses_def H in_N\<^sub>1_iff)
      subgoal
        using p
       apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
       apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
       by fast
      done
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M1 M1a N' L'a L''
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>)
      subgoal
        using N\<^sub>0 p(33) p(1-18) p(48)
        apply (auto simp add: (* is_N\<^sub>1_def *) in_lits_of_atms_of_mm_ain_atms_of_iff mset_take_mset_drop_mset'
            clauses_def H (* N\<^sub>1 *) image_image cdcl\<^sub>W_restart_mset.no_strange_atm_def
            cdcl\<^sub>W_restart_mset_state eq_commute[of _ \<open>atms_of N\<^sub>1\<close>] in_N\<^sub>1_iff is_N\<^sub>1_def
             dest!: in_diffD)
        by (metis Un_iff atms_of_ms_union p(55) set_image_mset set_mset_mset set_mset_union)
      subgoal
        using p
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      done
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M1 M1a L' L'a
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>)
      subgoal
        using N\<^sub>0 p(54) p(33) p(1-18) p(47)
        by (auto simp: (* is_N\<^sub>1_def *) in_lits_of_atms_of_mm_ain_atms_of_iff mset_take_mset_drop_mset'
            clauses_def H (* N\<^sub>1 *) image_image cdcl\<^sub>W_restart_mset.no_strange_atm_def
            cdcl\<^sub>W_restart_mset_state eq_commute[of _ \<open>atms_of N\<^sub>1\<close>] in_N\<^sub>1_iff is_N\<^sub>1_def
            dest!: in_diffD)
      subgoal
        using p
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      done
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M1 M1a L' L'a
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>)
      subgoal
        using N\<^sub>0 p(33) p(1-18) p(48) p(55)
        by (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff mset_take_mset_drop_mset'
            clauses_def H image_image cdcl\<^sub>W_restart_mset.no_strange_atm_def
            cdcl\<^sub>W_restart_mset_state eq_commute[of _ \<open>atms_of N\<^sub>1\<close>] in_N\<^sub>1_iff is_N\<^sub>1_def
            dest!: in_diffD)
      subgoal
        using p
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      done
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M' SN' N'
      SU' U' SD' D' SNP' NP' SUP' UP' SWS' WS' W' M''' M'' L L' E E'
    proof -
      note M'''_M'' = p(37)
      then obtain K c M2 where M': \<open>M' = c @ M2 @ Decided K # M'''\<close>
        by (clarsimp_all dest!: get_all_ann_decomposition_exists_prepend)
      define F where \<open>F = c @ M2\<close>
      have \<open>M' = F @ Decided K # M'''\<close>
        using M' F_def by auto
      moreover have \<open>no_dup (trail (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W))))\<close>
        using p(23) unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by fast
      ultimately show ?thesis
        using p(1-16) by (cases M'; cases F) (clarsimp_all simp: cdcl\<^sub>W_restart_mset_state)
    qed
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M' SN' N'
      SU' U' SD' D' SNP' NP' SUP' UP' SWS' WS' W' M''' M'' L L' E E'
    proof -
      thm p
      note SWS = p(1) and SUP = p(2) and SNP = p(3) and SD = p(4) and SU = p(5) and SN = p(6) and
        S = p(7) and M_not_Nil = p(15) and lvl_count_decided = p(10) and D_not_None = p(18) and
        D_not_Some_Nil = p(19) and ex_decomp = p(20) and stgy_invs = p(21) and struct_invs = p(23)
        and no_skip = p(32) and M1_M1a = p(37) and L'_La = p(48) and hd_uL' = p(49) and uhd_D' = p(50)
        and L'_D' = p(52) and EE' = p(53) and atm_hd = p(54) and atm_L = p(55) and S_expand = p(1-14)
        thm p(35-40)
      have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>
        using struct_invs
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      have EE'': \<open>(E, E') \<in> {(E, F).
        F = [- lit_of (hd M'), L] @ remove1 (- lit_of (hd M')) (remove1 L E) \<and>
        the D' = mset E \<and> E ! 0 = - lit_of (hd M') \<and> E ! 1 = L}\<close> and E_E': \<open>E = E'\<close> and
        E_add_remove: \<open>E = [- lit_of (hd M'), L] @ remove1 (- lit_of (hd M')) (remove1 L E)\<close>
        using EE' by blast+
      have \<open>- lit_of (hd M') \<in># mset E\<close> \<open>L \<in># mset E\<close>
        by (subst E_add_remove; use EE'' in auto)+
      then have mset_E_D': \<open>mset E = the D'\<close>
        apply (subst E_add_remove)
        using L'_D' uhd_D' hd_uL' EE'' L'_D' apply auto -- \<open>TODO proof\<close>
        by (smt Clausal_Logic.uminus_lit_swap \<open>- lit_of (hd M') \<in># mset E\<close> \<open>L \<in># mset E\<close>
            add_mset_diff_bothsides add_mset_eq_add_mset_ne insert_DiffM)
      have \<open>length E' \<ge> 2\<close>
        using EE'' L'_D' uhd_D' hd_uL' by (cases E'; cases \<open>tl E'\<close>) simp_all
      then have E': \<open>E!0 # E!1 # remove1 (E ! 0) (remove1 (E ! 1) E) = E\<close>
        using EE'' unfolding E_E'[symmetric]
        by (cases E'; cases \<open>tl E'\<close>) auto
      show ?thesis (is \<open>(?T', ?T) \<in> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}\<close>)
      proof -
        have T: \<open>?T = ?T'\<close> and DD': \<open>D = D'\<close>
          using M1_M1a L'_La S_expand EE'' E' hd_uL' by (auto simp: uminus_lit_swap)

        have is_N\<^sub>1_add: \<open>is_N\<^sub>1 (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset N\<^sub>1\<close> if \<open>is_N\<^sub>1 B\<close> for A B
          using that unfolding is_N\<^sub>1_def by auto

        have LL: \<open>xa \<in> set E' \<longleftrightarrow> xa \<in># (the D)\<close> for xa
          using D_not_None S_expand mset_E_D' E_E' by auto
        have atms_take_U_N: \<open>atms_of_ms (mset ` set (take U (tl N))) \<subseteq> atms_of_ms (mset ` set (tl N))\<close>
          by (auto simp: atms_of_ms_def dest: in_set_takeD)

        have \<open>set_mset
             (lits_of_atms_of_m (add_mset (- lit_of (hd M)) (add_mset L' (mset E - {#- lit_of (hd M), L'#})))) \<subseteq> set_mset N\<^sub>1\<close>
        proof (cases M)
          case Nil
          then show ?thesis using M_not_Nil by fast
        next
          case (Cons L''' M')
          have
            alien_confl:\<open>atms_of (the D) \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close> and
            \<open>\<forall>L mark. Propagated L mark \<in> set (convert_lits_l N M) \<longrightarrow>
                atms_of mark \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close> and
            \<open>atms_of_ms (mset ` set (drop (Suc U) N)) \<subseteq>
                 atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close> and
            \<open>atms_of_mm UP \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close>
            \<open>atm_of ` lits_of_l M \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close>
            using M_not_Nil alien N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] atm_hd atm_L D_not_None EE'
            unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
            by (auto simp add: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
                image_image
                dest!: in_atms_of_minusD)
          have K_N: \<open>atm_of L' \<in> atms_of N\<^sub>1\<close>
            if \<open>atm_of L' \<in> atms_of_ms (mset ` set (tl N))\<close>
            for L' :: \<open>nat literal\<close>
            using M_not_Nil N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] atm_hd atm_L D_not_None EE' that
            unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
            by (auto simp add: in_lits_of_atms_of_mm_ain_atms_of_iff atm_of_eq_atm_of
                cdcl\<^sub>W_restart_mset_state clauses_def in_N\<^sub>1_iff S_expand
                in_lits_of_atms_of_m_ain_atms_of_iff LL
                mset_take_mset_drop_mset' H image_image
                dest!: in_atms_of_minusD)
          moreover have K_NP: \<open>atm_of L' \<in> atms_of N\<^sub>1\<close> if \<open>atm_of L' \<in> atms_of_mm NP\<close>
            for L' :: \<open>nat literal\<close>
            using M_not_Nil N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] atm_hd atm_L D_not_None EE' that
            unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
            by (auto simp add: in_lits_of_atms_of_mm_ain_atms_of_iff atm_of_eq_atm_of
                cdcl\<^sub>W_restart_mset_state clauses_def in_N\<^sub>1_iff S_expand
                in_lits_of_atms_of_m_ain_atms_of_iff LL
                mset_take_mset_drop_mset' H image_image
                dest!: in_atms_of_minusD)
          moreover have \<open>xa \<in> set E \<Longrightarrow> atm_of xa \<in> atms_of N\<^sub>1\<close> for xa
            using alien_confl EE'' atms_take_U_N DD' by (auto intro: K_N K_NP)
          ultimately show ?thesis
            using atm_hd atm_L
            by (auto simp add: in_N\<^sub>1_iff in_lits_of_atms_of_m_ain_atms_of_iff mset_take_mset_drop_mset'
                dest!: in_atms_of_minusD)
        qed
        then have \<open>literals_are_N\<^sub>0 ?T\<close>
          using N\<^sub>0 EE'' L'_D' uhd_D' hd_uL' L'_La S_expand
          by (cases \<open>Suc U - length N\<close>; cases N)
            (auto simp add: clauses_def mset_take_mset_drop_mset' uminus_lit_swap
              lits_of_atms_of_mm_union lits_of_atms_of_mm_add_mset (* is_N\<^sub>1_def *)
              in_lits_of_atms_of_mm_ain_atms_of_iff is_N\<^sub>1_add)
        then show ?thesis
          unfolding T by blast
      qed
    qed
    subgoal by simp
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M' SN' N'
      SU' U' SD' D' SNP' NP' SUP' UP' SWS' WS' W' M''' M'' L L'
    proof -
      note M'''_M'' = p(37)
      then obtain K c M2 where M': \<open>M' = c @ M2 @ Decided K # M'''\<close>
        by (clarsimp_all dest!: get_all_ann_decomposition_exists_prepend)
      define F where \<open>F = c @ M2\<close>
      have \<open>M' = F @ Decided K # M'''\<close>
        using M' F_def by auto
      moreover have \<open>no_dup (trail (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W))))\<close>
        using p(23) unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by fast
      ultimately show ?thesis
        using p(1-16) by (cases M'; cases F) (clarsimp_all simp: cdcl\<^sub>W_restart_mset_state)
    qed
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M' SN' N'
      SU' U' SD' D' SNP' NP' SUP' UP' SWS' WS' W' M''' M'' L L'
    proof -
      have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>
        using p(23) unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        by fast
      then show ?thesis
        using N\<^sub>0 unfolding p(1-16)
        apply (subst (asm) twl_struct_invs_is_N\<^sub>1_clauses_init_clss)
        using p(23) apply simp
        using p(1-16)
        by (cases M) (auto simp: image_image in_N\<^sub>1_iff cdcl\<^sub>W_restart_mset_state is_N\<^sub>1_alt_def
            cdcl\<^sub>W_restart_mset.no_strange_atm_def mset_take_mset_drop_mset')
    qed
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M' SN' N'
      SU' U' SD' D' SNP' NP' SUP' UP' SWS' WS' W' M''' M'' E E'
    proof -
      thm p
      note SWS = p(1) and SUP = p(2) and SNP = p(3) and SD = p(4) and SU = p(5) and SN = p(6) and
        S = p(7) and M_not_Nil = p(15) and lvl_count_decided = p(10) and D_not_None = p(18) and
        D_not_Some_Nil = p(19) and ex_decomp = p(20) and stgy_invs = p(22) and struct_invs = p(23)
        and no_skip = p(33) and M1_M1a = p(37) and E_E' = p(40) and
        S_expand = p(1-14)
      have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>
        using struct_invs
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast

      show ?thesis (is \<open>(?T', ?T) \<in> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}\<close>)
      proof -
        have T: \<open>?T = ?T'\<close>
          using M1_M1a S_expand E_E' by auto

        have is_N\<^sub>1_add: \<open>is_N\<^sub>1 (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset N\<^sub>1\<close> if \<open>is_N\<^sub>1 B\<close> for A B
          using that unfolding is_N\<^sub>1_def by auto


        have \<open>atms_of_ms (mset ` set (take U (tl N))) \<subseteq> atms_of_ms (mset ` set (tl N))\<close>
          by (auto simp: atms_of_ms_def dest: in_set_takeD)

        then have \<open>set_mset (lits_of_atms_of_m (the D)) \<subseteq> set_mset N\<^sub>1\<close>
          using M_not_Nil alien N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] D_not_None
          unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
          apply (cases M)
          by (auto 5 5 simp: in_lits_of_atms_of_mm_ain_atms_of_iff atm_of_eq_atm_of
              cdcl\<^sub>W_restart_mset_state clauses_def in_N\<^sub>1_iff S_expand
              in_lits_of_atms_of_m_ain_atms_of_iff
              mset_take_mset_drop_mset' H image_image
              dest!: in_atms_of_minusD)

        then have \<open>literals_are_N\<^sub>0 ?T\<close>
          using N\<^sub>0
          by (cases \<open>Suc U - length N\<close>; cases N)
            (simp_all add: clauses_def mset_take_mset_drop_mset' S_expand
              lits_of_atms_of_mm_union lits_of_atms_of_mm_add_mset (* is_N\<^sub>1_def *)
              in_lits_of_atms_of_mm_ain_atms_of_iff is_N\<^sub>1_add)
        then show ?thesis
          using T by blast
      qed
    qed
    done
qed


subsubsection \<open>Decide or Skip\<close>

definition decide_wl_or_skip_D :: "nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres" where
  \<open>decide_wl_or_skip_D S = (do {
    ASSERT(twl_struct_invs (twl_st_of_wl None S));
    ASSERT(twl_stgy_invs (twl_st_of_wl None S));
    ASSERT(additional_WS_invs (st_l_of_wl None S));
    ASSERT(get_conflict_wl S = None);
    ASSERT(literals_are_N\<^sub>0 S);
    L \<leftarrow> find_unassigned_lit_wl S;
    if L \<noteq> None
    then do {
      let (M, N, U, D, NP, UP, Q, W) = S;
      ASSERT(L \<noteq> None);
      ASSERT(the L \<in> snd ` D\<^sub>0);
      let K = the L;
      ASSERT(undefined_lit M K);
      RETURN (False, (Decided K # M, N, U, D, NP, UP, {#-K#}, W))}
    else do {RETURN (True, S)}
  })
\<close>

theorem decide_wl_or_skip_D_spec:
  assumes \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>decide_wl_or_skip_D S
    \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T} (decide_wl_or_skip S)\<close>
proof -
  let ?clss = \<open>(\<lambda>(_, N, _). N)\<close>
  let ?learned = \<open>(\<lambda>(_, _, U, _). U)\<close>
  have H: \<open>find_unassigned_lit_wl S \<le> \<Down> {(L', L). L = L' \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit (get_trail_wl S) (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# mset (take (?learned S) (tl (?clss S))))) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit (get_trail_wl S) L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# mset (take (?learned S) (tl (?clss S))))))}
     (find_unassigned_lit_wl S')\<close>
    if \<open>S = S'\<close>
    for S S'
    by (cases S') (auto simp: find_unassigned_lit_wl_def that intro!: RES_refine)

  have \<open>(decide_wl_or_skip_D, decide_wl_or_skip) \<in> {((T'), (T)).  T = T' \<and> literals_are_N\<^sub>0 T} \<rightarrow>\<^sub>f
     \<langle>{((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T}\<rangle> nres_rel\<close>
    unfolding decide_wl_or_skip_D_def decide_wl_or_skip_def
    apply (intro frefI)
    apply (refine_vcg H)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by simp
    subgoal by (simp add: mset_take_mset_drop_mset' clauses_def)
    subgoal by (auto simp add: mset_take_mset_drop_mset' clauses_def image_image
          is_N\<^sub>1_alt_def in_N\<^sub>1_iff)
    subgoal by (auto simp add: mset_take_mset_drop_mset' clauses_def image_image
          is_N\<^sub>1_alt_def in_N\<^sub>1_iff)
    subgoal by (simp add: mset_take_mset_drop_mset' clauses_def)
    subgoal by (simp add: mset_take_mset_drop_mset' clauses_def)
    done
  then show ?thesis
    using assms by (cases S) (auto simp: fref_def nres_rel_def)
qed

subsubsection \<open>Backtrack, Skip, Resolve or Decide\<close>

definition cdcl_twl_o_prog_wl_D :: "nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres" where
  \<open>cdcl_twl_o_prog_wl_D S =
    do {
      ASSERT(twl_struct_invs (twl_st_of_wl None S));
      ASSERT(twl_stgy_invs (twl_st_of_wl None S));
      ASSERT(additional_WS_invs (st_l_of_wl None S));
      do {
        if get_conflict_wl S = None
        then decide_wl_or_skip_D S
        else do {
          T \<leftarrow> skip_and_resolve_loop_wl_D S;
          ASSERT(get_conflict_wl T \<noteq> None);
          if get_conflict_wl T \<noteq> Some {#}
          then do {U \<leftarrow> backtrack_wl_D T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>

theorem cdcl_twl_o_prog_wl_D_spec:
  assumes \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T}
     (cdcl_twl_o_prog_wl S)\<close>
proof -
  have 1: \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (backtrack_wl T)\<close> if \<open>literals_are_N\<^sub>0 S\<close> and \<open>S = T\<close> for S T
    using backtrack_wl_D_spec[of S] that by fast
  have 2: \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl T)\<close>
    if N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> \<open>S = T\<close>
    for S T
    using skip_and_resolve_loop_wl_D_spec[of S] that by fast
  show ?thesis
    using assms
    unfolding cdcl_twl_o_prog_wl_D_def cdcl_twl_o_prog_wl_def
    apply (refine_vcg decide_wl_or_skip_D_spec 1 2)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by simp
    subgoal by auto
    subgoal by auto
    done
qed



subsubsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>cdcl_twl_stgy_prog_wl_D S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs (twl_st_of_wl None T) \<and>
          twl_stgy_invs (twl_st_of_wl None T) \<and>
          (brk \<longrightarrow> no_step cdcl_twl_stgy (twl_st_of_wl None T)) \<and>
          cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of_wl None S\<^sub>0) (twl_st_of_wl None T) \<and>
          (\<not>brk \<longrightarrow> get_conflict_wl T = None) \<and>
          literals_are_N\<^sub>0 T\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          cdcl_twl_o_prog_wl_D T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

theorem cdcl_twl_stgy_prog_wl_D_spec:
  assumes \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>cdcl_twl_stgy_prog_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
     (cdcl_twl_stgy_prog_wl S)\<close>
proof -
  have 1: \<open>((False, S), False, S) \<in> Id\<close> by fast
  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_N\<^sub>0 S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_N\<^sub>0 S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of S] that by fast
  show ?thesis
    using assms
    unfolding cdcl_twl_stgy_prog_wl_D_def cdcl_twl_stgy_prog_wl_def
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x x' x1 x2 S'
      by (cases x') fast
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


lemma cdcl_twl_stgy_prog_wl_D_spec_final2_Down:
  assumes \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S = None\<close> and \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    \<open>correct_watching S\<close> and \<open>literals_are_N\<^sub>0 S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl_D S \<le>
      \<Down> {(S, S'). S' = st_l_of_wl None S}
        (SPEC(\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of (twl_st_of_wl None S))
          (state\<^sub>W_of (twl_st_of None T))))\<close>
  apply (rule order.trans)
   apply (rule cdcl_twl_stgy_prog_wl_D_spec)
    using assms apply (solves \<open>simp\<close>)
  apply (rule order.trans)
     apply (rule ref_two_step)
      apply (rule order.refl)
     apply (rule cdcl_twl_stgy_prog_wl_spec_final2_Down)
    using assms apply (solves \<open>simp\<close>)+
    apply (auto simp: conc_fun_chain conc_fun_RES)
    done

theorem cdcl_twl_stgy_prog_wl_spec_final2:
  assumes \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S = None\<close> and \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    \<open>correct_watching S\<close> and \<open>literals_are_N\<^sub>0 S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl_D S \<le>
       SPEC(\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of (twl_st_of_wl None S))
          (state\<^sub>W_of (twl_st_of_wl None T)))\<close>
  using cdcl_twl_stgy_prog_wl_D_spec_final2_Down[OF assms] unfolding conc_fun_SPEC
  by auto

end -- \<open>end of locale @{locale twl_array_code}\<close>

end
