theory CDCL_Two_Watched_Literals_List_Watched_Domain
  imports CDCL_Two_Watched_Literals_List_Watched Array_Array_List Array_List_Array
    WB_Word_Assn "../lib/Explorer"
begin

text \<open>We refine the implementation by adding a \<^emph>\<open>domain\<close> on the literals\<close>

no_notation Ref.update ("_ := _" 62)

subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym clauses_to_update_ll = \<open>nat list\<close>
type_synonym lit_queue_l = \<open>uint32 list\<close>
type_synonym nat_trail = \<open>(uint32 \<times> nat option) list\<close>
type_synonym clause_wl = \<open>uint32 array\<close>
type_synonym unit_lits_wl = \<open>uint32 list list\<close>

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

definition unat_lit_rel :: "(uint32 \<times> nat literal) set" where
  \<open>unat_lit_rel \<equiv> uint32_nat_rel O nat_lit_rel\<close>

abbreviation unat_lit_assn :: "nat literal \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>unat_lit_assn \<equiv> pure unat_lit_rel\<close>

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

lemma
   nat_lit_rel_right_unique: \<open>IS_RIGHT_UNIQUE nat_lit_rel\<close> and
   nat_lit_rel_left_unique: \<open>IS_LEFT_UNIQUE nat_lit_rel\<close>
  unfolding single_valued_def nat_lit_rel_def IS_LEFT_UNIQUE_def
  by (auto simp: lit_of_natP_nat_of_lit_iff)

term \<open>\<lambda>R R'. {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>

definition ann_lit_rel:: "('a \<times> nat) set \<Rightarrow> ('b \<times> nat option) set \<Rightarrow>
    (('a \<times> 'b) \<times> (nat, nat) ann_lit) set" where
  ann_lit_rel_internal_def:
  \<open>ann_lit_rel R R' = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>

type_synonym ann_lit_wl = \<open>uint32 \<times> nat option\<close>
type_synonym ann_lits_wl = \<open>ann_lit_wl list\<close>
term \<open> \<langle>uint32_nat_rel\<rangle>option_rel\<close>

definition nat_ann_lit_rel :: "(ann_lit_wl \<times> (nat, nat) ann_lit) set" where
  nat_ann_lit_rel_internal_def: \<open>nat_ann_lit_rel = \<langle>uint32_nat_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>ann_lit_rel\<close>

lemma ann_lit_rel_def:
  \<open>\<langle>R, R'\<rangle>ann_lit_rel = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>
  unfolding nat_ann_lit_rel_internal_def ann_lit_rel_internal_def relAPP_def ..

lemma nat_ann_lit_rel_def:
  \<open>nat_ann_lit_rel = {(a, b). b = ann_lit_of_pair ((\<lambda>(a,b). (literal_of_nat (nat_of_uint32 a), b)) a)}\<close>
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
  \<open>pair_nat_ann_lit_assn \<equiv> pure nat_ann_lit_rel\<close>

abbreviation pair_nat_ann_lits_assn :: "(nat, nat) ann_lits \<Rightarrow> ann_lits_wl \<Rightarrow> assn" where
  \<open>pair_nat_ann_lits_assn \<equiv> list_assn pair_nat_ann_lit_assn\<close>

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

definition upperN :: nat where
  \<open>upperN = 2 ^32\<close>

text \<open>We start in a context where we have an initial set of atoms. \<close>
locale twl_array_code_ops =
  fixes N\<^sub>0 :: \<open>nat multiset\<close>
begin

text \<open>This is the \<^emph>\<open>completion\<close> of \<^term>\<open>N\<^sub>0\<close>, containing the positive and the negation of every
  literal of \<^term>\<open>N\<^sub>0\<close>:\<close>
definition N\<^sub>1 where \<open>N\<^sub>1 = poss N\<^sub>0 + negs N\<^sub>0\<close>

definition is_N\<^sub>1 :: "nat literal multiset \<Rightarrow> bool" where
  \<open>is_N\<^sub>1 S \<longleftrightarrow> set_mset S = set_mset N\<^sub>1\<close>

abbreviation literals_are_N\<^sub>0 where
  \<open>literals_are_N\<^sub>0 S \<equiv>
     is_N\<^sub>1 (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S))))\<close>

definition literals_are_in_N\<^sub>0 :: \<open>nat clause \<Rightarrow> bool\<close> where
  \<open>literals_are_in_N\<^sub>0 C \<longleftrightarrow> set_mset (all_lits_of_m C) \<subseteq> set_mset N\<^sub>1\<close>

lemma all_lits_of_m_subset_all_lits_of_mmD:
  \<open>a \<in># b \<Longrightarrow> set_mset (all_lits_of_m a) \<subseteq> set_mset (all_lits_of_mm b)\<close>
  by (auto simp: all_lits_of_m_def all_lits_of_mm_def)

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
  from all_lits_of_m_subset_all_lits_of_mmD[OF this] show ?thesis
    using assms(3) unfolding is_N\<^sub>1_def literals_are_in_N\<^sub>0_def by blast
qed

lemma in_N\<^sub>1_atm_of_in_atms_of_iff: \<open>x \<in># N\<^sub>1 \<longleftrightarrow> atm_of x \<in> atms_of N\<^sub>1\<close>
  by (cases x) (auto simp: N\<^sub>1_def atms_of_def atm_of_eq_atm_of image_Un image_image)

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

lemma hr_comp_uint32_nat_assn_nat_lit_rel[simp]:
  \<open>hr_comp uint32_nat_assn nat_lit_rel = unat_lit_assn\<close>
  by (auto simp: hrp_comp_def hr_comp_def uint32_nat_rel_def
        lit_of_natP_def hr_comp_pure br_def unat_lit_rel_def)

lemma length_aa_length_ll_f[sepref_fr_rules]:
  \<open>(uncurry length_aa_u, uncurry (RETURN oo length_ll_f)) \<in>
   [\<lambda>(W, L). L \<in> snd ` D\<^sub>0]\<^sub>a
     array_watched_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry length_aa_u, uncurry (RETURN \<circ>\<circ> length_ll_f))
     \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel)
     (\<lambda>(W, L). L \<in> snd ` D\<^sub>0) (\<lambda>_ (xs, i). i < length xs)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     ((arrayO_assn (arl_assn nat_assn))\<^sup>k *\<^sub>a
                      uint32_nat_assn\<^sup>k)
                     (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r
                      nat_lit_rel) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_aa_u_hnr length_ll_length_ll_f] .

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

lemma atms_of_N\<^sub>1_N\<^sub>0: \<open>atms_of N\<^sub>1 = set_mset N\<^sub>0\<close>
  unfolding N\<^sub>1_def by (auto simp: atms_of_def image_Un image_image)

end


locale twl_array_code =
  twl_array_code_ops N\<^sub>0
  for N\<^sub>0 :: \<open>nat multiset\<close> +
  assumes in_N1_less_than_upperN: \<open>\<forall>L \<in># N\<^sub>1. nat_of_lit L < upperN\<close>
begin

definition unit_prop_body_wl_D_inv where
\<open>unit_prop_body_wl_D_inv T' i L \<longleftrightarrow>
    unit_prop_body_wl_inv T' i L \<and> literals_are_N\<^sub>0 T' \<and> L \<in> snd ` D\<^sub>0
  \<close>

definition unit_propagation_inner_loop_body_wl_D :: "nat literal \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow>
    (nat \<times> nat twl_st_wl) nres" where
  \<open>unit_propagation_inner_loop_body_wl_D L w S = do {
      ASSERT(unit_prop_body_wl_D_inv S w L);
      let C = (watched_by S L) ! w;
      let i = (if ((get_clauses_wl S)!C) ! 0 = L then 0 else 1);
      let L' = ((get_clauses_wl S)!C) ! (1 - i);
      let val_L' = valued (get_trail_wl S) L';
      if val_L' = Some True
      then RETURN (w+1, S)
      else do {
        f \<leftarrow> find_unwatched_l (get_trail_wl S) ((get_clauses_wl S)!C);
        ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
        case f of
          None \<Rightarrow>
            if val_L' = Some False
            then do {RETURN (w+1, mark_conflict_wl ((get_clauses_wl S)!C) S)}
            else do {RETURN (w+1, propgate_lit_wl L' C S)}
        | Some f \<Rightarrow> do {
            update_clause_wl L C w i f S
          }
      }
   }\<close>

declare Id_refine[refine_vcg del] refine0(5)[refine_vcg del]

lemma (in -) mset_tl_update_swap:
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
  have f': \<open>(f, f') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>(f, f') \<in> Id\<close> for f f'
    using that by auto
  define find_unwatched_wl :: \<open>(nat,nat) ann_lits \<Rightarrow> _\<close> where
    \<open>find_unwatched_wl = find_unwatched_l\<close>
  have find_unwatched: \<open>find_unwatched_wl (get_trail_wl S) ((get_clauses_wl S)!((watched_by S K) ! w))
    \<le> \<Down> {(L, L'). L = L' \<and> (L \<noteq> None \<longrightarrow> the L < length ((get_clauses_wl S)!((watched_by S K) ! w)) \<and> the L \<ge> 2)}
        (find_unwatched_l (get_trail_wl S) ((get_clauses_wl S)!((watched_by S K) ! w)))\<close>
      (is \<open>_ \<le> \<Down> ?find_unwatched _\<close>)
    for C and L and K
    unfolding find_unwatched_l_def find_unwatched_wl_def S
    by (auto simp: intro!: RES_refine)

  have \<open>mset `# mset (take n (tl xs)) +
    mset `# mset (drop (Suc n) xs) =
    mset `# mset (tl xs)\<close> for n :: nat and xs :: \<open>'a list list\<close>
    unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc
      append_take_drop_id ..
  then have m: \<open>(mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b)) =
         (mset `# mset (tl xs)) + a + b\<close>
    for a b and xs :: \<open>'a list list\<close> and n :: nat
    by auto

  have update_clause_wl: \<open>update_clause_wl K (watched_by S K ! w) w
     (if get_clauses_wl S ! (watched_by S K ! w) ! 0 = K then 0 else 1) n S
    \<le> \<Down> {((n', T'), n, T). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}
       (update_clause_wl K (watched_by S K ! w) w
         (if get_clauses_wl S ! (watched_by S K ! w) ! 0 = K then 0 else 1) n' S)\<close>
    if \<open>(n, n') \<in> Id\<close> and \<open>unit_prop_body_wl_D_inv S w K\<close>
      \<open>(f, f') \<in> ?find_unwatched K\<close> and
      \<open>f = Some n\<close> \<open>f' = Some n'\<close> and
      \<open>unit_prop_body_wl_find_unwatched_inv f (watched_by S K ! w) S\<close>
    for n n' f f'
    unfolding update_clause_wl_def S
    apply clarify
    apply refine_vcg
    using that N\<^sub>0
    by (auto simp: clauses_def  mset_take_mset_drop_mset mset_tl_update_swap unit_prop_body_wl_find_unwatched_inv_def
          mset_take_mset_drop_mset' m S unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def)
  show ?thesis
    unfolding unit_propagation_inner_loop_body_wl_D_def find_unwatched_wl_def[symmetric]
    unfolding unit_propagation_inner_loop_body_wl_def
    supply [[goals_limit=1]]
    apply (refine_rcg find_unwatched f')
    subgoal using assms unfolding S unit_prop_body_wl_D_inv_def by auto
    subgoal by simp
    subgoal by (auto simp: unit_prop_body_wl_D_inv_def)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (auto simp: mark_conflict_wl_def S unit_prop_body_wl_D_inv_def clauses_def)
    subgoal by (auto simp: propgate_lit_wl_def S unit_prop_body_wl_D_inv_def clauses_def)
    subgoal by (rule update_clause_wl) assumption+
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
  then show ?G2
    apply -
    apply (match_spec)
    apply (match_fun_rel; match_fun_rel?)
    by fastforce+
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
        ASSERT(L \<in># all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S))));
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
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_inv (twl_st_of_wl None S\<^sub>0) (brk, twl_st_of_wl None S) \<and>
         additional_WS_invs (st_l_of_wl None S) \<and> correct_watching S \<and> literals_are_N\<^sub>0 S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          do {
            let D' = the (get_conflict_wl S);
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S));
            if -L \<notin># D' then
              do {RETURN (False, tl_state_wl S)}
            else
              if get_maximum_level (get_trail_wl S) (remove1_mset (-L) D') = count_decided (get_trail_wl S)
              then
                do {RETURN (update_confl_tl_wl C L S)}
              else
                do {RETURN (True, S)}
          }
        )
        (get_conflict_wl S\<^sub>0 = Some {#}, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma twl_struct_invs_is_N\<^sub>1_clauses_init_clss:
  fixes S\<^sub>0 :: \<open>nat twl_st_wl\<close>
  defines \<open>S \<equiv> twl_st_of_wl None S\<^sub>0\<close>
  defines \<open>clss \<equiv> (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of S)))\<close>
  defines \<open>init \<equiv> (all_lits_of_mm (init_clss (state\<^sub>W_of S)))\<close>
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
        cdcl\<^sub>W_restart_mset.no_strange_atm_def in_all_lits_of_mm_ain_atms_of_iff)
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

lemma is_N\<^sub>1_alt_def: \<open>is_N\<^sub>1 (all_lits_of_mm A) \<longleftrightarrow> atms_of_mm A = atms_of N\<^sub>1\<close>
  unfolding set_mset_set_mset_eq_iff is_N\<^sub>1_def Ball_def in_N\<^sub>1_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff
  by auto (metis literal.sel(2))+


lemma skip_and_resolve_loop_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close>
  shows \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl S)\<close>
    (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  define invar where
   \<open>invar = (\<lambda>(brk, T). skip_and_resolve_loop_inv (twl_st_of_wl None S) (brk, twl_st_of_wl None T) \<and>
         additional_WS_invs (st_l_of_wl None T) \<and> correct_watching T \<and> literals_are_N\<^sub>0 T)\<close>
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto
  have H: \<open>(\<lambda>(brk, T). skip_and_resolve_loop_inv (twl_st_of_wl None S) (brk, twl_st_of_wl None T) \<and>
         additional_WS_invs (st_l_of_wl None T) \<and> correct_watching T) =
       invar\<close>
    apply (intro ext, rename_tac brkT)
    subgoal for brkT
      using cdcl_twl_o_literals_are_N\<^sub>0_invs[of S \<open>snd brkT\<close>]
      using 1 N\<^sub>0 unfolding invar_def skip_and_resolve_loop_inv_def
      apply (cases brkT)
      apply clarify
      apply simp
      by blast
    done

  show ?thesis
    unfolding skip_and_resolve_loop_wl_D_def skip_and_resolve_loop_wl_def H
    apply (subst (2) WHILEIT_add_post_condition)
    apply (refine_rcg 1 WHILEIT_refine[where R = \<open>{((i', S'), (i, S)). i = i' \<and> (S', S) \<in> ?R}\<close>])
    subgoal using assms by auto
    subgoal unfolding invar_def by fast
    subgoal unfolding invar_def by fast
    subgoal unfolding invar_def by fast
    subgoal by fast
    subgoal by fast
    subgoal by auto
    subgoal unfolding invar_def by auto
    subgoal by auto
    subgoal unfolding invar_def by auto
    subgoal by fast
    subgoal by auto
    done
qed

definition find_lit_of_max_level_wl' :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
   nat literal nres" where
  \<open>find_lit_of_max_level_wl' M N U D NP UP Q W L =
     find_lit_of_max_level_wl (M, N, U, Some D, NP, UP, Q, W) L\<close>

definition (in -) list_of_mset2 :: "nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause \<Rightarrow> nat clause_l nres" where
  \<open>list_of_mset2 L L' D =
    SPEC (\<lambda>E. mset E = D \<and> E!0 = L \<and> E!1 = L')\<close>

definition (in -) single_of_mset where
  \<open>single_of_mset D = SPEC(\<lambda>L. D = mset [L])\<close>

definition backtrack_wl_D_inv where
  \<open>backtrack_wl_D_inv S \<longleftrightarrow> backtrack_wl_inv S \<and> literals_are_N\<^sub>0 S\<close>

definition propgate_bt_wl_D :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>propgate_bt_wl_D = (\<lambda>L L' (M, N, U, D, NP, UP, Q, W). do {
    D'' \<leftarrow> list_of_mset2 (-L) L' (the D);
    RETURN (Propagated (-L) (length N) # M,
        N @ [D''], U,
          None, NP, UP, {#L#}, W(-L:= W (-L) @ [length N], L':= W L' @ [length N]))
      })\<close>

definition propgate_unit_bt_wl_D :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close> where
  \<open>propgate_unit_bt_wl_D = (\<lambda>L (M, N, U, D, NP, UP, Q, W). do {
        D' \<leftarrow> single_of_mset (the D);
        RETURN (Propagated (-L) 0 # M, N, U, None, NP, add_mset {#D'#} UP, {#L#}, W)
    })\<close>

definition backtrack_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>backtrack_wl_D S =
    do {
      ASSERT(backtrack_wl_D_inv S);
      let L = lit_of (hd (get_trail_wl S));
      S \<leftarrow> extract_shorter_conflict_wl S;
      S \<leftarrow> find_decomp_wl L S;

      if size (the (get_conflict_wl S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_wl S L;
        propgate_bt_wl_D L L' S
      }
      else do {
        propgate_unit_bt_wl_D L S
     }
  }\<close>
lemma literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0:
  assumes
    N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
  shows \<open>literals_are_in_N\<^sub>0 (the (get_conflict_wl S))\<close>
proof -
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have N: \<open>atms_of (the (get_conflict_wl S)) \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S)))\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases S; cases \<open>get_conflict_wl S\<close>)
       (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset')

  have \<open>is_N\<^sub>1 (all_lits_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S))))\<close>
    using twl_struct_invs_is_N\<^sub>1_clauses_init_clss[OF struct] N\<^sub>0 by fast
  then show ?thesis
    using N in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff
    by (fastforce simp: literals_are_in_N\<^sub>0_def is_N\<^sub>1_def )
qed

lemma literals_are_in_N\<^sub>0_mono:
  assumes N: \<open>literals_are_in_N\<^sub>0 D'\<close> and D: \<open>D \<subseteq># D'\<close>
  shows \<open>literals_are_in_N\<^sub>0 D\<close>
proof -
  have \<open>set_mset (all_lits_of_m D) \<subseteq> set_mset (all_lits_of_m D')\<close>
    using D by (auto simp: in_all_lits_of_m_ain_atms_of_iff atm_iff_pos_or_neg_lit)
  then show ?thesis
     using N unfolding literals_are_in_N\<^sub>0_def by fast
qed

lemma backtrack_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and confl: \<open>get_conflict_wl S ~= None\<close>
  shows \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (backtrack_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto

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
  have list_of_mset: \<open>list_of_mset2 L L' D \<le>
      \<Down> {(E, F). F = [L, L'] @ remove1 L (remove1 L' E) \<and> D = mset E \<and> E!0 = L \<and> E!1 = L' \<and> E=F}
        (list_of_mset D')\<close>
    (is \<open>_ \<le> \<Down> ?list_of_mset _\<close>)
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

  define extract_shorter_conflict_wl' where
    \<open>extract_shorter_conflict_wl' S = extract_shorter_conflict_wl S\<close> for S :: \<open>nat twl_st_wl\<close>
  define find_lit_of_max_level_wl' where
    \<open>find_lit_of_max_level_wl' S = find_lit_of_max_level_wl S\<close> for S :: \<open>nat twl_st_wl\<close>

  have extract_shorter_conflict_wl: \<open>extract_shorter_conflict_wl' S
    \<le> \<Down> {(U, U'). U = U' \<and> equality_except_conflict U S \<and> get_conflict_wl U \<noteq> None \<and>
      the (get_conflict_wl U) \<subseteq># the (get_conflict_wl S) \<and>
      -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl U)
      } (extract_shorter_conflict_wl S)\<close>
    (is \<open>_ \<le> \<Down> ?extract_shorter _\<close>)
    unfolding extract_shorter_conflict_wl'_def extract_shorter_conflict_wl_def
    by (cases S)
      (auto 5 5 simp: extract_shorter_conflict_wl'_def extract_shorter_conflict_wl_def
       intro!: RES_refine)

  have find_decomp_wl: \<open>find_decomp_wl (lit_of (hd (get_trail_wl S))) T
    \<le> \<Down> {(U, U'). U = U' \<and> equality_except_trail U T} (find_decomp_wl (lit_of (hd (get_trail_wl S))) T')\<close>
    (is \<open>_ \<le> \<Down> ?find_decomp _\<close>)
    if \<open>(T, T') \<in> ?extract_shorter\<close>
    for T T'
    using that unfolding find_decomp_wl_def
    by (cases T) (auto 5 5 intro!: RES_refine)

  have find_lit_of_max_level_wl:
    \<open>find_lit_of_max_level_wl U (lit_of (hd (get_trail_wl S)))
      \<le> \<Down> Id (find_lit_of_max_level_wl U' (lit_of (hd (get_trail_wl S))))\<close>
    if
      \<open>(U, U') \<in> ?find_decomp T\<close>
    for T U U'
    using that unfolding find_lit_of_max_level_wl_def
    by (cases T) (auto 5 5 intro!: RES_refine)

  have find_lit_of_max_level_wl':
     \<open>find_lit_of_max_level_wl' U (lit_of (hd (get_trail_wl S)))
        \<le> \<Down>{(L, L'). L = L' \<and> L \<in># remove1_mset (-lit_of (hd (get_trail_wl S))) (the (get_conflict_wl U))}
           (find_lit_of_max_level_wl U' (lit_of (hd (get_trail_wl S))))\<close>
      (is \<open>_ \<le> \<Down> ?find_lit _\<close>)
    if
      "backtrack_wl_inv S" and
      "backtrack_wl_D_inv S" and
      "(U, U') \<in> ?find_decomp T" and
      "1 < size (the (get_conflict_wl U))" and
      "1 < size (the (get_conflict_wl U'))"
    for U U' T
    using that unfolding find_lit_of_max_level_wl'_def find_lit_of_max_level_wl_def
    by (cases U) (auto 5 5 intro!: RES_refine)

  have is_N\<^sub>1_add: \<open>is_N\<^sub>1 (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset N\<^sub>1\<close> if \<open>is_N\<^sub>1 B\<close> for A B
    using that unfolding is_N\<^sub>1_def by auto

  have propgate_bt_wl_D: "propgate_bt_wl_D (lit_of (hd (get_trail_wl S))) L U
        \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
           (propgate_bt_wl (lit_of (hd (get_trail_wl S))) L' U')"
    if
      "backtrack_wl_inv S" and
      bt: "backtrack_wl_D_inv S" and
      TT': "(T, T') \<in> ?extract_shorter" and
      UU': "(U, U') \<in> ?find_decomp T" and
      "1 < size (the (get_conflict_wl U))" and
      "1 < size (the (get_conflict_wl U'))" and
      LL': "(L, L') \<in> ?find_lit U"
    for L L' T T' U U'
  proof -
    obtain MS NS US DS NPS UPS W Q where
       S: \<open>S = (MS, NS, US, Some DS, NPS, UPS, Q, W)\<close>
      using bt by (cases S; cases \<open>get_conflict_wl S\<close>)
        (auto simp: backtrack_wl_D_inv_def backtrack_wl_inv_def
          backtrack_l_inv_def)
    then obtain DT where
      T: \<open>T = (MS, NS, US, Some DT, NPS, UPS, Q, W)\<close> and DT: \<open>DT \<subseteq># DS\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU where
      U: \<open>U = (MU, NS, US, Some DT, NPS, UPS, Q, W)\<close> and U': \<open>U' = U\<close>
      using UU' by (cases U) auto
    define list_of_mset where
      \<open>list_of_mset D L L' = ?list_of_mset D L L'\<close> for D and L L' :: \<open>nat literal\<close>
    have
      dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
      N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and
      struct: \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close>
      using bt unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    then have \<open>distinct_mset DT\<close>
      using DT unfolding S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      by (auto simp: cdcl\<^sub>W_restart_mset_state intro: distinct_mset_mono)
    then have [simp]: \<open>L \<noteq> -lit_of (hd MS)\<close>
      using LL' by (auto simp: U S dest: distinct_mem_diff_mset)
    have propa_ref:
      \<open>((Propagated (- lit_of (hd (get_trail_wl S))) (length NS) # MU, NS @ [D], US, None, NPS, UPS, unmark (hd (get_trail_wl S)), W
          (- lit_of (hd (get_trail_wl S)) := W (- lit_of (hd (get_trail_wl S))) @ [length NS], L := W L @ [length NS])),
         Propagated (- lit_of (hd (get_trail_wl S))) (length NS) # MU,
         NS @ [[- lit_of (hd (get_trail_wl S)), L'] @ remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L' D')], US, None, NPS, UPS,
         unmark (hd (get_trail_wl S)), W
         (- lit_of (hd (get_trail_wl S)) := W (- lit_of (hd (get_trail_wl S))) @ [length NS], L' := W L' @ [length NS]))
        \<in> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}\<close>
      if DD': \<open>(D, D') \<in> list_of_mset (the (Some DT)) (- lit_of (hd (get_trail_wl S))) L\<close>
      for D D'
    proof -
      have [simp]: \<open>L = L'\<close>
        using LL' by fast
      have DD'_eq[simp]: \<open>D' = D\<close> and D_DT: \<open>mset D = DT\<close>
        using DD' unfolding list_of_mset_def by force+
      have [simp]: "- lit_of (hd MS) # L' # remove1 (- lit_of (hd MS)) (remove1 L' D) = D"
        using DD' that LL' unfolding list_of_mset_def by (cases D; cases \<open>tl D\<close>) (auto simp: S)


      have [simp]: \<open>US < length NS\<close> \<open>NS \<noteq> []\<close>
        using add_invs unfolding S additional_WS_invs_def by auto
      have [simp]: \<open>is_N\<^sub>1 (all_lits_of_mm
        (mset `# mset (take US (tl NS)) + NPS + (mset `# mset (drop (Suc US) NS) + UPS)))\<close>
        apply (rule subst[of _ _ \<open>is_N\<^sub>1\<close>, OF _ N\<^sub>0])
        apply (rule arg_cong[of _ _ \<open>all_lits_of_mm\<close>])
        by (auto simp: clauses_def U U' S T mset_take_mset_drop_mset mset_take_mset_drop_mset'
           all_lits_of_mm_add_mset)
      then have [simp]: \<open>is_N\<^sub>1 (all_lits_of_mm (mset `# mset (tl NS) + NPS + UPS))\<close>
        apply (rule back_subst)
        apply (rule arg_cong[of _ _ \<open>is_N\<^sub>1\<close>])
        apply (rule arg_cong[of _ _ \<open>all_lits_of_mm\<close>])
        by (auto simp: clauses_def U U' S T mset_take_mset_drop_mset mset_take_mset_drop_mset'
           all_lits_of_mm_add_mset)
      have struct': \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
        using struct by simp
      have \<open>literals_are_in_N\<^sub>0 DS\<close>
        using literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0[OF N\<^sub>0 _ struct']
        by (simp add: S)
      then have N\<^sub>0_D: \<open>literals_are_in_N\<^sub>0 (mset D)\<close>
        using DT unfolding D_DT by (blast intro: literals_are_in_N\<^sub>0_mono)
      have \<open>take (Suc US - length NS) [D] = [D] \<and> drop (Suc US - length NS) [D] = [] \<or>
          take (Suc US - length NS) [D] = [] \<and> drop (Suc US - length NS) [D] = [D]\<close>
        by (cases \<open>Suc US - length NS\<close>) (auto)
      then show ?thesis
        using N\<^sub>0_D
        by (auto simp: clauses_def U U' S T mset_take_mset_drop_mset mset_take_mset_drop_mset'
           all_lits_of_mm_add_mset is_N\<^sub>1_add Suc_leI literals_are_in_N\<^sub>0_def)
    qed
    show ?thesis
      unfolding propgate_bt_wl_D_def propgate_bt_wl_def propgate_bt_wl_D_def U U' S T
      apply clarify
      apply (refine_vcg list_of_mset)
      subgoal ..
      subgoal using TT' T by (auto simp: U S)
      subgoal using LL' by (auto simp: T U S dest: in_diffD)
      subgoal using LL' by auto
      subgoal for D D'
        unfolding list_of_mset_def[symmetric] U[symmetric] U'[symmetric] S[symmetric] T[symmetric]
        by (rule propa_ref)
      done
  qed

  have propgate_unit_bt_wl_D: "propgate_unit_bt_wl_D (lit_of (hd (get_trail_wl S))) U
    \<le> SPEC (\<lambda>c. (c, propgate_unit_bt_wl (lit_of (hd (get_trail_wl S))) U')
                 \<in> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T})"
    if
      "backtrack_wl_inv S" and
      bt: "backtrack_wl_D_inv S" and
      TT': "(T, T') \<in> ?extract_shorter" and
      UU': "(U, U') \<in> ?find_decomp T" and
      "\<not>1 < size (the (get_conflict_wl U))" and
      "\<not>1 < size (the (get_conflict_wl U'))"
    for L L' T T' U U'
  proof -
    obtain MS NS US DS NPS UPS W Q where
       S: \<open>S = (MS, NS, US, Some DS, NPS, UPS, Q, W)\<close>
      using bt by (cases S; cases \<open>get_conflict_wl S\<close>)
        (auto simp: backtrack_wl_D_inv_def backtrack_wl_inv_def
          backtrack_l_inv_def)
    then obtain DT where
      T: \<open>T = (MS, NS, US, Some DT, NPS, UPS, Q, W)\<close> and DT: \<open>DT \<subseteq># DS\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU where
      U: \<open>U = (MU, NS, US, Some DT, NPS, UPS, Q, W)\<close> and U': \<open>U' = U\<close>
      using UU' by (cases U) auto
    have
      dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
      N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and
      struct: \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close>
      using bt unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have [simp]: \<open>is_N\<^sub>1 (all_lits_of_mm
       (mset `# mset (take US (tl NS)) + NPS + (mset `# mset (drop (Suc US) NS) + UPS)))\<close>
        apply (rule subst[of _ _ \<open>is_N\<^sub>1\<close>, OF _ N\<^sub>0])
        apply (rule arg_cong[of _ _ \<open>all_lits_of_mm\<close>])
        by (auto simp: clauses_def U U' S T mset_take_mset_drop_mset mset_take_mset_drop_mset'
           all_lits_of_mm_add_mset)
    have struct': \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
      using struct by simp
    have \<open>literals_are_in_N\<^sub>0 DS\<close>
      using literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0[OF N\<^sub>0 _ struct']
      by (simp add: S)
    then have N\<^sub>0_D: \<open>literals_are_in_N\<^sub>0 DT\<close>
      using DT by (blast intro: literals_are_in_N\<^sub>0_mono)
    show ?thesis
      unfolding propgate_unit_bt_wl_D_def propgate_unit_bt_wl_def U U' single_of_mset_def
      apply clarify
      apply refine_vcg
      using N\<^sub>0_D by (auto simp: clauses_def mset_take_mset_drop_mset mset_take_mset_drop_mset'
          all_lits_of_mm_add_mset is_N\<^sub>1_add literals_are_in_N\<^sub>0_def)
  qed
  show ?thesis
    unfolding backtrack_wl_D_def backtrack_wl_def find_lit_of_max_level_wl'_def
      array_of_arl_def
    apply (subst  extract_shorter_conflict_wl'_def[symmetric])
    apply (subst find_lit_of_max_level_wl'_def[symmetric])
    supply [[goals_limit=1]]
    apply (refine_vcg extract_shorter_conflict_wl find_lit_of_max_level_wl find_decomp_wl
       find_lit_of_max_level_wl' propgate_bt_wl_D propgate_unit_bt_wl_D)
    subgoal using N\<^sub>0 unfolding backtrack_wl_D_inv_def by fast
    subgoal by auto
    by assumption+
qed


subsubsection \<open>Decide or Skip\<close>

definition find_unassigned_lit_wl_D where
  \<open>find_unassigned_lit_wl_D S = (
     SPEC(\<lambda>((M, N, U, D, NP, UP, WS, Q), L).
         S = (M, N, U, D, NP, UP, WS, Q) \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N)))) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N)))))))

\<close>
definition decide_wl_or_skip_D :: "nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres" where
  \<open>decide_wl_or_skip_D S = (do {
    ASSERT(twl_struct_invs (twl_st_of_wl None S));
    ASSERT(twl_stgy_invs (twl_st_of_wl None S));
    ASSERT(additional_WS_invs (st_l_of_wl None S));
    ASSERT(get_conflict_wl S = None);
    ASSERT(literals_are_N\<^sub>0 S);
    (S, L) \<leftarrow> find_unassigned_lit_wl_D S;
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
  have H: \<open>find_unassigned_lit_wl_D S \<le> \<Down> {((S', L'), L). S' = S \<and> L = L' \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit (get_trail_wl S) (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# mset (take (?learned S) (tl (?clss S))))) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit (get_trail_wl S) L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# mset (take (?learned S) (tl (?clss S))))))}
     (find_unassigned_lit_wl S')\<close>
    if \<open>S = S'\<close>
    for S S'
    by (cases S') (auto simp: find_unassigned_lit_wl_def find_unassigned_lit_wl_D_def that
        intro!: RES_refine)

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
          is_N\<^sub>1_alt_def in_N\<^sub>1_atm_of_in_atms_of_iff)
    subgoal by (auto simp add: mset_take_mset_drop_mset' clauses_def image_image
          is_N\<^sub>1_alt_def in_N\<^sub>1_atm_of_in_atms_of_iff)
    subgoal by (auto simp add: mset_take_mset_drop_mset' clauses_def)
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
  \<close>

theorem cdcl_twl_o_prog_wl_D_spec:
  assumes \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T}
     (cdcl_twl_o_prog_wl S)\<close>
proof -
  have 1: \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (backtrack_wl T)\<close> if \<open>literals_are_N\<^sub>0 S\<close> and \<open>get_conflict_wl S ~= None\<close> and \<open>S = T\<close>
    for S T
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
          additional_WS_invs (st_l_of_wl None T) \<and>
          correct_watching T \<and>
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
  have 1: \<open>((False, S), False, S) \<in> {((brk', T'), brk, T). brk = brk' \<and> T = T' \<and> literals_are_N\<^sub>0 T}\<close>
    using assms by fast
  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_N\<^sub>0 S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_N\<^sub>0 S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_D_def cdcl_twl_stgy_prog_wl_def
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by auto
    subgoal by fast
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
