theory CDCL_W_Partial_Encoding
  imports CDCL_W_Optimal_Model
begin


subsection \<open>Encoding of partial SAT into total SAT\<close>

definition DECO_clause :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v clause\<close> where
  \<open>DECO_clause M = (uminus o lit_of) `# (filter_mset is_decided (mset M))\<close>

lemma
  DECO_clause_cons_Decide[simp]:
    \<open>DECO_clause (Decided L # M) = add_mset (-L) (DECO_clause M)\<close> and
  DECO_clause_cons_Proped[simp]:
    \<open>DECO_clause (Propagated L C # M) = DECO_clause M\<close>
  by (auto simp: DECO_clause_def)


text \<open>As a way to make sure we don't reuse theorems names:\<close>
interpretation test: conflict_driven_clause_learning\<^sub>W_optimal_weight where
  state_eq = \<open>(=)\<close> and
  state = id and
  trail = \<open>\<lambda>(M, N, U, D, W). M\<close> and
  init_clss = \<open>\<lambda>(M, N, U, D, W). N\<close> and
  learned_clss = \<open>\<lambda>(M, N, U, D, W). U\<close> and
  conflicting = \<open>\<lambda>(M, N, U, D, W). D\<close> and
  cons_trail = \<open>\<lambda>K (M, N, U, D, W). (K # M, N, U, D, W)\<close> and
  tl_trail = \<open>\<lambda>(M, N, U, D, W). (tl M, N, U, D, W)\<close> and
  add_learned_cls = \<open>\<lambda>C (M, N, U, D, W). (M, N, add_mset C U, D, W)\<close> and
  remove_cls = \<open>\<lambda>C (M, N, U, D, W). (M, removeAll_mset C N, removeAll_mset C U, D, W)\<close> and
  update_conflicting = \<open>\<lambda>C (M, N, U, _, W). (M, N, U, C, W)\<close> and
  init_state = \<open>\<lambda>N. ([], N, {#}, None, None, ())\<close> and
  \<rho> = \<open>\<lambda>_. 0\<close> and
  update_additional_info = \<open>\<lambda>W (M, N, U, D, _, _). (M, N, U, D, W)\<close>
  by unfold_locales (auto simp: state\<^sub>W_ops.additional_info_def)

text \<open>
  We here formalise the encoding from a formula to another formula from which we will run derive the
  optimal partial model.

  There are a few difference compared to Dominik Zimmer's current draft:
  \<^item> We directly work on formula in CNF. So we need more variables and more formulas.
  \<^item> We use the version of the draft with the additional clause to make sure that a variable is either
    defined or undefined.

  The intended meaning is the following:
  \<^item> \<^term>\<open>\<Sigma>\<close> is the set of all variables
  \<^item> \<^term>\<open>\<Delta>\<Sigma>\<close> is the set of all variables with a non-zero weight: These are the variable that are
    replaced during preprocessing, but it does not matter if the weight 0.
\<close>

locale optimal_encoding_opt = conflict_driven_clause_learning\<^sub>W_optimal_weight
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
    \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
    \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

     \<comment> \<open>get state:\<close>
     init_state
     \<rho>
     update_additional_info
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
	'v clause option \<times> 'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  fixes \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v \<times> 'v\<close>
begin

abbreviation replacement_pos :: \<open>'v \<Rightarrow> 'v\<close> ("(_)\<^sup>\<mapsto>\<^sup>1" 100) where
  \<open>replacement_pos A \<equiv> (fst(new_vars A))\<close>

abbreviation replacement_neg :: \<open>'v \<Rightarrow> 'v\<close> ("(_)\<^sup>\<mapsto>\<^sup>0" 100) where
  \<open>replacement_neg A \<equiv> (fst(snd(new_vars A)))\<close>


abbreviation additional_atm :: \<open>'v \<Rightarrow> 'v\<close> where
  \<open>additional_atm A \<equiv> snd(snd(new_vars A))\<close>
abbreviation additional_var :: \<open>'v \<Rightarrow> 'v literal\<close> where
  \<open>additional_var A \<equiv> Pos (additional_atm A)\<close>


fun encode_lit where
  \<open>encode_lit (Pos A) = (if A \<in> \<Delta>\<Sigma> then Pos (replacement_pos A) else Pos A)\<close> |
  \<open>encode_lit (Neg A) = (if A \<in> \<Delta>\<Sigma> then Pos (replacement_neg A) else Neg A)\<close>

lemma encode_lit_alt_def:
  \<open>encode_lit A = (if atm_of A \<in> \<Delta>\<Sigma>
    then Pos (if is_pos A then replacement_pos (atm_of A) else replacement_neg (atm_of A))
    else A)\<close>
  by (cases A) auto

definition encode_clause :: \<open>'v clause \<Rightarrow> 'v clause\<close> where
  \<open>encode_clause C = encode_lit `# C\<close>

lemma encode_clause_simp[simp]:
  \<open>encode_clause {#} = {#}\<close>
  \<open>encode_clause (add_mset A C) = add_mset (encode_lit A) (encode_clause C)\<close>
  \<open>encode_clause (C + D) = encode_clause C + encode_clause D\<close>
  by (auto simp: encode_clause_def)

definition encode_clauses :: \<open>'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>encode_clauses C = encode_clause `# C\<close>

lemma encode_clauses_simp[simp]:
  \<open>encode_clauses {#} = {#}\<close>
  \<open>encode_clauses (add_mset A C) = add_mset (encode_clause A) (encode_clauses C)\<close>
  \<open>encode_clauses (C + D) = encode_clauses C + encode_clauses D\<close>
  by (auto simp: encode_clauses_def)

definition additional_constraint :: \<open>'v \<Rightarrow> 'v clauses\<close> where
  \<open>additional_constraint A =
     {#{#Neg (A\<^sup>\<mapsto>\<^sup>1), Pos A#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>1), additional_var A#},
       {#-additional_var A, -Pos A, Pos (A\<^sup>\<mapsto>\<^sup>1)#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>0), Neg A#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>0), additional_var A#},
       {#-additional_var A, -Neg A, Pos (A\<^sup>\<mapsto>\<^sup>0)#},
       {#Pos (A\<^sup>\<mapsto>\<^sup>0), Pos (A\<^sup>\<mapsto>\<^sup>1), -additional_var A#}#}\<close>

definition additional_constraints :: \<open>'v clauses\<close> where
  \<open>additional_constraints = \<Union>#(additional_constraint `# (mset_set \<Delta>\<Sigma>))\<close>

definition penc :: \<open>'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>penc N = encode_clauses N + additional_constraints\<close>

lemma size_encode_clauses[simp]: \<open>size (encode_clauses N) = size N\<close>
  by (auto simp: encode_clauses_def)

lemma size_penc:
  \<open>size (penc N) = size N + 7 * card \<Delta>\<Sigma>\<close>
  by (auto simp: penc_def additional_constraints_def
      additional_constraint_def size_Union_mset_image_mset)

lemma atms_of_mm_additional_constraints: \<open>finite \<Delta>\<Sigma> \<Longrightarrow>
   atms_of_mm additional_constraints = \<Delta>\<Sigma> \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>
      \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
  by (auto simp: additional_constraints_def additional_constraint_def atms_of_ms_def)

lemma atms_of_mm_encode_clause_subset:
  \<open>atms_of_mm (encode_clauses N) \<subseteq> (atms_of_mm N - \<Delta>\<Sigma>) \<union> replacement_pos ` {A \<in> \<Delta>\<Sigma>. A \<in> atms_of_mm N}
    \<union> replacement_neg ` {A \<in> \<Delta>\<Sigma>. A \<in> atms_of_mm N}\<close>
  by (auto simp: encode_clauses_def encode_lit_alt_def atms_of_ms_def atms_of_def
      encode_clause_def split: if_splits
      dest!: multi_member_split[of _ N])

text \<open>In every meaningful application of the theorem below, we have \<open>\<Delta>\<Sigma> \<subseteq> atms_of_mm N\<close>.\<close>
lemma atms_of_mm_penc_subset: \<open>finite \<Delta>\<Sigma> \<Longrightarrow>
  atms_of_mm (penc N) \<subseteq> atms_of_mm N \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>
      \<union> replacement_neg ` \<Delta>\<Sigma> \<union> \<Delta>\<Sigma>\<close>
  using atms_of_mm_encode_clause_subset[of N]
  by (auto simp: penc_def atms_of_mm_additional_constraints)

lemma atms_of_mm_encode_clause_subset2: \<open>finite \<Delta>\<Sigma> \<Longrightarrow> \<Delta>\<Sigma> \<subseteq> atms_of_mm N \<Longrightarrow>
  atms_of_mm N \<subseteq> atms_of_mm (encode_clauses N) \<union> \<Delta>\<Sigma>\<close>
  by (auto simp: encode_clauses_def encode_lit_alt_def atms_of_ms_def atms_of_def
      encode_clause_def split: if_splits
      dest!: multi_member_split[of _ N])

lemma atms_of_mm_penc_subset2: \<open>finite \<Delta>\<Sigma> \<Longrightarrow> \<Delta>\<Sigma> \<subseteq> atms_of_mm N \<Longrightarrow>
  atms_of_mm (penc N) = atms_of_mm N \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>
      \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
  using atms_of_mm_encode_clause_subset[of N] atms_of_mm_encode_clause_subset2[of N]
  by (auto simp: penc_def atms_of_mm_additional_constraints)

theorem card_atms_of_mm_penc:
  assumes \<open>finite \<Delta>\<Sigma>\<close> and
    \<open>\<Delta>\<Sigma> \<subseteq> atms_of_mm N\<close>
  shows \<open>card (atms_of_mm (penc N)) \<le> 4 * card (atms_of_mm N)\<close> (is \<open>?A \<le> ?B\<close>)
proof -
  have \<open>?A = card
     (atms_of_mm N \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union>
      replacement_neg ` \<Delta>\<Sigma>)\<close> (is \<open>_ = card (?W \<union> ?X \<union> ?Y \<union> ?Z)\<close>)
    using arg_cong[OF atms_of_mm_penc_subset2[of N], of card] assms
    using card_Un_le
    by auto
  also have \<open>... \<le> card (?W \<union> ?X \<union> ?Y) + card ?Z\<close>
    using card_Un_le[of \<open>?W \<union> ?X \<union> ?Y\<close> ?Z] by auto
  also have \<open>... \<le> card (?W \<union> ?X) + card ?Y + card ?Z\<close>
    using card_Un_le[of \<open>?W \<union> ?X\<close> ?Y] by auto
  also have \<open>... \<le> card ?W + card ?X + card ?Y + card ?Z\<close>
    using card_Un_le[of \<open>?W\<close> ?X] by auto
  also have \<open>... \<le>  4 * card (atms_of_mm N)\<close>
    using card_mono[of \<open>atms_of_mm N\<close> \<open>\<Delta>\<Sigma>\<close>] assms
      card_image_le[of \<Delta>\<Sigma> additional_atm]
      card_image_le[of \<Delta>\<Sigma> replacement_pos]
      card_image_le[of \<Delta>\<Sigma> replacement_neg]
    by auto
  finally show ?thesis .
qed

definition postp :: \<open>'v partial_interp \<Rightarrow> 'v partial_interp\<close> where
  \<open>postp I =
     {A \<in> I. atm_of A \<notin> \<Delta>\<Sigma> \<and> atm_of A \<in> \<Sigma>} \<union> {A \<in> I. atm_of A \<in> \<Delta>\<Sigma> \<and> additional_var (atm_of A) \<in> I}\<close>

lemma preprocess_clss_model_additional_variables:
  assumes \<open>I \<Turnstile>sm penc N\<close> and
    \<open>A \<in> \<Delta>\<Sigma>\<close> and
    \<open>finite \<Delta>\<Sigma>\<close> and
    cons: \<open>consistent_interp I\<close>
  shows
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<in>I \<longleftrightarrow> (additional_var A \<in> I \<and> Pos A \<in> I)\<close> (is ?A) and
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>0) \<in>I \<longleftrightarrow> (additional_var A \<in> I \<and> Neg A \<in> I)\<close> (is ?B)
proof -
  have H: \<open>A \<in> I \<Longrightarrow> -A \<notin> I\<close> for A
    using assms cons by (auto simp: consistent_interp_def)
  show ?A ?B
    using assms H[of \<open>Pos A\<close>] H[of \<open>Neg A\<close>] H[of \<open>Pos (A\<^sup>\<mapsto>\<^sup>1)\<close>]  H[of \<open>Neg (A\<^sup>\<mapsto>\<^sup>1)\<close>]
      H[of \<open>Neg (additional_atm A)\<close>] H[of \<open>Pos (additional_atm A)\<close>]
      H[of \<open>Pos (A\<^sup>\<mapsto>\<^sup>0)\<close>]  H[of \<open>Neg (A\<^sup>\<mapsto>\<^sup>0)\<close>]
    by (auto simp: penc_def additional_constraints_def true_clss_def
        additional_constraint_def ball_Un)
qed

lemma preprocess_clss_model_additional_variables2:
  assumes
    \<open>atm_of A \<in> \<Sigma> - \<Delta>\<Sigma>\<close>
  shows
    \<open>A \<in> postp I \<longleftrightarrow> A \<in> I\<close> (is ?A)
proof -
  show ?A
    using assms
    by (auto simp: postp_def)
qed

lemma encode_clause_iff:
  assumes
    \<open>\<And>A. A \<in> \<Delta>\<Sigma> \<Longrightarrow> Pos A \<in> I \<longleftrightarrow> Pos (replacement_pos A) \<in> I\<close>
    \<open>\<And>A. A \<in> \<Delta>\<Sigma> \<Longrightarrow> Neg A \<in> I \<longleftrightarrow> Pos (replacement_neg A) \<in> I\<close>
  shows \<open>I \<Turnstile> encode_clause C \<longleftrightarrow> I \<Turnstile> C\<close>
  using assms
  apply (induction C)
  subgoal by auto
  subgoal for A C
    by (cases A)
      (auto simp: encode_clause_def encode_lit_alt_def split: if_splits)
  done

lemma encode_clauses_iff:
  assumes
    \<open>\<And>A. A \<in> \<Delta>\<Sigma> \<Longrightarrow> Pos A \<in> I \<longleftrightarrow> Pos (replacement_pos A) \<in> I\<close>
    \<open>\<And>A. A \<in> \<Delta>\<Sigma> \<Longrightarrow> Neg A \<in> I \<longleftrightarrow> Pos (replacement_neg A) \<in> I\<close>
  shows \<open>I \<Turnstile>m encode_clauses C \<longleftrightarrow> I \<Turnstile>m C\<close>
  using encode_clause_iff[OF assms]
  by (auto simp: encode_clauses_def true_cls_mset_def)


definition \<Sigma>\<^sub>a\<^sub>d\<^sub>d where
  \<open>\<Sigma>\<^sub>a\<^sub>d\<^sub>d = replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma> \<union> additional_atm ` \<Delta>\<Sigma>\<close>


definition upostp :: \<open>'v partial_interp \<Rightarrow> 'v partial_interp\<close> where
  \<open>upostp I =
     Neg ` {A \<in> \<Sigma>. Pos A \<notin> I \<and> Neg A \<notin> I}
     \<union> {A \<in> I. atm_of A \<in> \<Sigma>}
     \<union> Neg ` additional_atm ` {A \<in> \<Delta>\<Sigma>. Pos A \<notin> I \<and> Neg A \<notin> I}
     \<union> Pos ` additional_atm ` {A \<in> \<Delta>\<Sigma>. Pos A \<in> I \<or> Neg A \<in> I}
     \<union> Pos ` replacement_pos ` {A \<in> \<Delta>\<Sigma>. Pos A \<in> I}
     \<union> Neg ` replacement_pos ` {A \<in> \<Delta>\<Sigma>. Pos A \<notin> I}
     \<union> Pos ` replacement_neg ` {A \<in> \<Delta>\<Sigma>. Neg A \<in> I}
     \<union> Neg ` replacement_neg ` {A \<in> \<Delta>\<Sigma>. Neg A \<notin> I}\<close>

lemma atm_of_upostp_subset:
  \<open>atm_of ` (upostp I) \<subseteq>
    atm_of ` I \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union>
    replacement_neg ` \<Delta>\<Sigma> \<union> \<Sigma>\<close>
  by (auto simp: upostp_def image_Un)

lemma atm_of_upostp_subset2:
  \<open>atm_of ` I \<subseteq> \<Sigma> \<Longrightarrow> atm_of ` I \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union>
    replacement_neg ` \<Delta>\<Sigma> \<union> \<Sigma> \<subseteq> atm_of ` (upostp I)
    \<close>
  apply (auto simp: upostp_def image_Un image_image)
   apply (metis (mono_tags, lifting) imageI literal.sel(1) mem_Collect_eq)
  apply (metis (mono_tags, lifting) imageI literal.sel(2) mem_Collect_eq)
  done

inductive odecide :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
  odecide_noweight: \<open>odecide S T\<close>
if
  \<open>conflicting S = None\<close> and
  \<open>undefined_lit (trail S) L\<close> and
  \<open>atm_of L \<in> atms_of_mm (init_clss S)\<close> and
  \<open>T \<sim> cons_trail (Decided L) S\<close> and
  \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma>\<close> |
  odecide_additional_var: \<open>odecide S T\<close>
if
  \<open>conflicting S = None\<close> and
  \<open>undefined_lit (trail S) (Neg (additional_atm L))\<close> and
  \<open>L \<in> atms_of_mm (init_clss S)\<close> and
  \<open>T \<sim> cons_trail (Decided (Neg (additional_atm L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close> |
  odecide_replacement_pos: \<open>odecide S T\<close>
if
  \<open>conflicting S = None\<close> and
  \<open>undefined_lit (trail S) (Pos (replacement_pos L))\<close> and
  \<open>L \<in> atms_of_mm (init_clss S)\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_pos L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close> |
  odecide_replacement_neg: \<open>odecide S T\<close>
if
  \<open>conflicting S = None\<close> and
  \<open>undefined_lit (trail S) (Pos (replacement_neg L))\<close> and
  \<open>L \<in> atms_of_mm (init_clss S)\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_neg L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close>

inductive_cases odecideE: \<open>odecide S T\<close>

definition no_new_lonely_clause :: \<open>'v clause \<Rightarrow> bool\<close> where
  \<open>no_new_lonely_clause C \<longleftrightarrow>
    (\<forall>L \<in> \<Delta>\<Sigma>. L \<in> atms_of C \<longrightarrow>
      Neg (replacement_pos L) \<in># C \<or> Neg (replacement_neg L) \<in># C \<or> C \<in># additional_constraint L)\<close>

definition no_lonely_weighted_lit_cls :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>no_lonely_weighted_lit_cls C \<longleftrightarrow>
    (\<forall>L \<in> \<Delta>\<Sigma>. L \<in> atms_of C \<longrightarrow>
      (Neg (replacement_pos L) \<in># C \<or> (- additional_var L \<in># C \<and> Pos (replacement_neg L) \<in># C)) \<or>
       Neg (replacement_neg L) \<in># C \<or> (- additional_var L \<in># C \<and> Pos (replacement_pos L) \<in># C))\<close>

definition no_lonely_weighted_lit :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>no_lonely_weighted_lit S \<longleftrightarrow>
    (conflicting S \<noteq> None \<longrightarrow> no_lonely_weighted_lit_cls (the (conflicting S))) \<and>
    (\<forall>C \<in># clauses S. no_lonely_weighted_lit_cls C)\<close>

definition lonely_weighted_lit_decided where
  \<open>lonely_weighted_lit_decided S \<longleftrightarrow>
    (\<forall>L \<in> \<Delta>\<Sigma>. Decided (Pos L) \<notin> set (trail S) \<and> Decided (Neg L) \<notin> set (trail S))\<close>

end


locale optimal_encoding = optimal_encoding_opt
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
    \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
    \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

    \<comment> \<open>get state:\<close>
    init_state
    \<rho>
    update_additional_info
    \<Sigma> \<Delta>\<Sigma>
    new_vars
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
	'v clause option \<times> 'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and
    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v \<times> 'v\<close> +
  assumes
    finite_\<Sigma>:
    \<open>finite \<Delta>\<Sigma>\<close> and
    \<Delta>\<Sigma>_\<Sigma>:
    \<open>\<Delta>\<Sigma> \<subseteq> \<Sigma>\<close> and
    new_vars_pos:
    \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_pos A \<notin> \<Sigma>\<close> and
    new_vars_neg:
    \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_neg A \<notin> \<Sigma>\<close> and
    new_vars_addition_var:
    \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> additional_atm A \<notin> \<Sigma>\<close> and
    new_vars_dist:
    \<open>inj_on replacement_pos \<Delta>\<Sigma>\<close>
    \<open>inj_on replacement_neg \<Delta>\<Sigma>\<close>
    \<open>inj_on additional_atm \<Delta>\<Sigma>\<close>
    \<open>replacement_pos ` \<Delta>\<Sigma> \<inter> replacement_neg ` \<Delta>\<Sigma> = {}\<close>
    \<open>replacement_pos ` \<Delta>\<Sigma> \<inter> additional_atm ` \<Delta>\<Sigma> = {}\<close>
    \<open>replacement_neg ` \<Delta>\<Sigma> \<inter> additional_atm ` \<Delta>\<Sigma> = {}\<close> and
    \<Sigma>_no_weight:
    \<open>atm_of C \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> \<rho> (add_mset C M) = \<rho> M\<close>
begin


lemma new_vars_dist2:
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_pos A \<noteq> replacement_pos B\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_neg A \<noteq> replacement_neg B\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> A \<noteq> B \<Longrightarrow> additional_atm A \<noteq> additional_atm B\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_neg A \<noteq> replacement_pos B\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_pos A \<noteq> additional_atm B\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_neg A \<noteq> additional_atm B\<close>
  using new_vars_dist unfolding inj_on_def apply blast
  using new_vars_dist unfolding inj_on_def apply blast
  using new_vars_dist unfolding inj_on_def apply blast
  using new_vars_dist unfolding inj_on_def apply blast
  using new_vars_dist unfolding inj_on_def apply fast
  using new_vars_dist unfolding inj_on_def apply fast
  done

lemma consistent_interp_postp:
  \<open>consistent_interp I \<Longrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def)

text \<open>The reverse of the previous theorem does not hold due to the filtering on the variables of
  \<^term>\<open>\<Delta>\<Sigma>\<close>. One example of version that holds:\<close>
lemma
  assumes \<open>A \<in> \<Delta>\<Sigma>\<close>
  shows \<open>consistent_interp (postp {Pos A , Neg A})\<close> and
    \<open>\<not>consistent_interp {Pos A, Neg A}\<close>
  using assms \<Delta>\<Sigma>_\<Sigma>
  using new_vars_addition_var
  by (auto simp: consistent_interp_def postp_def uminus_lit_swap)

text \<open>Some more restricted version of the reverse hold, like:\<close>
lemma consistent_interp_postp_iff:
  \<open>atm_of ` I \<subseteq> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> consistent_interp I \<longleftrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def)

lemma new_vars_different_iff[simp]:
  \<open>A \<noteq> x\<^sup>\<mapsto>\<^sup>1\<close>
  \<open>A \<noteq> x\<^sup>\<mapsto>\<^sup>0\<close>
  \<open>x\<^sup>\<mapsto>\<^sup>1 \<noteq> A\<close>
  \<open>x\<^sup>\<mapsto>\<^sup>0 \<noteq> A\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>0 \<noteq> x\<^sup>\<mapsto>\<^sup>1\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>1 \<noteq> x\<^sup>\<mapsto>\<^sup>0\<close>
  \<open>x \<noteq> additional_atm x\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>0 \<noteq> additional_atm x\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>1 \<noteq> additional_atm x\<close>
  \<open>additional_atm x \<noteq> x\<close>
  \<open>additional_atm x \<noteq> A\<^sup>\<mapsto>\<^sup>0\<close>
  \<open>additional_atm x \<noteq> A\<^sup>\<mapsto>\<^sup>1\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>0 = x\<^sup>\<mapsto>\<^sup>0 \<longleftrightarrow> A = x\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>1 = x\<^sup>\<mapsto>\<^sup>1 \<longleftrightarrow> A = x\<close>
  \<open>additional_atm A = additional_atm x \<longleftrightarrow> A = x\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>1) \<notin> \<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>0) \<notin> \<Sigma>\<close>
  \<open>additional_atm A \<notin> \<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>1) \<notin> \<Delta>\<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>0) \<notin> \<Delta>\<Sigma>\<close>
  \<open>additional_atm A \<notin> \<Delta>\<Sigma>\<close>
  if \<open>A \<in> \<Delta>\<Sigma>\<close>  \<open>x \<in> \<Delta>\<Sigma>\<close> for A x
  using \<Delta>\<Sigma>_\<Sigma> new_vars_pos[of x] new_vars_pos[of A]  new_vars_neg[of x] new_vars_neg[of A]
    new_vars_neg new_vars_dist2[of A x] new_vars_dist2[of x A]
    new_vars_addition_var[of x] new_vars_addition_var[of A] that new_vars_addition_var[of x]
  by (cases \<open>A = x\<close>; fastforce simp: comp_def; fail)+

lemma consistent_interp_upostp:
  \<open>consistent_interp I \<Longrightarrow> consistent_interp (upostp I)\<close>
  using \<Delta>\<Sigma>_\<Sigma>
  using new_vars_addition_var
  by (auto simp: consistent_interp_def upostp_def uminus_lit_swap)

lemma upostp_additional_constraints_logic:
  assumes
    \<open>A \<in> \<Delta>\<Sigma>\<close>
  shows
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<in> upostp I \<longleftrightarrow> (additional_var A \<in> upostp I \<and> Pos A \<in> upostp I)\<close> (is ?A) and
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>0) \<in> upostp I \<longleftrightarrow> (additional_var A \<in> upostp I \<and> Neg A \<in> upostp I)\<close> (is ?B)
proof -
  show ?A
  proof
    assume \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<in> upostp I\<close>
    then have \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<in> (\<lambda>x. Pos (x\<^sup>\<mapsto>\<^sup>1)) ` {A \<in> \<Delta>\<Sigma>. Pos A \<in> I}\<close>
      using assms
      by (auto simp add: upostp_def image_image)
    then have \<open>Pos A \<in> I\<close>
      using assms
      by auto
    moreover have \<open>additional_var A \<in> upostp I\<close>
      using assms \<open>Pos A \<in> I\<close>
      by (auto simp add: upostp_def image_image)
    moreover have \<open>Pos A \<in> upostp I\<close>
      using \<Delta>\<Sigma>_\<Sigma> assms \<open>Pos A \<in> I\<close>
      by (auto simp add: upostp_def image_image)
    ultimately show \<open>additional_var A \<in> upostp I \<and> Pos A \<in> upostp I\<close>
      by auto
  next
    assume \<open>additional_var A \<in> upostp I \<and> Pos A \<in> upostp I\<close>
    then have \<open>Pos A \<in> I\<close>
      using assms
      by (auto simp add: upostp_def image_image)
    then show \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<in> upostp I\<close>
      using assms
      by (auto simp add: upostp_def image_image)
  qed

  show ?B
    using assms \<Delta>\<Sigma>_\<Sigma>
    by (auto simp add: upostp_def image_image)
qed

lemma penc_ent_upostp:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>I \<Turnstile>sm N\<close> and
    cons: \<open>consistent_interp I\<close> and
    atm: \<open>atm_of ` I \<subseteq> atms_of_mm N\<close>
  shows \<open>upostp I \<Turnstile>m penc N\<close>
proof -
  have [iff]: \<open>Pos (A\<^sup>\<mapsto>\<^sup>0) \<notin> I\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<notin> I\<close> \<open>additional_var A \<notin> I\<close> \<open>Neg (additional_atm A) \<notin> I\<close>
    \<open>Neg (A\<^sup>\<mapsto>\<^sup>0) \<notin> I\<close> \<open>Neg (A\<^sup>\<mapsto>\<^sup>1) \<notin> I\<close>  if \<open>A \<in> \<Delta>\<Sigma>\<close> for A
    using atm new_vars_neg[of A] new_vars_pos[of A] that new_vars_addition_var[of A]
    unfolding \<Sigma> by force+
  have enc: \<open>upostp I \<Turnstile>m encode_clauses N\<close>
    unfolding true_cls_mset_def
  proof
    fix C
    assume \<open>C \<in># encode_clauses N\<close>
    then obtain C' where
      \<open>C' \<in># N\<close> and
      \<open>C = encode_clause C'\<close>
      by (auto simp: encode_clauses_def)
    then obtain A where
      \<open>A \<in># C'\<close> and
      \<open>A \<in> I\<close>
      using sat
      by (auto simp: true_cls_def
          dest!: multi_member_split[of _ N])
    moreover have \<open>atm_of A \<in> \<Sigma> - \<Delta>\<Sigma> \<or> atm_of A \<in> \<Delta>\<Sigma>\<close>
      using atm \<open>A \<in> I\<close> unfolding \<Sigma> by blast
    ultimately have \<open>encode_lit A \<in> upostp I\<close>
      by (auto simp: encode_lit_alt_def upostp_def)
    then show \<open>upostp I \<Turnstile> C\<close>
      using \<open>A \<in># C'\<close>
      unfolding \<open>C = encode_clause C'\<close>
      by (auto simp: encode_clause_def dest: multi_member_split)
  qed
  have [iff]: \<open>Pos (y\<^sup>\<mapsto>\<^sup>1) \<notin> upostp I \<longleftrightarrow> Neg (y\<^sup>\<mapsto>\<^sup>1) \<in> upostp I\<close>
    \<open>Pos (y\<^sup>\<mapsto>\<^sup>0) \<notin> upostp I \<longleftrightarrow> Neg (y\<^sup>\<mapsto>\<^sup>0) \<in> upostp I\<close>
    \<open>Neg (additional_atm y) \<notin> upostp I \<longleftrightarrow> additional_var y \<in> upostp I\<close>
    if \<open>y \<in> \<Delta>\<Sigma>\<close> for y
    using that
    by (cases \<open>Pos y \<in> I\<close>; auto simp: upostp_def image_image; fail)+
  have H:
    \<open>Pos y \<notin> upostp I \<longleftrightarrow> Neg y \<in> upostp I\<close>
    if \<open>y \<in> \<Delta>\<Sigma>\<close> for y
    using that cons \<Delta>\<Sigma>_\<Sigma> unfolding consistent_interp_def
    using that by (cases \<open>Pos y \<in> I\<close>; auto simp: upostp_def image_image)
  have [dest]: \<open>Neg A \<in> upostp I \<Longrightarrow> Pos A \<notin> upostp I\<close>
    \<open>Pos A \<in> upostp I \<Longrightarrow> Neg A \<notin> upostp I\<close> for A
    using consistent_interp_upostp[OF cons]
    by (auto simp: consistent_interp_def)

  have add: \<open>upostp I \<Turnstile>m additional_constraints\<close>
    using finite_\<Sigma>
    apply (auto simp: additional_constraints_def true_cls_mset_def additional_constraint_def)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I] H[of y]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I] H[of y]
      by (auto simp: image_image consistent_interp_def)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I] H[of y]
      by (auto simp: image_image consistent_interp_def)
    done

  show \<open>upostp I \<Turnstile>m penc N\<close>
    using enc add unfolding penc_def by auto
qed

lemma satisfiable_penc:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>satisfiable (set_mset N)\<close>
  shows \<open>satisfiable (set_mset (penc N))\<close>
  using assms
  apply (subst (asm) satisfiable_def_min)
  apply clarify
  subgoal for I
    using penc_ent_upostp[of N I] consistent_interp_upostp[of I]
    by auto
  done

lemma penc_ent_postp:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>I \<Turnstile>sm penc N\<close> and
    cons: \<open>consistent_interp I\<close>
  shows \<open>postp I \<Turnstile>m N\<close>
proof -
  have enc: \<open>I \<Turnstile>m encode_clauses N\<close> and \<open>I \<Turnstile>m additional_constraints\<close>
    using sat unfolding penc_def
    by auto

  show \<open>postp I \<Turnstile>m N\<close>
    unfolding true_cls_mset_def
  proof
    fix C
    assume \<open>C \<in># N\<close>
    then have \<open>I \<Turnstile> encode_clause C\<close>
      using enc by (auto dest!: multi_member_split)
    then show \<open>postp I \<Turnstile> C\<close>
      unfolding true_cls_def
      using cons finite_\<Sigma> preprocess_clss_model_additional_variables[of I N] sat
        preprocess_clss_model_additional_variables2[of _ I]
        \<Sigma> \<open>C \<in># N\<close> in_m_in_literals
      apply (auto simp: encode_clause_def postp_def encode_lit_alt_def
          split: if_splits
          dest!: multi_member_split[of _ C])
      by blast (*TODO proof*)
  qed
qed

lemma satisfiable_penc_satisfiable:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>satisfiable (set_mset (penc N))\<close>
  shows \<open>satisfiable (set_mset N)\<close>
  using assms apply (subst (asm) satisfiable_def)
  apply clarify
  subgoal for I
    using penc_ent_postp[OF \<Sigma>, of I] consistent_interp_postp[of I]
    by auto
  done

lemma satisfiable_penc_iff:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close>
  shows \<open>satisfiable (set_mset (penc N)) \<longleftrightarrow> satisfiable (set_mset N)\<close>
  using assms satisfiable_penc satisfiable_penc_satisfiable by blast


abbreviation \<rho>\<^sub>e_filter :: \<open>'v literal multiset \<Rightarrow> 'v literal multiset\<close> where
  \<open>\<rho>\<^sub>e_filter M \<equiv> filter_mset (\<lambda>x. atm_of x \<in> \<Delta>\<Sigma> \<and> additional_var (atm_of x) \<in># M) M\<close>

definition \<rho>\<^sub>e :: \<open>'v literal multiset \<Rightarrow> 'a :: {linorder}\<close> where
  \<open>\<rho>\<^sub>e M = \<rho> (\<rho>\<^sub>e_filter M)\<close>

lemma \<rho>\<^sub>e_mono: \<open>consistent_interp (set_mset B) \<Longrightarrow> distinct_mset B \<Longrightarrow> A \<subseteq># B \<Longrightarrow> \<rho>\<^sub>e A \<le> \<rho>\<^sub>e B\<close>
  unfolding \<rho>\<^sub>e_def
  apply (rule \<rho>_mono)
  subgoal by (auto intro: consistent_interp_subset)
  subgoal
    by (rule distinct_mset_mono[of _ B]) auto
  subgoal
    by (rule filter_mset_mono_subset) auto
  done


interpretation enc_weight_opt: conflict_driven_clause_learning\<^sub>W_optimal_weight where
  state_eq = state_eq and
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state and
  \<rho> = \<rho>\<^sub>e and
  update_additional_info = update_additional_info
  apply unfold_locales
  subgoal by (rule \<rho>\<^sub>e_mono)
  subgoal using update_additional_info by fast
  subgoal using weight_init_state by fast
  done

lemma \<Sigma>_no_weight_\<rho>\<^sub>e: \<open>atm_of C \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> \<rho>\<^sub>e (add_mset C M) = \<rho>\<^sub>e M\<close>
  using \<Sigma>_no_weight[of C \<open>\<rho>\<^sub>e_filter M\<close>]
  apply (auto simp: \<rho>\<^sub>e_def)
  by (metis (no_types, lifting) literal.sel(1) new_vars_addition_var)


lemma \<rho>_cancel_notin_\<Delta>\<Sigma>:
  \<open>(\<And>x. x \<in># M \<Longrightarrow> atm_of x \<in> \<Sigma> - \<Delta>\<Sigma>) \<Longrightarrow> \<rho> (M + M') = \<rho> M'\<close>
  by (induction M) (auto simp: \<Sigma>_no_weight)

lemma \<rho>_mono2:
  \<open>consistent_interp (set_mset M') \<Longrightarrow> distinct_mset M' \<Longrightarrow>
   (\<And>A. A \<in># M \<Longrightarrow> atm_of A \<in> \<Sigma>) \<Longrightarrow> (\<And>A. A \<in># M' \<Longrightarrow> atm_of A \<in> \<Sigma>) \<Longrightarrow>
     {#A \<in># M. atm_of A \<in> \<Delta>\<Sigma>#} \<subseteq># {#A \<in># M'. atm_of A \<in> \<Delta>\<Sigma>#} \<Longrightarrow> \<rho> M \<le> \<rho> M'\<close>
  apply (subst (2) multiset_partition[of _ \<open>\<lambda>A. atm_of A \<notin> \<Delta>\<Sigma>\<close>])
  apply (subst multiset_partition[of _ \<open>\<lambda>A. atm_of A \<notin> \<Delta>\<Sigma>\<close>])
  apply (subst \<rho>_cancel_notin_\<Delta>\<Sigma>)
  subgoal by auto
  apply (subst \<rho>_cancel_notin_\<Delta>\<Sigma>)
  subgoal by auto
  by (auto intro!: \<rho>_mono intro: consistent_interp_subset intro!: distinct_mset_mono[of _ M'])

lemma finite_upostp: \<open>finite I  \<Longrightarrow> finite \<Sigma> \<Longrightarrow> finite (upostp I)\<close>
  using finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
  by (auto simp: upostp_def)

lemma \<rho>\<^sub>e_upostp_\<rho>:
  assumes [simp]: \<open>finite \<Sigma>\<close> and
    \<open>finite I\<close> and
    cons: \<open>consistent_interp I\<close> and
    I_\<Sigma>: \<open>atm_of ` I \<subseteq> \<Sigma>\<close>
  shows \<open>\<rho>\<^sub>e (mset_set (upostp I)) = \<rho> (mset_set I)\<close> (is \<open>?A = ?B\<close>)
proof -
  have [simp]: \<open>finite I\<close>
    using assms by auto
  have [simp]: \<open>mset_set
	{x \<in> I.
	 atm_of x \<in> \<Sigma> \<and>
	 atm_of x \<notin> replacement_pos ` \<Delta>\<Sigma> \<and>
	 atm_of x \<notin> replacement_neg ` \<Delta>\<Sigma> \<and> atm_of x \<notin> additional_atm ` \<Delta>\<Sigma>} = mset_set I\<close>
    using I_\<Sigma> by auto
  have [simp]: \<open>finite {A \<in> \<Delta>\<Sigma>. P A}\<close> for P
    by (rule finite_subset[of _ \<Delta>\<Sigma>])
      (use \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> in auto)
  have \<open>?A \<le> ?B\<close>
    using assms \<Delta>\<Sigma>_\<Sigma> apply -
    unfolding \<rho>\<^sub>e_def filter_filter_mset
    apply (rule \<rho>_mono2)
    subgoal using cons by auto
    subgoal using distinct_mset_mset_set by auto
    subgoal by auto
    subgoal by auto
    apply (rule filter_mset_mono_subset)
    subgoal by  (auto simp: upostp_def)
    subgoal for x
      by (cases \<open>x \<in> I\<close>; cases x) (auto simp: upostp_def)
    done
  moreover have \<open>?B \<le> ?A\<close>
    using assms \<Delta>\<Sigma>_\<Sigma> apply -
    unfolding \<rho>\<^sub>e_def filter_filter_mset
    apply (rule \<rho>_mono2)
    subgoal using cons by (auto intro: consistent_interp_subset[of _ \<open>upostp I\<close>]
      simp: consistent_interp_upostp finite_upostp)
    subgoal by (auto intro: distinct_mset_mono[of _ \<open>mset_set (upostp I)\<close>]
      simp: distinct_mset_mset_set)
    subgoal by auto
    subgoal by auto
    unfolding filter_filter_mset
    apply (rule filter_mset_mono_subset)
    subgoal by  (auto simp: upostp_def)
    subgoal for x
      by (cases \<open>x \<in> I\<close>; cases x) (auto simp: upostp_def)
    done
  ultimately show ?thesis
    by simp
qed


lemma \<rho>_postp_\<rho>\<^sub>e:
  assumes \<open>finite \<Sigma>\<close> and
    \<open>finite I\<close> and
    \<open>consistent_interp I\<close> and
    I_\<Sigma>: \<open>atm_of ` I \<subseteq> \<Sigma> \<union> \<Sigma>\<^sub>a\<^sub>d\<^sub>d\<close>
  shows \<open>\<rho>\<^sub>e (mset_set I) \<ge> \<rho> (mset_set (postp I))\<close>
proof -
  have [simp]: \<open>finite I\<close>
    using assms by auto
  have [simp]: \<open>finite {A \<in> I. P A}\<close> for P
    apply (rule finite_subset[of _ \<open>Pos ` atm_of ` I \<union> Neg ` atm_of ` I\<close>])
     apply auto
    by (metis image_iff literal.exhaust_sel)

  show ?thesis
    using assms \<Delta>\<Sigma>_\<Sigma>
    by (auto simp: postp_def \<rho>\<^sub>e_def \<Sigma>\<^sub>a\<^sub>d\<^sub>d_def conj_disj_distribR
        mset_set_Union intro!: \<rho>_mono2
        intro: consistent_interp_subset distinct_mset_mset_set)
qed

lemma encode_lit_eq_iff:
  \<open>atm_of x \<in> \<Sigma> \<Longrightarrow> atm_of y \<in> \<Sigma> \<Longrightarrow> encode_lit x = encode_lit y \<longleftrightarrow> x = y\<close>
  by (cases x; cases y) (auto simp: encode_lit_alt_def atm_of_eq_atm_of)

lemma distinct_mset_encode_clause_iff:
  \<open>atms_of N \<subseteq> \<Sigma> \<Longrightarrow> distinct_mset (encode_clause N) \<longleftrightarrow> distinct_mset N\<close>
  by (induction N)
    (auto simp: encode_clause_def encode_lit_eq_iff
      dest!: multi_member_split)

lemma distinct_mset_encodes_clause_iff:
  \<open>atms_of_mm N \<subseteq> \<Sigma> \<Longrightarrow> distinct_mset_mset (encode_clauses N) \<longleftrightarrow> distinct_mset_mset N\<close>
  by (induction N)
    (auto simp: encode_clauses_def distinct_mset_encode_clause_iff)

lemma distinct_additional_constraints[simp]:
  \<open>distinct_mset_mset additional_constraints\<close>
  by (auto simp: additional_constraints_def additional_constraint_def
      distinct_mset_set_def finite_\<Sigma>)

lemma distinct_mset_penc:
  \<open>atms_of_mm N \<subseteq> \<Sigma> \<Longrightarrow> distinct_mset_mset (penc N) \<longleftrightarrow> distinct_mset_mset N\<close>
  by (auto simp: penc_def
      distinct_mset_encodes_clause_iff)

lemma finite_postp: \<open>finite I \<Longrightarrow> finite (postp I)\<close>
  by (auto simp: postp_def)

theorem full_encoding_OCDCL_correctness:
  assumes
    st: \<open>full enc_weight_opt.cdcl_bab_stgy (init_state (penc N)) T\<close> and
    dist: \<open>distinct_mset_mset N\<close> and
    atms: \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> postp (set_mset (the (weight T))) \<Turnstile>sm N\<close>
    \<open>weight T \<noteq> None \<Longrightarrow> distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow>
      atms_of I \<subseteq> atms_of_mm N \<Longrightarrow> set_mset I \<Turnstile>sm N \<Longrightarrow>
      \<rho> I \<ge> \<rho> (mset_set (postp (set_mset (the (weight T)))))\<close>
proof -
  let ?N = \<open>penc N\<close>
  have \<open>distinct_mset_mset (penc N)\<close>
    by (subst distinct_mset_penc)
      (use dist atms in auto)
  then have
    unsat: \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset ?N)\<close> and
    model: \<open>weight T \<noteq> None \<Longrightarrow> consistent_interp (set_mset (the (weight T))) \<and>
       atms_of (the (weight T)) \<subseteq> atms_of_mm ?N \<and> set_mset (the (weight T)) \<Turnstile>sm ?N \<and>
       distinct_mset (the (weight T))\<close> and
    opt: \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm ?N \<Longrightarrow>
      set_mset I \<Turnstile>sm ?N \<Longrightarrow> Some (\<rho>\<^sub>e I) \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
    for I
    using enc_weight_opt.full_cdcl_bab_stgy_no_conflicting_clause_from_init_state[of
        \<open>penc N\<close> T, OF st]
    by fast+

  show \<open>unsatisfiable (set_mset N)\<close> if \<open>weight T = None\<close>
    using unsat[OF that] satisfiable_penc[OF atms] by blast
  let ?K = \<open>postp (set_mset (the (weight T)))\<close>
  show \<open>?K \<Turnstile>sm N\<close> if \<open>weight T \<noteq> None\<close>
    using penc_ent_postp[OF atms, of \<open>set_mset (the (weight T))\<close>] model[OF that]
    by auto
  show \<open>\<rho> I \<ge> \<rho> (mset_set ?K)\<close>
    if Some: \<open>weight T \<noteq> None\<close> and
      dist: \<open>distinct_mset I\<close> and
      cons: \<open>consistent_interp (set_mset I)\<close> and
      atm: \<open>atms_of I \<subseteq> atms_of_mm N\<close> and
      I_N: \<open>set_mset I \<Turnstile>sm N\<close>
  proof -
    let ?I = \<open>mset_set (upostp (set_mset I))\<close>
    have Some': \<open>enc_weight_opt.weight T \<noteq> None\<close>
      using Some by auto
    have [simp]: \<open>finite (upostp (set_mset I))\<close>
      by (rule finite_upostp)
        (use atms in auto)
    then have I: \<open>set_mset ?I = upostp (set_mset I)\<close>
      by auto
    have \<open>set_mset ?I \<Turnstile>m ?N\<close>
      unfolding I
      by (rule penc_ent_upostp[OF atms I_N cons])
        (use atm in \<open>auto dest: multi_member_split\<close>)
    moreover have \<open>distinct_mset ?I\<close>
      by (rule distinct_mset_mset_set)
    moreover {
      have A: \<open>atms_of (mset_set (upostp (set_mset I))) = atm_of ` (upostp (set_mset I))\<close>
        \<open>atm_of ` set_mset I = atms_of I\<close>
        by (auto simp: atms_of_def)
      have \<open>atms_of ?I = atms_of_mm ?N\<close>
        apply (subst atms_of_mm_penc_subset2[OF finite_\<Sigma>])
        subgoal using \<Delta>\<Sigma>_\<Sigma> atms by auto
        subgoal
          using atm_of_upostp_subset[of \<open>set_mset I\<close>] atm_of_upostp_subset2[of \<open>set_mset I\<close>] atm
          unfolding atms A
          by auto
        done
    }
    moreover have cons': \<open>consistent_interp (set_mset ?I)\<close>
      using cons unfolding I by (rule consistent_interp_upostp)
    ultimately have \<open>Some (\<rho>\<^sub>e ?I) \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
      using opt[of ?I] by auto
    moreover {
      have \<open>\<rho>\<^sub>e ?I = \<rho> (mset_set (set_mset I))\<close>
        by (rule \<rho>\<^sub>e_upostp_\<rho>)
          (use \<Delta>\<Sigma>_\<Sigma> atms atm cons in \<open>auto dest: multi_member_split\<close>)
      then have \<open>\<rho>\<^sub>e ?I = \<rho> I\<close>
        by (subst (asm) distinct_mset_set_mset_ident)
          (use atms dist in auto)
    }
    ultimately have \<open>Some (\<rho> I) \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
      using Some'
      by auto
    moreover {
      have \<open>\<rho> (mset_set ?K) \<le> \<rho>\<^sub>e (the (weight T))\<close>
        unfolding \<rho>\<^sub>e_def
        apply (rule \<rho>_mono2)
        subgoal using model Some' by (auto intro: consistent_interp_subset)
        subgoal using model Some' by (auto intro: distinct_mset_mono[of _ \<open>the (weight T)\<close>])
        subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
        subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
        subgoal
          unfolding filter_filter_mset
          apply (rule filter_mset_mono_subset)
          subgoal
            apply (subst distinct_subseteq_iff[symmetric])
            using dist model[OF Some]
            by (auto simp: postp_def distinct_mset_mset_set)
          subgoal by (auto simp: postp_def)
          done
        done
      then have \<open>Some (\<rho> (mset_set ?K)) \<le> enc_weight_opt.\<rho>' (weight T)\<close>
        using Some by auto
    }
    moreover {
      have \<open>\<rho>\<^sub>e (mset_set ?K) \<le> \<rho>\<^sub>e (mset_set (set_mset (the (weight T))))\<close>
        unfolding \<rho>\<^sub>e_def
        apply (rule \<rho>_mono2)
        subgoal using model Some' by (auto intro: consistent_interp_subset)
        subgoal using model Some' by (auto intro: distinct_mset_mono[of _ \<open>the (weight T)\<close>])
        subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
        subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
        subgoal
          unfolding filter_filter_mset
          apply (rule filter_mset_mono_subset)
          by (auto simp: postp_def)
        done
      then have \<open>Some (\<rho>\<^sub>e (mset_set ?K)) \<le> enc_weight_opt.\<rho>' (weight T)\<close>
        apply (subst (asm) distinct_mset_set_mset_ident)
         apply (use atms dist model[OF Some] in auto; fail)[]
        using Some' by auto
    }
    moreover have \<open>\<rho>\<^sub>e (mset_set ?K) \<le> \<rho> (mset_set ?K)\<close>
      unfolding \<rho>\<^sub>e_def
      apply (rule \<rho>_mono2)
      subgoal
        using model Some' by (auto simp: finite_postp consistent_interp_postp)
      subgoal by (auto simp: distinct_mset_mset_set)
      subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
      subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
      subgoal
        unfolding filter_filter_mset
        apply (rule filter_mset_mono_subset)
        by (auto simp: postp_def)
      done
    ultimately show ?thesis
      using Some' by auto
  qed
qed


inductive ocdcl\<^sub>W_o_r :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
  decide: "odecide S S' \<Longrightarrow> ocdcl\<^sub>W_o_r S S'" |
  bj: "enc_weight_opt.cdcl_bab_bj S S' \<Longrightarrow> ocdcl\<^sub>W_o_r S S'"

inductive cdcl_bab_r :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
  cdcl_conflict: "conflict S S' \<Longrightarrow> cdcl_bab_r S S'" |
  cdcl_propagate: "propagate S S' \<Longrightarrow> cdcl_bab_r S S'" |
  cdcl_improve: "enc_weight_opt.improvep S S' \<Longrightarrow> cdcl_bab_r S S'" |
  cdcl_conflict_opt: "enc_weight_opt.conflict_opt S S' \<Longrightarrow> cdcl_bab_r S S'" |
  cdcl_o': "ocdcl\<^sub>W_o_r S S' \<Longrightarrow> cdcl_bab_r S S'"

inductive cdcl_bab_r_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
  cdcl_bab_r_conflict: "conflict S S' \<Longrightarrow> cdcl_bab_r_stgy S S'" |
  cdcl_bab_r_propagate: "propagate S S' \<Longrightarrow> cdcl_bab_r_stgy S S'" |
  cdcl_bab_r_improve: "enc_weight_opt.improvep S S' \<Longrightarrow> cdcl_bab_r_stgy S S'" |
  cdcl_bab_r_conflict_opt: "enc_weight_opt.conflict_opt S S' \<Longrightarrow> cdcl_bab_r_stgy S S'" |
  cdcl_bab_r_other': "ocdcl\<^sub>W_o_r S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> cdcl_bab_r_stgy S S'"

lemma reduce_trail_to_compow_tl_trail_le:
  \<open>length M < length (trail M') \<Longrightarrow> reduce_trail_to M M' = (tl_trail^^(length (trail M') - length M)) M'\<close>
  apply (induction M\<equiv>M S\<equiv>M' arbitrary: M M' rule: reduce_trail_to.induct)
  subgoal for F S
    apply (subst reduce_trail_to.simps)
    apply (cases \<open>length F < length (trail S) - Suc 0\<close>)
    apply (auto simp: less_iff_Suc_add funpow_swap1)
    apply (subgoal_tac \<open>k=0\<close>)
    apply auto
    by presburger
  done

lemma ocdcl\<^sub>W_o_r_cases[consumes 1, case_names odecode obacktrack skip resolve]:
  assumes
    \<open>ocdcl\<^sub>W_o_r S T\<close>
    \<open>odecide S T \<Longrightarrow> P T\<close>
    \<open>enc_weight_opt.obacktrack S T \<Longrightarrow> P T\<close>
    \<open>skip S T \<Longrightarrow> P T\<close>
    \<open>resolve S T \<Longrightarrow> P T\<close>
  shows \<open>P T\<close>
  using assms by (auto simp: ocdcl\<^sub>W_o_r.simps enc_weight_opt.cdcl_bab_bj.simps)

context
  fixes S :: 'st
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = \<Sigma> \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>
     \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin


lemma odecide_decide:
  \<open>odecide S T \<Longrightarrow> decide S T\<close>
  apply (elim odecideE)
  subgoal for L
    by (rule decide.intros[of S \<open>L\<close>]) auto
  subgoal for L
    by (rule decide.intros[of S \<open>Neg (additional_atm L)\<close>]) (use S_\<Sigma> \<Delta>\<Sigma>_\<Sigma> in auto)
  subgoal for L
    by (rule decide.intros[of S \<open>Pos (L\<^sup>\<mapsto>\<^sup>1)\<close>]) (use S_\<Sigma> \<Delta>\<Sigma>_\<Sigma> in auto)
  subgoal for L
    by (rule decide.intros[of S \<open>Pos (L\<^sup>\<mapsto>\<^sup>0)\<close>]) (use S_\<Sigma> \<Delta>\<Sigma>_\<Sigma> in auto)
  done

lemma ocdcl\<^sub>W_o_r_ocdcl\<^sub>W_o:
  \<open>ocdcl\<^sub>W_o_r S T \<Longrightarrow> enc_weight_opt.ocdcl\<^sub>W_o S T\<close>
  using S_\<Sigma> by (auto simp: ocdcl\<^sub>W_o_r.simps enc_weight_opt.ocdcl\<^sub>W_o.simps
      dest: odecide_decide)

lemma cdcl_bab_r_cdcl_bab:
  \<open>cdcl_bab_r S T \<Longrightarrow> enc_weight_opt.cdcl_bab S T\<close>
  using S_\<Sigma> by (auto simp: cdcl_bab_r.simps enc_weight_opt.cdcl_bab.simps
      dest: ocdcl\<^sub>W_o_r_ocdcl\<^sub>W_o)

lemma cdcl_bab_r_stgy_cdcl_bab_stgy:
  \<open>cdcl_bab_r_stgy S T \<Longrightarrow> enc_weight_opt.cdcl_bab_stgy S T\<close>
  using S_\<Sigma> by (auto simp: cdcl_bab_r_stgy.simps enc_weight_opt.cdcl_bab_stgy.simps
      dest: ocdcl\<^sub>W_o_r_ocdcl\<^sub>W_o)

end


context
  fixes S :: 'st
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = \<Sigma> \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>
     \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin

lemma rtranclp_cdcl_bab_r_cdcl_bab:
  \<open>cdcl_bab_r\<^sup>*\<^sup>* S T \<Longrightarrow> enc_weight_opt.cdcl_bab\<^sup>*\<^sup>* S T\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using S_\<Sigma> enc_weight_opt.rtranclp_cdcl_bab_no_more_init_clss[of S T]
    by(auto dest: cdcl_bab_r_cdcl_bab)
  done


lemma rtranclp_cdcl_bab_r_stgy_cdcl_bab_stgy:
  \<open>cdcl_bab_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> enc_weight_opt.cdcl_bab_stgy\<^sup>*\<^sup>* S T\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using S_\<Sigma>
      enc_weight_opt.rtranclp_cdcl_bab_no_more_init_clss[of S T,
        OF enc_weight_opt.rtranclp_cdcl_bab_stgy_cdcl_bab]
    by(auto dest: cdcl_bab_r_stgy_cdcl_bab_stgy)
  done

end

lemma total_entails_iff_no_conflict:
  assumes \<open>atms_of_mm N \<subseteq> atm_of ` I\<close> and \<open>consistent_interp I\<close>
  shows \<open>I \<Turnstile>sm N \<longleftrightarrow> (\<forall>C \<in># N. \<not>I \<Turnstile>s CNot C)\<close>
  apply rule
  subgoal
    using assms by (auto dest!: multi_member_split
        simp: consistent_CNot_not)
  subgoal
    by (smt assms(1) atms_of_atms_of_ms_mono atms_of_ms_CNot_atms_of
        atms_of_ms_insert atms_of_ms_mono atms_of_s_def empty_iff
        subset_iff sup.orderE total_not_true_cls_true_clss_CNot
        total_over_m_alt_def true_clss_def)
  done

lemma no_step_cdcl_bab_r_stgy_no_step_cdcl_bab_stgy:
  assumes
    N: \<open>init_clss S = penc N\<close> and
    \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    tr_alien: \<open>atm_of ` lits_of_l (trail S) \<subseteq> \<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>
       \<union> additional_atm ` \<Delta>\<Sigma>\<close>
  shows
    \<open>no_step cdcl_bab_r_stgy S \<longleftrightarrow> no_step enc_weight_opt.cdcl_bab_stgy S\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?B
  then show \<open>?A\<close>
    using N \<Sigma> cdcl_bab_r_stgy_cdcl_bab_stgy[of S] atms_of_mm_encode_clause_subset[of N]
      atms_of_mm_encode_clause_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
      atms_of_mm_penc_subset2[of N]
    by auto
next
  assume ?A
  then have
    nsd: \<open>no_step odecide S\<close> and
    nsp: \<open>no_step propagate S\<close> and
    nsc: \<open>no_step conflict S\<close> and
    nsi: \<open>no_step enc_weight_opt.improvep S\<close> and
    nsco: \<open>no_step enc_weight_opt.conflict_opt S\<close>
    by (auto simp: cdcl_bab_r_stgy.simps ocdcl\<^sub>W_o_r.simps)
  have
    nsi': \<open>\<And>M'. conflicting S = None \<Longrightarrow> \<not>enc_weight_opt.is_improving (trail S) M' S\<close> and
    nsco': \<open>conflicting S = None \<Longrightarrow> negate_ann_lits (trail S) \<notin># enc_weight_opt.conflicting_clss S\<close>
    using nsi nsco unfolding enc_weight_opt.improvep.simps enc_weight_opt.conflict_opt.simps
    by auto
  have N_\<Sigma>: \<open>atms_of_mm (penc N) =
    atms_of_mm N \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union>
    replacement_neg ` \<Delta>\<Sigma>\<close>
    using N \<Sigma> cdcl_bab_r_stgy_cdcl_bab_stgy[of S] atms_of_mm_encode_clause_subset[of N]
      atms_of_mm_encode_clause_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
      atms_of_mm_penc_subset2[of N]
    by auto
  have False if dec: \<open>decide S T\<close> for T
  proof -
    obtain L where
      [simp]: \<open>conflicting S = None\<close> and
      undef: \<open>undefined_lit (trail S) L\<close> and
      L: \<open>atm_of L \<in> atms_of_mm (init_clss S)\<close> and
      T: \<open>T \<sim> cons_trail (Decided L) S\<close>
      using dec unfolding decide.simps
      by auto

    have 1: \<open>atm_of L \<notin> \<Sigma> - \<Delta>\<Sigma>\<close>
      using nsd L undef by (fastforce simp: odecide.simps N \<Sigma>)
    have 2: False if L: \<open>atm_of L \<in> replacement_pos ` \<Delta>\<Sigma> \<union>
       replacement_neg ` \<Delta>\<Sigma> \<union> additional_atm ` \<Delta>\<Sigma>\<close>
    proof -
      obtain A where
        \<open>A \<in> \<Delta>\<Sigma>\<close> and
        \<open>atm_of L = replacement_pos A \<or> atm_of L = replacement_neg A \<or> atm_of L = additional_atm A\<close> and
        \<open>A \<in> \<Sigma>\<close>
        using L \<Delta>\<Sigma>_\<Sigma> by auto
      then show False
        using nsd L undef T N_\<Sigma>
        using odecide.intros(2-)[of S \<open>A\<close>]
        unfolding N
        by (cases L) (auto 6 5 simp: defined_lit_Neg_Pos_iff \<Sigma>)
    qed
    have defined_replacement_pos: \<open>defined_lit (trail S) (Pos (replacement_pos L))\<close>
      if \<open>L \<in> \<Delta>\<Sigma>\<close> for L
      using nsd that \<Delta>\<Sigma>_\<Sigma> odecide.intros(2-)[of S \<open>L\<close>] by (force simp: N \<Sigma> N_\<Sigma>)
    have defined_all: \<open>defined_lit (trail S) L\<close>
      if \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma>\<close> for L
      using nsd that \<Delta>\<Sigma>_\<Sigma> odecide.intros(1)[of S \<open>L\<close>] by (force simp: N \<Sigma> N_\<Sigma>)
    have defined_replacement_neg: \<open>defined_lit (trail S) (Pos (replacement_neg L))\<close>
      if \<open>L \<in> \<Delta>\<Sigma>\<close> for L
      using nsd that \<Delta>\<Sigma>_\<Sigma> odecide.intros(2-)[of S \<open>L\<close>] by (force simp: N \<Sigma> N_\<Sigma>)
    have defined_additional_atm: \<open>defined_lit (trail S) (Neg (additional_atm L))\<close>
      if \<open>L \<in> \<Delta>\<Sigma>\<close> for L
      using nsd that \<Delta>\<Sigma>_\<Sigma> odecide.intros(2-)[of S \<open>L\<close>] by (force simp: N \<Sigma> N_\<Sigma>)
    have \<open>atm_of L \<in># mset_set \<Delta>\<Sigma>\<close> and 3: \<open>atm_of L \<in> \<Delta>\<Sigma>\<close>
      using 1 2 L \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> by (auto simp: N \<Sigma> N_\<Sigma>)
    have nsp': \<open>\<forall>E. E \<in># additional_constraint L \<longrightarrow>
              (\<forall>L\<in># E. trail S \<Turnstile>as CNot (remove1_mset L E) \<longrightarrow>
                   defined_lit (trail S) L)\<close> and
      nsc': \<open>\<forall>E. E \<in># additional_constraint L \<longrightarrow>
              (\<forall>L\<in># E. \<not>trail S \<Turnstile>as CNot E)\<close>
      if \<open>L \<in> \<Delta>\<Sigma>\<close> for L
      using nsp nsc assms that finite_\<Sigma> unfolding penc_def
      by (fastforce simp: propagate.simps conflict.simps additional_constraints_def
          clauses_def
          dest!: multi_member_split[of \<open>L\<close>])+
    have [simp]: \<open>{A \<in> \<Delta>\<Sigma>. A \<in> \<Sigma>} = \<Delta>\<Sigma>\<close>
      using \<Delta>\<Sigma>_\<Sigma> by auto
    have atms_tr': \<open>\<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma> \<subseteq>
       atm_of ` (lits_of_l (trail S))\<close>
      using N \<Sigma> cdcl_bab_r_stgy_cdcl_bab_stgy[of S] atms_of_mm_encode_clause_subset[of N]
        atms_of_mm_encode_clause_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
        defined_replacement_pos defined_replacement_neg defined_additional_atm defined_all
      unfolding N \<Sigma> N_\<Sigma> (*TODO proof*)
      apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
        apply (metis image_eqI literal.sel(1) literal.sel(2) uminus_Pos)
       apply (metis image_eqI literal.sel(1) literal.sel(2))
      apply (metis image_eqI literal.sel(1) literal.sel(2))
      done
    then have atms_tr: \<open>atms_of_mm (encode_clauses N) \<subseteq> atm_of ` (lits_of_l (trail S))\<close>
      using N \<Sigma> atms_of_mm_encode_clause_subset[of N]
        atms_of_mm_encode_clause_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
      unfolding N \<Sigma> N_\<Sigma>
      by force
    let ?L = \<open>atm_of L\<close>
    have defined_if_additional_var:
      \<open>additional_var x \<in> lits_of_l (trail S) \<Longrightarrow>
          defined_lit (trail S) (Pos x)\<close> (is \<open>_ \<Longrightarrow> ?A\<close>) and
      ent_add:
      \<open>trail S \<Turnstile>asm additional_constraint x\<close>
      if \<open>x \<in> \<Delta>\<Sigma>\<close> for x
    proof -
      note [[simp_depth_limit = 2]]
      have eq:
        \<open>(Pos (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x) \<notin> lits_of_l (trail S)) \<and>
	   (Pos (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (additional_atm (x)) \<notin> lits_of_l (trail S)) \<and>
	   (Pos (x) \<in> lits_of_l (trail S) \<longrightarrow>
	    additional_var (x) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x\<^sup>\<mapsto>\<^sup>1) \<notin> lits_of_l (trail S)) \<and>
	   (Pos (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<longrightarrow>
	    Pos (x) \<notin> lits_of_l (trail S)) \<and>
	   (Pos (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (additional_atm (x)) \<notin> lits_of_l (trail S)) \<and>
	   (Neg (x) \<in> lits_of_l (trail S) \<longrightarrow>
	    additional_var (x) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x\<^sup>\<mapsto>\<^sup>0) \<notin> lits_of_l (trail S))\<close>
	      \<open>(Neg (x) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<or>
	    Pos (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S)) \<and>
	   (Pos (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<longrightarrow>
	    Pos (x) \<in> lits_of_l (trail S)) \<and>
	   (Neg (additional_atm (x)) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<or>
	    Pos (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S)) \<and>
	   (Pos (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<longrightarrow>
	    additional_var (x) \<in> lits_of_l (trail S)) \<and>
	   (Pos (x) \<in> lits_of_l (trail S) \<and>
	    Neg (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (additional_atm (x)) \<in> lits_of_l (trail S) \<or>
	    additional_var (x) \<in> lits_of_l (trail S)) \<and>
	   (additional_var (x) \<in> lits_of_l (trail S) \<and>
	    Neg (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x) \<in> lits_of_l (trail S) \<or>
	    Pos (x) \<in> lits_of_l (trail S)) \<and>
	   (additional_var (x) \<in> lits_of_l (trail S) \<and>
	    Pos (x) \<in> lits_of_l (trail S) \<longrightarrow>
	    Pos (x\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S)) \<and>
	   (Pos (x) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<or>
	    Pos (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S)) \<and>
	   (Pos (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x) \<in> lits_of_l (trail S)) \<and>
	   (Neg (additional_atm (x)) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<or>
	    Pos (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S)) \<and>
	   (Pos (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<longrightarrow>
	    additional_var (x) \<in> lits_of_l (trail S)) \<and>
	   (Neg (x) \<in> lits_of_l (trail S) \<and>
	    Neg (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<longrightarrow>
	    Neg (additional_atm (x)) \<in> lits_of_l (trail S) \<or>
	    additional_var (x) \<in> lits_of_l (trail S)) \<and>
	   (additional_var (x) \<in> lits_of_l (trail S) \<and>
	    Neg (x\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S) \<longrightarrow>
	    Pos (x) \<in> lits_of_l (trail S) \<or>
	    Neg (x) \<in> lits_of_l (trail S))\<close>
	      using that(1) nsc'[of \<open>x\<close>] nsp'[of \<open>x\<close>] finite_\<Sigma>
          defined_replacement_neg[of \<open>x\<close>]
         apply (simp_all only: conflict.simps clauses_def N additional_constraint_def
            penc_def true_annots_true_cls simp_thms 3
            true_clss_insert
            set_mset_empty empty_iff finite_set_mset_mset_set
            Decided_Propagated_in_iff_in_lits_of_l imp_disjL Ball_def
            all_conj_distrib ex_disj_distrib member_add_mset)
         apply simp_all
        by force
      have \<open>additional_var (x) \<in> lits_of_l (trail S) \<Longrightarrow>
         Neg (additional_atm x) \<notin> lits_of_l (trail S)\<close>
        using n_d that by (auto dest: no_dup_consistentD)
      then show ?A if \<open>additional_var (x) \<in> lits_of_l (trail S)\<close>
        using \<open>x \<in> \<Delta>\<Sigma>\<close> eq \<open>additional_var (x) \<in> lits_of_l (trail S)\<close>
        using defined_replacement_pos[of \<open>x\<close>]
        apply (case_tac \<open>Pos x \<in> lits_of_l (trail S)\<close>)
        using Decided_Propagated_in_iff_in_lits_of_l apply metis
        apply (simp only: Decided_Propagated_in_iff_in_lits_of_l)
        apply (case_tac \<open>Neg x \<in> lits_of_l (trail S)\<close>)
         apply (simp add: Decided_Propagated_in_iff_in_lits_of_l)
        apply (simp add: Decided_Propagated_in_iff_in_lits_of_l)
        done
      show \<open>trail S \<Turnstile>asm additional_constraint x\<close>
        using eq that defined_additional_atm defined_replacement_neg
          defined_replacement_pos
        apply (simp_all add: additional_constraint_def true_annot_def
            Decided_Propagated_in_iff_in_lits_of_l)
        apply (intro conjI)
             apply metis+
        done
    qed
    have eq_add_M': \<open>\<rho>\<^sub>e (mset (map lit_of (trail S) @ M')) =
	  \<rho>\<^sub>e (mset (map lit_of (trail S)))\<close>
      if
        \<open>total_over_m (set_mset (mset (map lit_of (trail S) @ M')))
	  (set_mset (init_clss S))\<close> and
	      dist: \<open>distinct_mset (atm_of `# mset (map lit_of (trail S) @ M'))\<close> and
	      \<open>consistent_interp (set_mset (mset (map lit_of (trail S) @ M')))\<close>
      for M'
    proof -
      have [simp]: \<open>additional_var a \<notin> set M'\<close> \<open>-additional_var a \<notin> set M'\<close>
        if \<open>a \<in> \<Delta>\<Sigma>\<close> for a
        using defined_additional_atm[of a, OF that] dist
        using that by (force simp: Decided_Propagated_in_iff_in_lits_of_l
            distinct_mset_add mset_inter_empty_set_mset lits_of_def
            eq_commute[of _ \<open>lit_of _\<close>])+
      then have [simp]: \<open>{#a \<in># mset M'. atm_of a \<in> \<Delta>\<Sigma> \<and>
	 (additional_var (atm_of a) \<in> lit_of ` set (trail S) \<or>
	    additional_var (atm_of a) \<in> set M')#} = {#}\<close>
	      using that defined_if_additional_var
	      apply (auto simp: filter_mset_empty_conv lits_of_def
	          consistent_interp_def distinct_mset_add mset_inter_empty_set_mset
	          eq_commute[of _ \<open>lit_of _\<close>]
	          intro: filter_mset_cong)
	      by (metis IntI defined_lit_map empty_iff imageI literal.sel(1))

      have [simp]: \<open>{#x \<in># lit_of `# mset (trail S).
       	 atm_of x \<in> \<Delta>\<Sigma> \<and>
       	 (additional_var (atm_of x) \<in> lit_of ` set (trail S) \<or>
       	  additional_var (atm_of x) \<in> set M')#} =
       	{#x \<in># lit_of `# mset (trail S).
       	 atm_of x \<in> \<Delta>\<Sigma> \<and> additional_var (atm_of x) \<in> lit_of ` set (trail S)#}\<close>
	      apply (rule filter_mset_cong2)
	      using n_d that
	      by (auto simp: lits_of_def uminus_lit_swap)
      show ?thesis
        unfolding \<rho>\<^sub>e_def apply -
        by (rule arg_cong[of _ _ \<rho>]) (auto simp: lits_of_def)
    qed

    have lit_of_mset_trail: \<open>lit_of `# mset (trail S) = mset (map lit_of (trail S))\<close>
      by auto
    have \<open>trail S \<Turnstile>asm encode_clauses N\<close>
      unfolding true_annots_true_cls
      apply (subst total_entails_iff_no_conflict[OF atms_tr])
      subgoal using n_d by (blast dest: distinct_consistent_interp)
      subgoal
        using nsc by (auto simp: conflict.simps clauses_def N
            penc_def true_annots_true_cls)
      done
    moreover have \<open>trail S \<Turnstile>asm additional_constraints\<close>
      using \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> that 1 ent_add
      unfolding additional_constraints_def
        true_annots_def true_annot_def by (auto
          dest: multi_member_split)
    ultimately have tr_S_clss: \<open>trail S \<Turnstile>asm init_clss S\<close>
      unfolding assms penc_def by auto

    have \<open>negate_ann_lits (trail S) \<in># enc_weight_opt.conflicting_clss S\<close>
      if \<open>\<not> Some (\<rho>\<^sub>e (lit_of `# mset (trail S))) < enc_weight_opt.\<rho>' (enc_weight_opt.weight S)\<close>
      unfolding negate_ann_lits_pNeg_lit_of comp_def lit_of_mset_trail
      apply (rule enc_weight_opt.pruned_clause_in_conflicting_clss)
         apply (use eq_add_M' that in auto)[]
      using \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> that tr_alien n_d
        apply (fastforce simp: simple_clss_def N \<Sigma> N_\<Sigma> lits_of_def
          image_image atms_of_def tautology_union uminus_lit_swap image_iff
          dest: )
      using no_dup_distinct[OF n_d] distinct_consistent_interp[OF n_d]
      by (auto simp: lits_of_def simp flip: distinct_mset_mset_distinct)
    then have ge:
      \<open>Some (\<rho>\<^sub>e (lit_of `# mset (trail S))) < enc_weight_opt.\<rho>' (enc_weight_opt.weight S)\<close>
      using nsco' by auto

    let ?M'' = \<open>Decided `# Pos `# {#L \<in># mset_set \<Delta>\<Sigma>. undefined_lit (trail S) (Pos L)#}\<close>
    let ?M' = \<open>mset (trail S) + ?M''\<close>
    obtain M' M'' :: \<open>('v, 'v clause) ann_lits\<close> where
      M': \<open>?M' = mset M'\<close> and
      M'': \<open>?M'' = mset M''\<close>
      using ex_mset by metis
    from arg_cong[OF this(1), of set_mset, symmetric]
    have lits_of_M': \<open>lits_of_l M' = lits_of_l (trail S) \<union>
     	 Pos ` {L \<in> \<Delta>\<Sigma>. undefined_lit (trail S) (Pos L)}\<close>
      using finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma> by (auto simp: lits_of_def image_Un image_image)
    have \<open>\<not>tautology (lit_of `# mset M')\<close>
      using \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> that tr_alien n_d
      by (force simp: simple_clss_def M'[symmetric] N \<Sigma> N_\<Sigma> lits_of_def
          image_image atms_of_def tautology_union uminus_lit_swap image_iff
          Decided_Propagated_in_iff_in_lits_of_l defined_lit_Neg_Pos_iff
          dest: no_dup_not_tautology)
    moreover have dist_M': \<open>distinct_mset
       (lit_of `# mset (trail S) +
	     poss (mset_set {x \<in> \<Delta>\<Sigma>. undefined_lit (trail S) (Pos x)}))\<close>
      using n_d \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma>
      by (auto simp: distinct_mset_add mset_inter_empty_set_mset
          Decided_Propagated_in_iff_in_lits_of_l defined_lit_Neg_Pos_iff
          lits_of_def image_image inj_on_Pos image_iff
          distinct_image_mset_inj distinct_mset_mset_set
          dest: no_dup_distinct)
    ultimately have simple_M': \<open>lit_of `# mset M' \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      using \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> that tr_alien
      by (auto simp: simple_clss_def M'[symmetric] N \<Sigma> N_\<Sigma> lits_of_def
          image_image atms_of_def )
    have n_d_M': \<open>no_dup M'\<close>
      using n_d finite_\<Sigma>
      by (force simp: no_dup_def distinct_mset_add mset_inter_empty_set_mset
          distinct_mset_mset_set Decided_Propagated_in_iff_in_lits_of_l
          lits_of_def
          simp flip: distinct_mset_mset_distinct M')
    moreover have \<open>total_over_m (lits_of_l M') (set_mset (init_clss S))\<close>
      using atms_tr' defined_replacement_pos defined_all defined_replacement_neg
        defined_additional_atm
      apply (auto simp: N \<Sigma> N_\<Sigma> total_over_m_def total_over_set_def
          lits_of_M' Decided_Propagated_in_iff_in_lits_of_l)
      apply (metis (mono_tags, lifting) Decided_Propagated_in_iff_in_lits_of_l image_eqI
          literal.sel(1) mem_Collect_eq uminus_Pos)
      done
    moreover have \<open>M' \<Turnstile>asm init_clss S\<close>
      using \<open>trail S \<Turnstile>asm init_clss S\<close> arg_cong[OF M', of set_mset, symmetric]
      by (auto simp: true_annots_true_cls)
    moreover have \<open>negate_ann_lits (trail S) \<in># enc_weight_opt.conflicting_clss S\<close>
      if \<open>\<not> Some (\<rho>\<^sub>e (lit_of `# mset (trail S))) < enc_weight_opt.\<rho>' (enc_weight_opt.weight S)\<close>
      unfolding negate_ann_lits_pNeg_lit_of comp_def lit_of_mset_trail
      apply (rule enc_weight_opt.pruned_clause_in_conflicting_clss)
         apply (use eq_add_M' that in auto)[]
      using \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> that tr_alien n_d
        apply (fastforce simp: simple_clss_def M'[symmetric] N \<Sigma> N_\<Sigma> lits_of_def
          image_image atms_of_def tautology_union uminus_lit_swap image_iff
          dest: )
      using no_dup_distinct[OF n_d] distinct_consistent_interp[OF n_d]
      by (auto simp: lits_of_def simp flip: distinct_mset_mset_distinct)
    moreover have \<open>\<rho>\<^sub>e (lit_of `# mset M') = \<rho>\<^sub>e (lit_of `# mset (trail S))\<close>
      unfolding M'[symmetric] mset_append[symmetric] M'' mset_map[symmetric]
        map_append
      apply (rule eq_add_M')
      unfolding M' mset_append M''[symmetric] mset_map image_mset_union[symmetric]
        map_append
      by (use calculation n_d_M' in \<open>auto simp: lits_of_def
	       simp flip: no_dup_alt_def
	       dest: no_dup_distinct distinct_consistent_interp\<close>)
    moreover have eq: \<open>\<rho>\<^sub>e (lit_of `# mset (trail S) + lit_of `# c) =
	     \<rho>\<^sub>e (lit_of `# mset (trail S))\<close>
      if
        \<open>total_over_m (lits_of_l M'a) (set_mset (init_clss S))\<close> and
        M'a: \<open>mset M'a = mset (trail S) + c\<close> and
        simple: \<open>lit_of `# mset (trail S) + lit_of `# c \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      for c :: \<open>('v, 'v clause) ann_lit multiset\<close> and M'a
    proof -
      obtain c' where c: \<open>c = mset c'\<close>
        using ex_mset by metis
      show ?thesis
        unfolding c mset_append[symmetric] mset_map[symmetric]
          map_append
        apply (rule eq_add_M')
        using that(1) simple  arg_cong[OF M'a, of set_mset]
          distinct_consistent_interp[of M'a, unfolded no_dup_alt_def M'a]
        by (auto simp: simple_clss_def c total_over_m_alt_def
            atms_of_def image_image image_Un lits_of_def tautology_distinct_atm_iff)
    qed
    ultimately show False
      using nsi'[of M'] simple_M' n_d_M' ge
      unfolding enc_weight_opt.conflicting_clss_def
      by (auto simp: enc_weight_opt.improvep.simps enc_weight_opt.is_improving_int_def
          enc_weight_opt.conflict_opt.simps enc_weight_opt.conflicting_clss_def
          subset_mset.le_iff_add)
  qed
  then show ?B
    using \<open>?A\<close>
    by (auto simp: cdcl_bab_r_stgy.simps enc_weight_opt.cdcl_bab_stgy.simps
        ocdcl\<^sub>W_o_r.simps enc_weight_opt.ocdcl\<^sub>W_o.simps)
qed

lemma cdcl_bab_r_stgy_init_clss:
  \<open>cdcl_bab_r_stgy S T \<Longrightarrow> init_clss S = init_clss T\<close>
  by (auto simp: cdcl_bab_r_stgy.simps ocdcl\<^sub>W_o_r.simps  enc_weight_opt.cdcl_bab_bj.simps
      elim: conflictE propagateE enc_weight_opt.improveE enc_weight_opt.conflict_optE
      odecideE skipE resolveE enc_weight_opt.obacktrackE)

lemma rtranclp_cdcl_bab_r_stgy_init_clss:
  \<open>cdcl_bab_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> init_clss S = init_clss T\<close>
  by  (induction rule: rtranclp_induct)(auto simp:  dest: cdcl_bab_r_stgy_init_clss)

lemma [simp]:
  \<open>enc_weight_opt.abs_state (init_state N) = abs_state (init_state N)\<close>
  by (auto simp: enc_weight_opt.abs_state_def abs_state_def)

corollary
  assumes
    \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and dist: \<open>distinct_mset_mset N\<close> and
    \<open>full cdcl_bab_r_stgy (init_state (penc N)) T \<close>
  shows
    \<open>full enc_weight_opt.cdcl_bab_stgy (init_state (penc N)) T\<close>
proof -
  have [simp]: \<open>atms_of_mm (CDCL_W_Abstract_State.init_clss (enc_weight_opt.abs_state T)) =
    atms_of_mm (init_clss T)\<close>
    by (auto simp: enc_weight_opt.abs_state_def init_clss.simps)
  let ?S = \<open>init_state (penc N)\<close>
  have
    st: \<open>cdcl_bab_r_stgy\<^sup>*\<^sup>* ?S T\<close> and
    ns: \<open>no_step cdcl_bab_r_stgy T\<close>
    using assms unfolding full_def by metis+
  have st': \<open>enc_weight_opt.cdcl_bab_stgy\<^sup>*\<^sup>* ?S T\<close>
    by (rule rtranclp_cdcl_bab_r_stgy_cdcl_bab_stgy[OF _ st])
      (use atms_of_mm_penc_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma> \<Sigma> in auto)
  have [simp]:
    \<open>CDCL_W_Abstract_State.init_clss (abs_state (init_state (penc N))) =
      (penc N)\<close>
    by (auto simp: abs_state_def init_clss.simps)
  have [iff]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state ?S)\<close>
    using dist distinct_mset_penc[of N]
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def \<Sigma>
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state T)\<close>
    using enc_weight_opt.rtranclp_cdcl_bab_stgy_all_struct_inv[of ?S T]
      enc_weight_opt.rtranclp_cdcl_bab_stgy_cdcl_bab[OF st']
    by auto
  then have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (enc_weight_opt.abs_state T)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (enc_weight_opt.abs_state T)\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have [simp]: \<open>init_clss T = penc N\<close>
    using rtranclp_cdcl_bab_r_stgy_init_clss[OF st] by auto

  have \<open>no_step enc_weight_opt.cdcl_bab_stgy T\<close>
    by (rule no_step_cdcl_bab_r_stgy_no_step_cdcl_bab_stgy[THEN iffD1, of _ N, OF _ _ _ _ ns])
      (use  alien atms_of_mm_penc_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma> lev
        in \<open>auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def \<Sigma>
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def\<close>)
  then show \<open>full enc_weight_opt.cdcl_bab_stgy (init_state (penc N)) T\<close>
    using st' unfolding full_def
    by auto
qed

lemma cdcl_bab_stgy_no_smaller_propa:
  \<open>cdcl_bab_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  apply (induction rule: cdcl_bab_stgy.induct)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bab_bj.simps
        elim!: rulesE)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bab_bj.simps
        elim!: rulesE)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bab_bj.simps
        elim!: rulesE)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bab_bj.simps
        elim!: rulesE)
  subgoal for T
    apply (cases rule: ocdcl\<^sub>W_o.cases, assumption; thin_tac \<open>ocdcl\<^sub>W_o S T\<close>)
    subgoal
      using decide_no_smaller_step[of S T]
      unfolding enc_weight_opt.no_confl_prop_impr.simps
      by auto
    subgoal
      apply (cases rule: cdcl_bab_bj.cases, assumption; thin_tac \<open>cdcl_bab_bj S T\<close>)
      subgoal
        using no_smaller_propa_tl[of S T]
        by (auto elim: rulesE)
      subgoal
        using no_smaller_propa_tl[of S T]
        by (auto elim: rulesE)
      subgoal
        using backtrackg_no_smaller_propa[OF obacktrack_backtrackg, of S T]
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto elim: obacktrackE)
      done
    done
  done

lemma additional_constraints_no_lonely_weighted_lit_cls:
  \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> C \<in># additional_constraint L \<Longrightarrow>
    no_lonely_weighted_lit_cls C\<close>
  by (auto simp: additional_constraint_def
      no_lonely_weighted_lit_cls_def)


lemma defined_replacement_pos_orinal:
  assumes
    def_neg: \<open>Pos (atm_of L\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S)\<close> and
    \<open>set_mset additional_constraints \<subseteq> set_mset (clauses S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    lev_L: \<open>get_level (trail S) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>1)) < backtrack_lvl S\<close> and
    L: \<open>atm_of L \<in> \<Delta>\<Sigma>\<close> and
    n_d: \<open>no_dup (trail S)\<close>
  shows \<open>defined_lit (trail S) L\<close>
proof -
  define i where \<open>i = get_level (trail S) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>1))\<close>
  have \<open>atm_of L \<in># mset_set \<Delta>\<Sigma>\<close>
    using L finite_\<Sigma> by auto
  then have H: \<open>\<And>M K M'. trail S = M' @ Decided K # M \<longrightarrow> (\<forall>D L'.
    D + {#L'#} \<in># additional_constraint (atm_of L) \<longrightarrow> undefined_lit M L' \<longrightarrow> \<not> M \<Turnstile>as CNot D)\<close>
    using smaller_propa assms(2) unfolding no_smaller_propa_def
      additional_constraints_def
    by (auto dest!: multi_member_split)
  obtain M1 M2 K where
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_K: \<open>get_level (trail S) K = Suc i\<close>
    using backtrack_ex_decomp[OF n_d lev_L] unfolding i_def
    by blast
  obtain M3 where
    M3: \<open>trail S = M3 @ M2 @ Decided K # M1\<close>
    using decomp by auto
  define M2' where
    \<open>M2' = M3 @ M2\<close>
  have \<open>undefined_lit (M2' @ Decided K # []) (Pos (atm_of L\<^sup>\<mapsto>\<^sup>1))\<close>
    using def_neg n_d lev_L lev_K i_def[symmetric]
    unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: get_level_append_if defined_lit_Neg_Pos_iff
        get_level_cons_if
        split: if_splits
        dest: no_dup_consistentD
        no_dup_append_in_atm_notin)
  then have Pos': \<open>Pos (atm_of L\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l M1\<close>
    using def_neg unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD no_dup_append_in_atm_notin)
  then have [iff]: \<open>defined_lit M1 (Neg (atm_of L\<^sup>\<mapsto>\<^sup>1))\<close>
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

  have [iff]: \<open>atm_of L \<noteq> additional_atm (atm_of L)\<close>
    using L by auto
  have 1: \<open>add_mset x N \<subseteq># {#a, b#} \<longleftrightarrow> (x = a \<and> N \<subseteq># {#b#} \<or> x = b \<and> N \<subseteq># {#a#})\<close>
    for N and x a b :: \<open>'v literal\<close>
    by (metis add_mset_commute empty_iff member_add_mset
        mset_subset_eq_add_mset_cancel mset_subset_eq_insertD set_mset_empty)
  have le2_empty: \<open>D - {#a, b#} = {#} \<longleftrightarrow> D = {#} \<or> D = {#a#} \<or> D = {#b#} \<or> D = {#a, b#}\<close>
    for D and a b :: \<open>'v literal\<close>
    unfolding Diff_eq_empty_iff_mset
    by (cases D)
      (auto simp add: add_mset_eq_add_mset remove1_mset_empty_iff 1
        subset_eq_mset_single_iff)
  have 2: \<open>remove1_mset a N = C \<longleftrightarrow> (a \<notin># N \<and> N = C \<or> N = add_mset a C)\<close>
    for N C and a :: \<open>'v literal\<close>
    by (auto simp: add_mset_remove_trivial_If
        split: if_splits)
  have \<open>defined_lit M1 L\<close>
    using H[of M2' K M1] L Pos' M3 unfolding M2'_def
    by (cases L)
      (simp_all add: additional_constraint_def add_mset_eq_add_mset
        le2_empty 2 defined_lit_Neg_Pos_iff
        all_conj_distrib remove1_mset_empty_iff conj_disj_distribL)
  then show ?thesis
    using M3 unfolding M2'_def
    by (auto simp: defined_lit_append)
qed

lemma defined_replacement_neg_orinal:
  assumes
    def_neg: \<open>Pos (atm_of L\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S)\<close> and
    \<open>set_mset additional_constraints \<subseteq> set_mset (clauses S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    lev_L: \<open>get_level (trail S) (Pos (atm_of L\<^sup>\<mapsto>\<^sup>0)) < backtrack_lvl S\<close> and
    L: \<open>atm_of L \<in> \<Delta>\<Sigma>\<close> and
    n_d: \<open>no_dup (trail S)\<close>
  shows \<open>defined_lit (trail S) L\<close>
proof -
  define i where \<open>i = get_level (trail S) (Pos (atm_of L\<^sup>\<mapsto>\<^sup>0))\<close>
  have \<open>atm_of L \<in># mset_set \<Delta>\<Sigma>\<close>
    using L finite_\<Sigma> by auto
  then have H: \<open>\<And>M K M'. trail S = M' @ Decided K # M \<longrightarrow> (\<forall>D L'.
    D + {#L'#} \<in># additional_constraint (atm_of L) \<longrightarrow> undefined_lit M L' \<longrightarrow> \<not> M \<Turnstile>as CNot D)\<close>
    using smaller_propa assms(2) unfolding no_smaller_propa_def penc_def
      additional_constraints_def
    by (auto dest!: multi_member_split)
  obtain M1 M2 K where
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_K: \<open>get_level (trail S) K = Suc i\<close>
    using backtrack_ex_decomp[OF n_d lev_L] unfolding i_def
    by blast
  obtain M3 where
    M3: \<open>trail S = M3 @ M2 @ Decided K # M1\<close>
    using decomp by auto
  define M2' where
    \<open>M2' = M3 @ M2\<close>
  have \<open>undefined_lit (M2' @ Decided K # []) (Pos (atm_of L\<^sup>\<mapsto>\<^sup>0))\<close>
    using def_neg n_d lev_L lev_K i_def[symmetric]
    unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: get_level_append_if defined_lit_Neg_Pos_iff
        get_level_cons_if
        split: if_splits
        dest: no_dup_consistentD
        no_dup_append_in_atm_notin)
  then have Pos': \<open>Pos (atm_of L\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l M1\<close>
    using def_neg unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD no_dup_append_in_atm_notin)
  then have [iff]: \<open>defined_lit M1 (Pos (atm_of L\<^sup>\<mapsto>\<^sup>0))\<close>
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

  have [iff]: \<open>atm_of L \<noteq> additional_atm (atm_of L)\<close>
    using L by auto
  have 1: \<open>add_mset x N \<subseteq># {#a, b#} \<longleftrightarrow> (x = a \<and> N \<subseteq># {#b#} \<or> x = b \<and> N \<subseteq># {#a#})\<close>
    for N and x a b :: \<open>'v literal\<close>
    by (metis add_mset_commute empty_iff member_add_mset
        mset_subset_eq_add_mset_cancel mset_subset_eq_insertD set_mset_empty)
  have le2_empty: \<open>D - {#a, b#} = {#} \<longleftrightarrow> D = {#} \<or> D = {#a#} \<or> D = {#b#} \<or> D = {#a, b#}\<close>
    for D and a b :: \<open>'v literal\<close>
    unfolding Diff_eq_empty_iff_mset
    by (cases D)
      (auto simp add: add_mset_eq_add_mset remove1_mset_empty_iff 1
        subset_eq_mset_single_iff)
  have 2: \<open>remove1_mset a N = C \<longleftrightarrow> (a \<notin># N \<and> N = C \<or> N = add_mset a C)\<close>
    for N C and a :: \<open>'v literal\<close>
    by (auto simp: add_mset_remove_trivial_If
        split: if_splits)
  have \<open>defined_lit M1 L\<close>
    using H[of M2' K M1] L Pos' M3 unfolding M2'_def
    by (cases L)
      (simp_all add: additional_constraint_def add_mset_eq_add_mset
        le2_empty 2 defined_lit_Neg_Pos_iff
        all_conj_distrib remove1_mset_empty_iff conj_disj_distribL)
  then show ?thesis
    using M3 unfolding M2'_def
    by (auto simp: defined_lit_append)
qed

lemma defined_replacement_additional_neg_orinal:
  assumes
    def_neg: \<open>Neg (atm_of L\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S)\<close>
      \<open>additional_var (atm_of L) \<in> lits_of_l (trail S)\<close> and
    \<open>set_mset additional_constraints \<subseteq> set_mset (clauses S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    lev_L: \<open>get_level (trail S) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>0)) < backtrack_lvl S\<close> and
    lev_L': \<open>get_level (trail S) (additional_var (atm_of L)) < backtrack_lvl S\<close> and
    L: \<open>atm_of L \<in> \<Delta>\<Sigma>\<close> and
    n_d: \<open>no_dup (trail S)\<close>
  shows \<open>defined_lit (trail S) L\<close>
proof -
  define i where
    \<open>i = max (get_level (trail S) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>0))) (get_level (trail S) (additional_var (atm_of L)))\<close>
  have \<open>atm_of L \<in># mset_set \<Delta>\<Sigma>\<close>
    using L finite_\<Sigma> by auto
  then have H: \<open>\<And>M K M'. trail S = M' @ Decided K # M \<longrightarrow> (\<forall>D L'.
    D + {#L'#} \<in># additional_constraint (atm_of L) \<longrightarrow> undefined_lit M L' \<longrightarrow> \<not> M \<Turnstile>as CNot D)\<close>
    using smaller_propa assms(3) finite_\<Sigma> unfolding no_smaller_propa_def
      additional_constraints_def
    by (auto dest: multi_member_split)

  have \<open>i < backtrack_lvl S\<close>
    using lev_L lev_L' unfolding i_def by auto
  then obtain M1 M2 K where
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_K: \<open>get_level (trail S) K = Suc i\<close>
    using backtrack_ex_decomp[OF n_d] unfolding i_def
    by blast
  obtain M3 where
    M3: \<open>trail S = M3 @ M2 @ Decided K # M1\<close>
    using decomp by auto
  define M2' where
    \<open>M2' = M3 @ M2\<close>
  have \<open>undefined_lit (M2' @ Decided K # []) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>0))\<close>
    using def_neg n_d lev_L lev_K i_def[symmetric]
    unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: get_level_append_if defined_lit_Neg_Pos_iff
        get_level_cons_if
        split: if_splits
        dest: no_dup_consistentD
        no_dup_append_in_atm_notin)
  then have Neg': \<open>Neg (atm_of L\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l M1\<close>
    using def_neg unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD no_dup_append_in_atm_notin)
  then have [iff]: \<open>defined_lit M1 (Pos (atm_of L\<^sup>\<mapsto>\<^sup>0))\<close>
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  have \<open>undefined_lit (M2' @ Decided K # []) (additional_var (atm_of L))\<close>
    using def_neg n_d lev_L' lev_K i_def[symmetric]
    unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: get_level_append_if defined_lit_Neg_Pos_iff
        get_level_cons_if
        split: if_splits
        dest: no_dup_consistentD
        no_dup_append_in_atm_notin)
  then have Pos': \<open>additional_var (atm_of L) \<in> lits_of_l M1\<close>
    using def_neg unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD no_dup_append_in_atm_notin)
  then have [iff]: \<open>defined_lit M1 (additional_var (atm_of L))\<close>
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  have [iff]: \<open>atm_of L \<noteq> additional_atm (atm_of L)\<close>
    using L by auto
  have 1: \<open>add_mset x N \<subseteq># {#a, b#} \<longleftrightarrow> (x = a \<and> N \<subseteq># {#b#} \<or> x = b \<and> N \<subseteq># {#a#})\<close>
    for N and x a b :: \<open>'v literal\<close>
    by (metis add_mset_commute empty_iff member_add_mset
        mset_subset_eq_add_mset_cancel mset_subset_eq_insertD set_mset_empty)
  have le2_empty: \<open>D - {#a, b#} = {#} \<longleftrightarrow> D = {#} \<or> D = {#a#} \<or> D = {#b#} \<or> D = {#a, b#}\<close>
    for D and a b :: \<open>'v literal\<close>
    unfolding Diff_eq_empty_iff_mset
    by (cases D)
      (auto simp add: add_mset_eq_add_mset remove1_mset_empty_iff 1
        subset_eq_mset_single_iff)
  have 2: \<open>remove1_mset a N = C \<longleftrightarrow> (a \<notin># N \<and> N = C \<or> N = add_mset a C)\<close>
    for N C and a :: \<open>'v literal\<close>
    by (auto simp: add_mset_remove_trivial_If
        split: if_splits)
  have \<open>defined_lit M1 L\<close>
    using H[of M2' K M1] L Pos' Neg' M3 unfolding M2'_def
    by (cases L)
      (simp_all add: additional_constraint_def add_mset_eq_add_mset
        le2_empty 2 defined_lit_Neg_Pos_iff
        all_conj_distrib remove1_mset_empty_iff conj_disj_distribL)
  then show ?thesis
    using M3 unfolding M2'_def
    by (auto simp: defined_lit_append)
qed

lemma defined_replacement_additional_neg_orinal2:
  assumes
    def_neg: \<open>Neg (atm_of L\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S)\<close>
      \<open>additional_var (atm_of L) \<in> lits_of_l (trail S)\<close> and
    \<open>set_mset additional_constraints \<subseteq> set_mset (clauses S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    lev_L: \<open>get_level (trail S) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>1)) < backtrack_lvl S\<close> and
    lev_L': \<open>get_level (trail S) (additional_var (atm_of L)) < backtrack_lvl S\<close> and
    L: \<open>atm_of L \<in> \<Delta>\<Sigma>\<close> and
    n_d: \<open>no_dup (trail S)\<close>
  shows \<open>defined_lit (trail S) L\<close>
proof -
  define i where
    \<open>i = max (get_level (trail S) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>1))) (get_level (trail S) (additional_var (atm_of L)))\<close>
  have \<open>atm_of L \<in># mset_set \<Delta>\<Sigma>\<close>
    using L finite_\<Sigma> by auto
  then have H: \<open>\<And>M K M'. trail S = M' @ Decided K # M \<longrightarrow> (\<forall>D L'.
    D + {#L'#} \<in># additional_constraint (atm_of L) \<longrightarrow> undefined_lit M L' \<longrightarrow> \<not> M \<Turnstile>as CNot D)\<close>
    using smaller_propa assms(3) finite_\<Sigma> unfolding no_smaller_propa_def
      additional_constraints_def
    by (auto dest: multi_member_split)

  have \<open>i < backtrack_lvl S\<close>
    using lev_L lev_L' unfolding i_def by auto
  then obtain M1 M2 K where
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_K: \<open>get_level (trail S) K = Suc i\<close>
    using backtrack_ex_decomp[OF n_d] unfolding i_def
    by blast
  obtain M3 where
    M3: \<open>trail S = M3 @ M2 @ Decided K # M1\<close>
    using decomp by auto
  define M2' where
    \<open>M2' = M3 @ M2\<close>
  have \<open>undefined_lit (M2' @ Decided K # []) (Neg (atm_of L\<^sup>\<mapsto>\<^sup>1))\<close>
    using def_neg n_d lev_L lev_K i_def[symmetric]
    unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: get_level_append_if defined_lit_Neg_Pos_iff
        get_level_cons_if
        split: if_splits
        dest: no_dup_consistentD
        no_dup_append_in_atm_notin)
  then have Neg': \<open>Neg (atm_of L\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l M1\<close>
    using def_neg unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD no_dup_append_in_atm_notin)
  then have [iff]: \<open>defined_lit M1 (Pos (atm_of L\<^sup>\<mapsto>\<^sup>1))\<close>
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  have \<open>undefined_lit (M2' @ Decided K # []) (additional_var (atm_of L))\<close>
    using def_neg n_d lev_L' lev_K i_def[symmetric]
    unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: get_level_append_if defined_lit_Neg_Pos_iff
        get_level_cons_if
        split: if_splits
        dest: no_dup_consistentD
        no_dup_append_in_atm_notin)
  then have Pos': \<open>additional_var (atm_of L) \<in> lits_of_l M1\<close>
    using def_neg unfolding M3 M2'_def[symmetric] append_assoc[symmetric]
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD no_dup_append_in_atm_notin)
  then have [iff]: \<open>defined_lit M1 (additional_var (atm_of L))\<close>
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  have [iff]: \<open>atm_of L \<noteq> additional_atm (atm_of L)\<close>
    using L by auto
  have 1: \<open>add_mset x N \<subseteq># {#a, b#} \<longleftrightarrow> (x = a \<and> N \<subseteq># {#b#} \<or> x = b \<and> N \<subseteq># {#a#})\<close>
    for N and x a b :: \<open>'v literal\<close>
    by (metis add_mset_commute empty_iff member_add_mset
        mset_subset_eq_add_mset_cancel mset_subset_eq_insertD set_mset_empty)
  have le2_empty: \<open>D - {#a, b#} = {#} \<longleftrightarrow> D = {#} \<or> D = {#a#} \<or> D = {#b#} \<or> D = {#a, b#}\<close>
    for D and a b :: \<open>'v literal\<close>
    unfolding Diff_eq_empty_iff_mset
    by (cases D)
      (auto simp add: add_mset_eq_add_mset remove1_mset_empty_iff 1
        subset_eq_mset_single_iff)
  have 2: \<open>remove1_mset a N = C \<longleftrightarrow> (a \<notin># N \<and> N = C \<or> N = add_mset a C)\<close>
    for N C and a :: \<open>'v literal\<close>
    by (auto simp: add_mset_remove_trivial_If
        split: if_splits)
  have \<open>defined_lit M1 L\<close>
    using H[of M2' K M1] L Pos' Neg' M3 unfolding M2'_def
    by (cases L)
      (simp_all add: additional_constraint_def add_mset_eq_add_mset
        le2_empty 2 defined_lit_Neg_Pos_iff
        all_conj_distrib remove1_mset_empty_iff conj_disj_distribL)
  then show ?thesis
    using M3 unfolding M2'_def
    by (auto simp: defined_lit_append)
qed

lemma Neg_in_lits_of_l_definedD:
  \<open>Neg A \<in> lits_of_l M \<Longrightarrow> defined_lit M (Pos A)\<close>
  by (simp add: Decided_Propagated_in_iff_in_lits_of_l)

lemma propagation_one_lit_of_same_lvl:
  assumes
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_propa S\<close> and
    \<open>Propagated L E \<in> set (trail S)\<close> and
    rea: \<open>reasons_in_clauses S\<close> and
    nempty: \<open>E - {#L#} \<noteq> {#}\<close>
  shows
    \<open>\<exists>L' \<in># E - {#L#}. get_level (trail S) L = get_level (trail S) L'\<close>
proof (rule ccontr)
  assume H: \<open>\<not>?thesis\<close>
  have ns: \<open>\<And>M K M' D L.
       trail S = M' @ Decided K # M \<Longrightarrow>
       D + {#L#} \<in># clauses S \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close> and
    n_d: \<open>no_dup (trail S)\<close>
    using assms unfolding no_smaller_propa_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  obtain M1 M2 where M2: \<open>trail S = M2 @ Propagated L E # M1\<close>
    using assms by (auto dest!: split_list)

  have \<open>\<And>L mark a b.
         a @ Propagated L mark # b = trail S \<Longrightarrow>
         b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> and
    \<open>set (get_all_mark_of_propagated (trail S)) \<subseteq> set_mset (clauses S)\<close>
    using assms unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      reasons_in_clauses_def
    by auto
  from this(1)[OF M2[symmetric]] this(2)
  have \<open>M1 \<Turnstile>as CNot (remove1_mset L E)\<close> and \<open>L \<in># E\<close> and \<open>E \<in># clauses S\<close>
    by (auto simp: M2)
  then have lev_le:
    \<open>L' \<in># E - {#L#} \<Longrightarrow> get_level (trail S) L > get_level (trail S) L'\<close> and
    \<open>trail S \<Turnstile>as CNot (remove1_mset L E)\<close> for L'
    using H n_d defined_lit_no_dupD(1)[of M1 _ M2]
      count_decided_ge_get_level[of M1 L']
    by (auto simp: M2 get_level_append_if get_level_cons_if
        Decided_Propagated_in_iff_in_lits_of_l atm_of_eq_atm_of
        true_annots_append_l
        dest!: multi_member_split)
  define i where \<open>i = get_level (trail S) L - 1\<close>
  have \<open>i < local.backtrack_lvl S\<close> and \<open>get_level (trail S) L \<ge> 1\<close>
    \<open>get_level (trail S) L > i\<close> and
    i2: \<open>get_level (trail S) L = Suc i\<close>
    using lev_le nempty count_decided_ge_get_level[of \<open>trail S\<close> L] i_def
    by (cases \<open>E - {#L#}\<close>; force)+
  from backtrack_ex_decomp[OF n_d this(1)] obtain M3 M4 K where
    decomp: \<open>(Decided K # M3, M4) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_K: \<open>get_level (trail S) K = Suc i\<close>
    by blast
  then obtain M5 where
    tr: \<open>trail S = (M5 @ M4) @ Decided K # M3\<close>
    by auto
  define M4' where \<open>M4' = M5 @ M4\<close>
  have \<open>undefined_lit M3 L\<close>
    using n_d \<open>get_level (trail S) L > i\<close> lev_K
      count_decided_ge_get_level[of M3 L] unfolding tr M4'_def[symmetric]
    by (auto simp: get_level_append_if get_level_cons_if
        atm_of_eq_atm_of
        split: if_splits dest: defined_lit_no_dupD)
  moreover have \<open>M3 \<Turnstile>as CNot (remove1_mset L E)\<close>
    using \<open>trail S \<Turnstile>as CNot (remove1_mset L E)\<close> lev_K n_d
    unfolding true_annots_def true_annot_def
    apply clarsimp
    subgoal for L'
      using lev_le[of \<open>-L'\<close>] lev_le[of \<open>L'\<close>] lev_K
      unfolding i2
      unfolding  tr M4'_def[symmetric]
      by (auto simp: get_level_append_if get_level_cons_if
          atm_of_eq_atm_of if_distrib if_distribR Decided_Propagated_in_iff_in_lits_of_l
          split: if_splits dest: defined_lit_no_dupD
          dest!: multi_member_split)
    done
  ultimately show False
    using ns[OF tr, of \<open>remove1_mset L E\<close> L] \<open>E \<in># clauses S\<close> \<open>L \<in># E\<close>
    by auto
qed


lemma simple_backtrack_obacktrack:
  \<open>simple_backtrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S) \<Longrightarrow>
    enc_weight_opt.obacktrack S T\<close>
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
  apply (auto simp: simple_backtrack.simps
      enc_weight_opt.obacktrack.simps)
  apply (rule_tac x=L in exI)
  apply (rule_tac x=D in exI)
  apply auto
  apply (rule_tac x=K in exI)
  apply (rule_tac x=M1 in exI)
  apply auto
  apply (rule_tac x=D in exI)
  apply (auto simp:)
  done

end

interpretation test_real: optimal_encoding_opt where
  state_eq = \<open>(=)\<close> and
  state = id and
  trail = \<open>\<lambda>(M, N, U, D, W). M\<close> and
  init_clss = \<open>\<lambda>(M, N, U, D, W). N\<close> and
  learned_clss = \<open>\<lambda>(M, N, U, D, W). U\<close> and
  conflicting = \<open>\<lambda>(M, N, U, D, W). D\<close> and
  cons_trail = \<open>\<lambda>K (M, N, U, D, W). (K # M, N, U, D, W)\<close> and
  tl_trail = \<open>\<lambda>(M, N, U, D, W). (tl M, N, U, D, W)\<close> and
  add_learned_cls = \<open>\<lambda>C (M, N, U, D, W). (M, N, add_mset C U, D, W)\<close> and
  remove_cls = \<open>\<lambda>C (M, N, U, D, W). (M, removeAll_mset C N, removeAll_mset C U, D, W)\<close> and
  update_conflicting = \<open>\<lambda>C (M, N, U, _, W). (M, N, U, C, W)\<close> and
  init_state = \<open>\<lambda>N. ([], N, {#}, None, None, ())\<close> and
  \<rho> = \<open>\<lambda>_. (0::real)\<close> and
  update_additional_info = \<open>\<lambda>W (M, N, U, D, _, _). (M, N, U, D, W)\<close> and
  \<Sigma> = \<open>{1..(100::nat)}\<close> and
  \<Delta>\<Sigma> = \<open>{1..(50::nat)}\<close> and
  new_vars = \<open>\<lambda>n. (200 + 3*n, 200 + 3*n+1, 200 + 3*n+2)\<close>
  by unfold_locales

lemma mult3_inj:
  \<open>3 * A = Suc (3 * Aa) \<longleftrightarrow> False\<close> \<open>3 * A = Suc (Suc (3 * Aa)) \<longleftrightarrow> False\<close> for A Aa::nat
  by presburger+

interpretation test_real: optimal_encoding where
  state_eq = \<open>(=)\<close> and
  state = id and
  trail = \<open>\<lambda>(M, N, U, D, W). M\<close> and
  init_clss = \<open>\<lambda>(M, N, U, D, W). N\<close> and
  learned_clss = \<open>\<lambda>(M, N, U, D, W). U\<close> and
  conflicting = \<open>\<lambda>(M, N, U, D, W). D\<close> and
  cons_trail = \<open>\<lambda>K (M, N, U, D, W). (K # M, N, U, D, W)\<close> and
  tl_trail = \<open>\<lambda>(M, N, U, D, W). (tl M, N, U, D, W)\<close> and
  add_learned_cls = \<open>\<lambda>C (M, N, U, D, W). (M, N, add_mset C U, D, W)\<close> and
  remove_cls = \<open>\<lambda>C (M, N, U, D, W). (M, removeAll_mset C N, removeAll_mset C U, D, W)\<close> and
  update_conflicting = \<open>\<lambda>C (M, N, U, _, W). (M, N, U, C, W)\<close> and
  init_state = \<open>\<lambda>N. ([], N, {#}, None, None, ())\<close> and
  \<rho> = \<open>\<lambda>_. (0::real)\<close> and
  update_additional_info = \<open>\<lambda>W (M, N, U, D, _, _). (M, N, U, D, W)\<close> and
  \<Sigma> = \<open>{1..(100::nat)}\<close> and
  \<Delta>\<Sigma> = \<open>{1..(50::nat)}\<close> and
  new_vars = \<open>\<lambda>n. (200 + 3*n, 200 + 3*n+1, 200 + 3*n+2)\<close>
  by unfold_locales (auto simp: inj_on_def mult3_inj)

interpretation test_nat: optimal_encoding_opt where
  state_eq = \<open>(=)\<close> and
  state = id and
  trail = \<open>\<lambda>(M, N, U, D, W). M\<close> and
  init_clss = \<open>\<lambda>(M, N, U, D, W). N\<close> and
  learned_clss = \<open>\<lambda>(M, N, U, D, W). U\<close> and
  conflicting = \<open>\<lambda>(M, N, U, D, W). D\<close> and
  cons_trail = \<open>\<lambda>K (M, N, U, D, W). (K # M, N, U, D, W)\<close> and
  tl_trail = \<open>\<lambda>(M, N, U, D, W). (tl M, N, U, D, W)\<close> and
  add_learned_cls = \<open>\<lambda>C (M, N, U, D, W). (M, N, add_mset C U, D, W)\<close> and
  remove_cls = \<open>\<lambda>C (M, N, U, D, W). (M, removeAll_mset C N, removeAll_mset C U, D, W)\<close> and
  update_conflicting = \<open>\<lambda>C (M, N, U, _, W). (M, N, U, C, W)\<close> and
  init_state = \<open>\<lambda>N. ([], N, {#}, None, None, ())\<close> and
  \<rho> = \<open>\<lambda>_. (0::nat)\<close> and
  update_additional_info = \<open>\<lambda>W (M, N, U, D, _, _). (M, N, U, D, W)\<close> and
  \<Sigma> = \<open>{1..(100::nat)}\<close> and
  \<Delta>\<Sigma> = \<open>{1..(50::nat)}\<close> and
  new_vars = \<open>\<lambda>n. (200 + 3*n, 200 + 3*n+1, 200 + 3*n+2)\<close>
  by unfold_locales

interpretation test_nat: optimal_encoding where
  state_eq = \<open>(=)\<close> and
  state = id and
  trail = \<open>\<lambda>(M, N, U, D, W). M\<close> and
  init_clss = \<open>\<lambda>(M, N, U, D, W). N\<close> and
  learned_clss = \<open>\<lambda>(M, N, U, D, W). U\<close> and
  conflicting = \<open>\<lambda>(M, N, U, D, W). D\<close> and
  cons_trail = \<open>\<lambda>K (M, N, U, D, W). (K # M, N, U, D, W)\<close> and
  tl_trail = \<open>\<lambda>(M, N, U, D, W). (tl M, N, U, D, W)\<close> and
  add_learned_cls = \<open>\<lambda>C (M, N, U, D, W). (M, N, add_mset C U, D, W)\<close> and
  remove_cls = \<open>\<lambda>C (M, N, U, D, W). (M, removeAll_mset C N, removeAll_mset C U, D, W)\<close> and
  update_conflicting = \<open>\<lambda>C (M, N, U, _, W). (M, N, U, C, W)\<close> and
  init_state = \<open>\<lambda>N. ([], N, {#}, None, None, ())\<close> and
  \<rho> = \<open>\<lambda>_. (0::nat)\<close> and
  update_additional_info = \<open>\<lambda>W (M, N, U, D, _, _). (M, N, U, D, W)\<close> and
  \<Sigma> = \<open>{1..(100::nat)}\<close> and
  \<Delta>\<Sigma> = \<open>{1..(50::nat)}\<close> and
  new_vars = \<open>\<lambda>n. (200 + 3*n, 200 + 3*n+1, 200 + 3*n+2)\<close>
  by unfold_locales (auto simp: inj_on_def mult3_inj)


subsection \<open>Partial MAX-SAT\<close>

definition weight_on_clauses where
  \<open>weight_on_clauses N\<^sub>S \<rho> I = (\<Sum>C \<in># (filter_mset (\<lambda>C. I \<Turnstile> C) N\<^sub>S). \<rho> C)\<close>

definition atms_exactly_m :: \<open>'v partial_interp \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
  \<open>atms_exactly_m I N \<longleftrightarrow>
  total_over_m I (set_mset N) \<and>
  atms_of_s I \<subseteq> atms_of_mm N\<close>

text \<open>Partial in the name refers to the fact that not all clauses are soft clauses, not to the fact
  that we consider partial models.\<close>
inductive partial_max_sat :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> ('v clause \<Rightarrow> nat) \<Rightarrow>
  'v partial_interp option \<Rightarrow> bool\<close> where
  partial_max_sat:
  \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
if
  \<open>I \<Turnstile>sm N\<^sub>H\<close> and
  \<open>atms_exactly_m I ((N\<^sub>H + N\<^sub>S))\<close> and
  \<open>consistent_interp I\<close> and
  \<open>\<And>I'. consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<le> weight_on_clauses N\<^sub>S \<rho> I\<close> |
  partial_max_unsat:
  \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> None\<close>
if
  \<open>unsatisfiable (set_mset N\<^sub>H)\<close>

inductive partial_min_sat :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> ('v clause \<Rightarrow> nat) \<Rightarrow>
  'v partial_interp option \<Rightarrow> bool\<close> where
  partial_min_sat:
  \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
if
  \<open>I \<Turnstile>sm N\<^sub>H\<close> and
  \<open>atms_exactly_m I (N\<^sub>H + N\<^sub>S)\<close> and
  \<open>consistent_interp I\<close> and
  \<open>\<And>I'. consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<ge> weight_on_clauses N\<^sub>S \<rho> I\<close> |
  partial_min_unsat:
  \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> None\<close>
if
  \<open>unsatisfiable (set_mset N\<^sub>H)\<close>

lemma atms_exactly_m_finite:
  assumes \<open>atms_exactly_m I N\<close>
  shows \<open>finite I\<close>
proof -
  have \<open>I \<subseteq> Pos ` (atms_of_mm N) \<union> Neg ` atms_of_mm N\<close>
    using assms by (force simp: total_over_m_def  atms_exactly_m_def lit_in_set_iff_atm
        atms_of_s_def)
  from finite_subset[OF this] show ?thesis by auto
qed


lemma
  fixes N\<^sub>H :: \<open>'v clauses\<close>
  assumes \<open>satisfiable (set_mset N\<^sub>H)\<close>
  shows sat_partial_max_sat: \<open>\<exists>I. partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close> and
    sat_partial_min_sat: \<open>\<exists>I. partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
proof -
  let ?Is = \<open>{I. atms_exactly_m I ((N\<^sub>H + N\<^sub>S)) \<and>  consistent_interp I \<and>
     I \<Turnstile>sm N\<^sub>H}\<close>
  let ?Is'= \<open>{I. atms_exactly_m I ((N\<^sub>H + N\<^sub>S)) \<and> consistent_interp I \<and>
    I \<Turnstile>sm N\<^sub>H \<and> finite I}\<close>
  have Is: \<open>?Is = ?Is'\<close>
    by (auto simp: atms_of_s_def atms_exactly_m_finite)
  have \<open>?Is' \<subseteq> set_mset ` simple_clss (atms_of_mm (N\<^sub>H + N\<^sub>S))\<close>
    apply rule
    unfolding image_iff
    by (rule_tac x= \<open>mset_set x\<close> in bexI)
      (auto simp: simple_clss_def atms_exactly_m_def image_iff
        atms_of_s_def atms_of_def distinct_mset_mset_set consistent_interp_tuatology_mset_set)
  from finite_subset[OF this] have fin: \<open>finite ?Is\<close> unfolding Is
    by (auto simp: simple_clss_finite)
  then have fin': \<open>finite (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
    by auto
  define \<rho>I where
    \<open>\<rho>I = Min (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
  have nempty: \<open>?Is \<noteq> {}\<close>
  proof -
    obtain I where I:
      \<open>total_over_m I (set_mset N\<^sub>H)\<close>
      \<open>I \<Turnstile>sm N\<^sub>H\<close>
      \<open>consistent_interp I\<close>
      \<open>atms_of_s I \<subseteq> atms_of_mm N\<^sub>H\<close>
      using assms unfolding satisfiable_def_min atms_exactly_m_def
      by (auto simp: atms_of_s_def atm_of_def total_over_m_def)
    let ?I = \<open>I \<union> Pos ` {x \<in> atms_of_mm N\<^sub>S. x \<notin> atm_of ` I}\<close>
    have \<open>?I \<in> ?Is\<close>
      using I
      by (auto simp: atms_exactly_m_def total_over_m_alt_def image_iff
          lit_in_set_iff_atm)
        (auto simp: consistent_interp_def uminus_lit_swap)
    then show ?thesis
      by blast
  qed
  have \<open>\<rho>I \<in> weight_on_clauses N\<^sub>S \<rho> ` ?Is\<close>
    unfolding \<rho>I_def
    by (rule Min_in[OF fin']) (use nempty in auto)
  then obtain I :: \<open>'v partial_interp\<close> where
    \<open>weight_on_clauses N\<^sub>S \<rho> I = \<rho>I\<close> and
    \<open>I \<in> ?Is\<close>
    by blast
  then have H: \<open>consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<ge> weight_on_clauses N\<^sub>S \<rho> I\<close> for I'
    using Min_le[OF fin', of \<open>weight_on_clauses N\<^sub>S \<rho> I'\<close>]
    unfolding \<rho>I_def[symmetric]
    by auto
  then have \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    apply -
    by (rule partial_min_sat)
      (use fin \<open>I \<in> ?Is\<close> in \<open>auto simp: atms_exactly_m_finite\<close>)
  then show \<open>\<exists>I. partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    by fast

  define \<rho>I where
    \<open>\<rho>I = Max (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
  have \<open>\<rho>I \<in> weight_on_clauses N\<^sub>S \<rho> ` ?Is\<close>
    unfolding \<rho>I_def
    by (rule Max_in[OF fin']) (use nempty in auto)
  then obtain I :: \<open>'v partial_interp\<close> where
    \<open>weight_on_clauses N\<^sub>S \<rho> I = \<rho>I\<close> and
    \<open>I \<in> ?Is\<close>
    by blast
  then have H: \<open>consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>m N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<le> weight_on_clauses N\<^sub>S \<rho> I\<close> for I'
    using Max_ge[OF fin', of \<open>weight_on_clauses N\<^sub>S \<rho> I'\<close>]
    unfolding \<rho>I_def[symmetric]
    by auto
  then have \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    apply -
    by (rule partial_max_sat)
      (use fin \<open>I \<in> ?Is\<close> in \<open>auto simp: atms_exactly_m_finite
	consistent_interp_tuatology_mset_set\<close>)
  then show \<open>\<exists>I. partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    by fast
qed

inductive weight_sat
  :: \<open>'v clauses \<Rightarrow> ('v literal multiset \<Rightarrow> 'a :: linorder) \<Rightarrow>
    'v literal multiset option \<Rightarrow> bool\<close>
where
  weight_sat:
  \<open>weight_sat N \<rho> (Some I)\<close>
if
  \<open>set_mset I \<Turnstile>sm N\<close> and
  \<open>atms_exactly_m (set_mset I) N\<close> and
  \<open>consistent_interp (set_mset I)\<close> and
  \<open>distinct_mset I\<close>
  \<open>\<And>I'. consistent_interp (set_mset I') \<Longrightarrow> atms_exactly_m (set_mset I') N \<Longrightarrow> distinct_mset I' \<Longrightarrow>
      set_mset I' \<Turnstile>sm N \<Longrightarrow> \<rho> I' \<ge> \<rho> I\<close> |
  partial_max_unsat:
  \<open>weight_sat N \<rho> None\<close>
if
  \<open>unsatisfiable (set_mset N)\<close>

lemma partial_max_sat_is_weight_sat:
  fixes additional_atm :: \<open>'v clause \<Rightarrow> 'v\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> and
    N\<^sub>S :: \<open>'v clauses\<close>
  defines
    \<open>\<rho>' \<equiv> (\<lambda>C. sum_mset
       ((\<lambda>L. if L \<in> Pos ` additional_atm ` set_mset N\<^sub>S
	 then count N\<^sub>S (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
	   * \<rho> (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
	 else 0) `# C))\<close>
  assumes
    add: \<open>\<And>C. C \<in># N\<^sub>S \<Longrightarrow> additional_atm C \<notin> atms_of_mm (N\<^sub>H + N\<^sub>S)\<close>
    \<open>\<And>C D. C \<in># N\<^sub>S \<Longrightarrow> D \<in># N\<^sub>S \<Longrightarrow> additional_atm C = additional_atm D \<longleftrightarrow> C = D\<close> and
    w: \<open>weight_sat (N\<^sub>H + (\<lambda>C. add_mset (Pos (additional_atm C)) C) `# N\<^sub>S) \<rho>' (Some I)\<close>
  shows
    \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some {L \<in> set_mset I. atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)})\<close>
proof -
  define N where \<open>N \<equiv> N\<^sub>H + (\<lambda>C. add_mset (Pos (additional_atm C)) C) `# N\<^sub>S\<close>
  define cl_of where \<open>cl_of L = (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)\<close> for L
  from w
  have
    ent: \<open>set_mset I \<Turnstile>sm N\<close> and
    bi: \<open>atms_exactly_m (set_mset I) N\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    dist: \<open>distinct_mset I\<close> and
    weight: \<open>\<And>I'. consistent_interp (set_mset I') \<Longrightarrow> atms_exactly_m (set_mset I') N \<Longrightarrow>
      distinct_mset I' \<Longrightarrow> set_mset I' \<Turnstile>sm N \<Longrightarrow> \<rho>' I' \<ge> \<rho>' I\<close>
    unfolding N_def[symmetric]
    by (auto simp: weight_sat.simps)
  let ?I = \<open>{L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)}\<close>
  have ent': \<open>set_mset I \<Turnstile>sm N\<^sub>H\<close>
    using ent unfolding true_clss_restrict
    by (auto simp: N_def)
  then have ent': \<open>?I \<Turnstile>sm N\<^sub>H\<close>
    apply (subst (asm) true_clss_restrict[symmetric])
    apply (rule true_clss_mono_left, assumption)
    apply auto
    done
  have [simp]: \<open>atms_of_ms ((\<lambda>C. add_mset (Pos (additional_atm C)) C) ` set_mset N\<^sub>S) =
    additional_atm ` set_mset N\<^sub>S \<union> atms_of_ms (set_mset N\<^sub>S)\<close>
    by (auto simp: atms_of_ms_def)
  have bi': \<open>atms_exactly_m ?I (N\<^sub>H + N\<^sub>S)\<close>
    using bi
    by (auto simp: atms_exactly_m_def total_over_m_def total_over_set_def
        atms_of_s_def N_def)
  have cons': \<open>consistent_interp ?I\<close>
    using cons by (auto simp: consistent_interp_def)
  have [simp]: \<open>cl_of (Pos (additional_atm xb)) = xb\<close>
    if \<open>xb \<in># N\<^sub>S\<close> for xb
    using someI[of \<open>\<lambda>C. additional_atm xb = additional_atm C\<close> xb] add that
    unfolding cl_of_def
    by auto

  let ?I = \<open>{L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)} \<union> Pos ` additional_atm ` {C \<in> set_mset N\<^sub>S. \<not>set_mset I \<Turnstile> C}
    \<union> Neg ` additional_atm ` {C \<in> set_mset N\<^sub>S. set_mset I \<Turnstile> C}\<close>
  have \<open>consistent_interp ?I\<close>
    using cons add by (auto simp: consistent_interp_def
        atms_exactly_m_def uminus_lit_swap
        dest: add)
  moreover have \<open>atms_exactly_m ?I N\<close>
    using bi
    by (auto simp: N_def atms_exactly_m_def total_over_m_def
        total_over_set_def image_image)
  moreover have \<open>?I \<Turnstile>sm N\<close>
    using ent by (auto simp: N_def true_clss_def image_image
          atm_of_lit_in_atms_of true_cls_def
        dest!: multi_member_split)
  moreover have \<open>set_mset (mset_set ?I) = ?I\<close> and fin: \<open>finite ?I\<close>
    by (auto simp: atms_exactly_m_finite)
  moreover have \<open>distinct_mset (mset_set ?I)\<close>
    by (auto simp: distinct_mset_mset_set)
  ultimately have \<open>\<rho>' (mset_set ?I) \<ge> \<rho>' I\<close>
    using weight[of \<open>mset_set ?I\<close>]
    by argo
  moreover have \<open>\<rho>' (mset_set ?I) \<le> \<rho>' I\<close>
    using ent
    by (auto simp: \<rho>'_def sum_mset_inter_restrict[symmetric] mset_set_subset_iff N_def
        intro!: sum_image_mset_mono
        dest!: multi_member_split)
  ultimately have I_I: \<open>\<rho>' (mset_set ?I) = \<rho>' I\<close>
    by linarith

  have min: \<open>weight_on_clauses N\<^sub>S \<rho> I'
      \<le> weight_on_clauses N\<^sub>S \<rho> {L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)}\<close>
    if
      cons: \<open>consistent_interp I'\<close> and
      bit: \<open>atms_exactly_m I' (N\<^sub>H + N\<^sub>S)\<close> and
      I': \<open>I' \<Turnstile>sm N\<^sub>H\<close>
    for I'
  proof -
    let ?I' = \<open>I' \<union> Pos ` additional_atm ` {C \<in> set_mset N\<^sub>S. \<not>I' \<Turnstile> C}
      \<union> Neg ` additional_atm ` {C \<in> set_mset N\<^sub>S. I' \<Turnstile> C}\<close>
    have \<open>consistent_interp ?I'\<close>
      using cons bit add by (auto simp: consistent_interp_def
          atms_exactly_m_def uminus_lit_swap
          dest: add)
    moreover have \<open>atms_exactly_m ?I' N\<close>
      using bit
      by (auto simp: N_def atms_exactly_m_def total_over_m_def
          total_over_set_def image_image)
    moreover have \<open>?I' \<Turnstile>sm N\<close>
      using I' by (auto simp: N_def true_clss_def image_image
          dest!: multi_member_split)
    moreover have \<open>set_mset (mset_set ?I') = ?I'\<close> and fin: \<open>finite ?I'\<close>
      using bit by (auto simp: atms_exactly_m_finite)
    moreover have \<open>distinct_mset (mset_set ?I')\<close>
      by (auto simp: distinct_mset_mset_set)
    ultimately have I'_I: \<open>\<rho>' (mset_set ?I') \<ge> \<rho>' I\<close>
      using weight[of \<open>mset_set ?I'\<close>]
      by argo
    have inj: \<open>inj_on cl_of (I' \<inter> (\<lambda>x. Pos (additional_atm x)) ` set_mset N\<^sub>S)\<close> for I'
      using add by (auto simp: inj_on_def)

    have we: \<open>weight_on_clauses N\<^sub>S \<rho> I' = sum_mset (\<rho> `# N\<^sub>S) -
      sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S)\<close> for I'
      unfolding weight_on_clauses_def
      apply (subst (3) multiset_partition[of _ \<open>(\<Turnstile>) I'\<close>])
      unfolding image_mset_union sum_mset.union
      by (auto simp: comp_def)
    have H: \<open>sum_mset
       (\<rho> `#
	filter_mset (Not \<circ> (\<Turnstile>) {L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)})
	 N\<^sub>S) = \<rho>' I\<close>
	    unfolding I_I[symmetric] unfolding \<rho>'_def cl_of_def[symmetric]
	      sum_mset_sum_count if_distrib
	    apply (auto simp: sum_mset_sum_count image_image simp flip: sum.inter_restrict
	        cong: if_cong)
	    apply (subst comm_monoid_add_class.sum.reindex_cong[symmetric, of cl_of, OF _ refl])
	    apply ((use inj in auto; fail)+)[2]
	    apply (rule sum.cong)
	    apply auto[]
	    using inj[of \<open>set_mset I\<close>] \<open>set_mset I \<Turnstile>sm N\<close> assms(2)
	    apply (auto dest!: multi_member_split simp: N_def image_Int
	        atm_of_lit_in_atms_of true_cls_def)[]
	    using add apply (auto simp: true_cls_def)
	    done
    have \<open>(\<Sum>x\<in>(I' \<union> (\<lambda>x. Pos (additional_atm x)) ` {C. C \<in># N\<^sub>S \<and> \<not> I' \<Turnstile> C} \<union>
	 (\<lambda>x. Neg (additional_atm x)) ` {C. C \<in># N\<^sub>S \<and> I' \<Turnstile> C}) \<inter>
	(\<lambda>x. Pos (additional_atm x)) ` set_mset N\<^sub>S.
       count N\<^sub>S (cl_of x) * \<rho> (cl_of x))
    \<le> (\<Sum>A\<in>{a. a \<in># N\<^sub>S \<and> \<not> I' \<Turnstile> a}. count N\<^sub>S A * \<rho> A)\<close>
      apply (subst comm_monoid_add_class.sum.reindex_cong[symmetric, of cl_of, OF _ refl])
      apply ((use inj in auto; fail)+)[2]
      apply (rule ordered_comm_monoid_add_class.sum_mono2)
      using that add by (auto dest:  simp: N_def
          atms_exactly_m_def)
    then have \<open>sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S) \<ge> \<rho>' (mset_set ?I')\<close>
      using fin unfolding cl_of_def[symmetric] \<rho>'_def
      by (auto simp: \<rho>'_def
          simp add: sum_mset_sum_count image_image simp flip: sum.inter_restrict)
    then have \<open>\<rho>' I \<le> sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S)\<close>
      using I'_I by auto
    then show ?thesis
      unfolding we H I_I apply -
      by auto
  qed

  show ?thesis
    apply (rule partial_max_sat.intros)
    subgoal using ent' by auto
    subgoal using bi' by fast
    subgoal using cons' by fast
    subgoal for I'
      by (rule min)
    done
qed

lemma atms_exactly_m_alt_def:
  \<open>atms_exactly_m (set_mset y) N \<longleftrightarrow> atms_of y \<subseteq> atms_of_mm N \<and>
	total_over_m (set_mset y) (set_mset N)\<close>
  by (auto simp: atms_exactly_m_def atms_of_s_def atms_of_def
      atms_of_ms_def dest!: multi_member_split)

lemma atms_exactly_m_alt_def2:
  \<open>atms_exactly_m (set_mset y) N \<longleftrightarrow> atms_of y = atms_of_mm N\<close>
  by (metis atms_of_def atms_of_s_def atms_exactly_m_alt_def equalityI order_refl total_over_m_def
      total_over_set_alt_def)

lemma (in optimal_encoding) full_cdcl_bab_stgy_weight_sat:
  \<open>full cdcl_bab_stgy (init_state N) T \<Longrightarrow> distinct_mset_mset N \<Longrightarrow> weight_sat N \<rho> (weight T)\<close>
  using full_cdcl_bab_stgy_no_conflicting_clause_from_init_state[of N T]
  apply (cases \<open>weight T = None\<close>)
  subgoal
    by (auto intro!: weight_sat.intros(2))
  subgoal premises p
    using p(1-4,6)
    apply (clarsimp simp only:)
    apply (rule weight_sat.intros(1))
    subgoal by auto
    subgoal by (auto simp: atms_exactly_m_alt_def)
    subgoal by auto
    subgoal by auto
    subgoal for J I'
      using p(5)[of I'] by (auto simp: atms_exactly_m_alt_def2)
    done
  done

end
