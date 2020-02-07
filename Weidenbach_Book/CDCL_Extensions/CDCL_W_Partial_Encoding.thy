theory CDCL_W_Partial_Encoding
  imports CDCL_W_Optimal_Model
begin

(*TODO Move*)
lemma consistent_interp_unionI:
  \<open>consistent_interp A \<Longrightarrow> consistent_interp B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> -a \<notin> B) \<Longrightarrow> (\<And>a. a \<in> B \<Longrightarrow> -a \<notin> A) \<Longrightarrow>
    consistent_interp (A \<union> B)\<close>
  by (auto simp: consistent_interp_def)

lemma consistent_interp_poss: \<open>consistent_interp (Pos ` A)\<close> and
  consistent_interp_negs: \<open>consistent_interp (Neg ` A)\<close>
  by (auto simp: consistent_interp_def)

lemma Neg_in_lits_of_l_definedD:
  \<open>Neg A \<in> lits_of_l M \<Longrightarrow> defined_lit M (Pos A)\<close>
  by (simp add: Decided_Propagated_in_iff_in_lits_of_l)


subsection \<open>Encoding of partial SAT into total SAT\<close>

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
  We here formalise the encoding from a formula to another formula from which we will use to derive the
  optimal partial model.

  While the proofs are still inspired by Dominic Zimmer's upcoming bachelor thesis, we now use the dual
  rail encoding, which is more elegant that the solution found by Christoph to solve the problem.

  The intended meaning is the following:
  \<^item> \<^term>\<open>\<Sigma>\<close> is the set of all variables
  \<^item> \<^term>\<open>\<Delta>\<Sigma>\<close> is the set of all variables with a (possibly non-zero) weight: These are the variable that needs
    to be replaced during encoding, but it does not matter if the weight 0.
\<close>
locale optimal_encoding_opt_ops = 
  fixes \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin

abbreviation replacement_pos :: \<open>'v \<Rightarrow> 'v\<close> (\<open>(_)\<^sup>\<mapsto>\<^sup>1\<close> 100) where
  \<open>replacement_pos A \<equiv> fst (new_vars A)\<close>

abbreviation replacement_neg :: \<open>'v \<Rightarrow> 'v\<close> (\<open>(_)\<^sup>\<mapsto>\<^sup>0\<close> 100) where
  \<open>replacement_neg A \<equiv> snd (new_vars A)\<close>


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
     {#{#Neg (A\<^sup>\<mapsto>\<^sup>1), Neg (A\<^sup>\<mapsto>\<^sup>0)#}#}\<close>

definition additional_constraints :: \<open>'v clauses\<close> where
  \<open>additional_constraints = \<Union>#(additional_constraint `# (mset_set \<Delta>\<Sigma>))\<close>

definition penc :: \<open>'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>penc N = encode_clauses N + additional_constraints\<close>

lemma size_encode_clauses[simp]: \<open>size (encode_clauses N) = size N\<close>
  by (auto simp: encode_clauses_def)

lemma size_penc:
  \<open>size (penc N) = size N + card \<Delta>\<Sigma>\<close>
  by (auto simp: penc_def additional_constraints_def
      additional_constraint_def size_Union_mset_image_mset)

lemma atms_of_mm_additional_constraints: \<open>finite \<Delta>\<Sigma> \<Longrightarrow>
   atms_of_mm additional_constraints = replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
  by (auto simp: additional_constraints_def additional_constraint_def atms_of_ms_def)

lemma atms_of_mm_encode_clause_subset:
  \<open>atms_of_mm (encode_clauses N) \<subseteq> (atms_of_mm N - \<Delta>\<Sigma>) \<union> replacement_pos ` {A \<in> \<Delta>\<Sigma>. A \<in> atms_of_mm N}
    \<union> replacement_neg ` {A \<in> \<Delta>\<Sigma>. A \<in> atms_of_mm N}\<close>
  by (auto simp: encode_clauses_def encode_lit_alt_def atms_of_ms_def atms_of_def
      encode_clause_def split: if_splits
      dest!: multi_member_split[of _ N])

text \<open>In every meaningful application of the theorem below, we have \<open>\<Delta>\<Sigma> \<subseteq> atms_of_mm N\<close>.\<close>
lemma atms_of_mm_penc_subset: \<open>finite \<Delta>\<Sigma> \<Longrightarrow>
  atms_of_mm (penc N) \<subseteq> atms_of_mm N \<union> replacement_pos ` \<Delta>\<Sigma>
      \<union> replacement_neg ` \<Delta>\<Sigma> \<union> \<Delta>\<Sigma>\<close>
  using atms_of_mm_encode_clause_subset[of N]
  by (auto simp: penc_def atms_of_mm_additional_constraints)

lemma atms_of_mm_encode_clause_subset2: \<open>finite \<Delta>\<Sigma> \<Longrightarrow> \<Delta>\<Sigma> \<subseteq> atms_of_mm N \<Longrightarrow>
  atms_of_mm N \<subseteq> atms_of_mm (encode_clauses N) \<union> \<Delta>\<Sigma>\<close>
  by (auto simp: encode_clauses_def encode_lit_alt_def atms_of_ms_def atms_of_def
      encode_clause_def split: if_splits
      dest!: multi_member_split[of _ N])

lemma atms_of_mm_penc_subset2: \<open>finite \<Delta>\<Sigma> \<Longrightarrow> \<Delta>\<Sigma> \<subseteq> atms_of_mm N \<Longrightarrow>
  atms_of_mm (penc N) = (atms_of_mm N - \<Delta>\<Sigma>) \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
  using atms_of_mm_encode_clause_subset[of N] atms_of_mm_encode_clause_subset2[of N]
  by (auto simp: penc_def atms_of_mm_additional_constraints)

theorem card_atms_of_mm_penc:
  assumes \<open>finite \<Delta>\<Sigma>\<close> and  \<open>\<Delta>\<Sigma> \<subseteq> atms_of_mm N\<close>
  shows \<open>card (atms_of_mm (penc N)) \<le> card (atms_of_mm N - \<Delta>\<Sigma>) + 2 * card \<Delta>\<Sigma>\<close> (is \<open>?A \<le> ?B\<close>)
proof -
  have \<open>?A = card
     ((atms_of_mm N - \<Delta>\<Sigma>) \<union> replacement_pos ` \<Delta>\<Sigma> \<union>
      replacement_neg ` \<Delta>\<Sigma>)\<close> (is \<open>_ = card (?W \<union> ?X \<union> ?Y)\<close>)
    using arg_cong[OF atms_of_mm_penc_subset2[of N], of card] assms card_Un_le
    by auto
  also have \<open>... \<le> card (?W \<union> ?X) + card ?Y\<close>
    using card_Un_le[of \<open>?W \<union> ?X\<close> ?Y] by auto
  also have \<open>... \<le> card ?W + card ?X + card ?Y\<close>
    using card_Un_le[of \<open>?W\<close> ?X] by auto
  also have \<open>... \<le>  card (atms_of_mm N - \<Delta>\<Sigma>) + 2 * card \<Delta>\<Sigma>\<close>
    using card_mono[of \<open>atms_of_mm N\<close> \<open>\<Delta>\<Sigma>\<close>] assms
      card_image_le[of \<Delta>\<Sigma> replacement_pos] card_image_le[of \<Delta>\<Sigma> replacement_neg]
    by auto
  finally show ?thesis .
qed

definition postp :: \<open>'v partial_interp \<Rightarrow> 'v partial_interp\<close> where
  \<open>postp I =
     {A \<in> I. atm_of A \<notin> \<Delta>\<Sigma> \<and> atm_of A \<in> \<Sigma>} \<union> Pos ` {A. A \<in> \<Delta>\<Sigma> \<and> Pos (replacement_pos A) \<in> I}
       \<union> Neg ` {A. A \<in> \<Delta>\<Sigma> \<and> Pos (replacement_neg A) \<in> I \<and> Pos (replacement_pos A) \<notin> I}\<close>

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
  \<open>\<Sigma>\<^sub>a\<^sub>d\<^sub>d = replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>


definition upostp :: \<open>'v partial_interp \<Rightarrow> 'v partial_interp\<close> where
  \<open>upostp I =
     Neg ` {A \<in> \<Sigma>. A \<notin> \<Delta>\<Sigma> \<and> Pos A \<notin> I \<and> Neg A \<notin> I}
     \<union> {A \<in> I. atm_of A \<in> \<Sigma> \<and> atm_of A \<notin> \<Delta>\<Sigma>}
     \<union> Pos ` replacement_pos ` {A \<in> \<Delta>\<Sigma>. Pos A \<in> I}
     \<union> Neg ` replacement_pos ` {A \<in> \<Delta>\<Sigma>. Pos A \<notin> I}
     \<union> Pos ` replacement_neg ` {A \<in> \<Delta>\<Sigma>. Neg A \<in> I}
     \<union> Neg ` replacement_neg ` {A \<in> \<Delta>\<Sigma>. Neg A \<notin> I}\<close>

lemma atm_of_upostp_subset:
  \<open>atm_of ` (upostp I) \<subseteq>
    (atm_of ` I - \<Delta>\<Sigma>) \<union> replacement_pos ` \<Delta>\<Sigma> \<union>
    replacement_neg ` \<Delta>\<Sigma> \<union> \<Sigma>\<close>
  by (auto simp: upostp_def image_Un)

end


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
     init_state \<rho>
     update_additional_info +
  optimal_encoding_opt_ops \<Sigma> \<Delta>\<Sigma> new_vars
  for
    state_eq :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
        'v clause option \<times> 'b" and
    trail :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits\<close> and
    init_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    learned_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    conflicting :: \<open>'st \<Rightarrow> 'v clause option\<close> and

    cons_trail :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    add_learned_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    update_conflicting :: \<open>'v clause option \<Rightarrow> 'st \<Rightarrow> 'st\<close> and

    init_state :: \<open>'v clauses \<Rightarrow> 'st\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin


inductive odecide :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
  odecide_noweight: \<open>odecide S T\<close>
if
  \<open>conflicting S = None\<close> and
  \<open>undefined_lit (trail S) L\<close> and
  \<open>atm_of L \<in> atms_of_mm (init_clss S)\<close> and
  \<open>T \<sim> cons_trail (Decided L) S\<close> and
  \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma>\<close> |
  odecide_replacement_pos: \<open>odecide S T\<close>
if
  \<open>conflicting S = None\<close> and
  \<open>undefined_lit (trail S) (Pos (replacement_pos L))\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_pos L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close> |
  odecide_replacement_neg: \<open>odecide S T\<close>
if
  \<open>conflicting S = None\<close> and
  \<open>undefined_lit (trail S) (Pos (replacement_neg L))\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_neg L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close>

inductive_cases odecideE: \<open>odecide S T\<close>

definition no_new_lonely_clause :: \<open>'v clause \<Rightarrow> bool\<close> where
  \<open>no_new_lonely_clause C \<longleftrightarrow>
    (\<forall>L \<in> \<Delta>\<Sigma>. L \<in> atms_of C \<longrightarrow>
      Neg (replacement_pos L) \<in># C \<or> Neg (replacement_neg L) \<in># C \<or> C \<in># additional_constraint L)\<close>

definition lonely_weighted_lit_decided where
  \<open>lonely_weighted_lit_decided S \<longleftrightarrow>
    (\<forall>L \<in> \<Delta>\<Sigma>. Decided (Pos L) \<notin> set (trail S) \<and> Decided (Neg L) \<notin> set (trail S))\<close>

end

locale optimal_encoding_ops = optimal_encoding_opt_ops
    \<Sigma> \<Delta>\<Sigma>
    new_vars +
  ocdcl_weight \<rho>
  for
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> +
  assumes
    finite_\<Sigma>:
    \<open>finite \<Delta>\<Sigma>\<close> and
    \<Delta>\<Sigma>_\<Sigma>:
    \<open>\<Delta>\<Sigma> \<subseteq> \<Sigma>\<close> and
    new_vars_pos:
    \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_pos A \<notin> \<Sigma>\<close> and
    new_vars_neg:
    \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_neg A \<notin> \<Sigma>\<close> and
    new_vars_dist:
    \<open>inj_on replacement_pos \<Delta>\<Sigma>\<close>
    \<open>inj_on replacement_neg \<Delta>\<Sigma>\<close>
    \<open>replacement_pos ` \<Delta>\<Sigma> \<inter> replacement_neg ` \<Delta>\<Sigma> = {}\<close> and
    \<Sigma>_no_weight:
      \<open>atm_of C \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> \<rho> (add_mset C M) = \<rho> M\<close>
begin

lemma new_vars_dist2:
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_pos A \<noteq> replacement_pos B\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_neg A \<noteq> replacement_neg B\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> B \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_neg A \<noteq> replacement_pos B\<close>
  using new_vars_dist unfolding inj_on_def apply blast
  using new_vars_dist unfolding inj_on_def apply blast
  using new_vars_dist unfolding inj_on_def apply blast
  done

lemma consistent_interp_postp:
  \<open>consistent_interp I \<Longrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def uminus_lit_swap)

text \<open>The reverse of the previous theorem does not hold due to the filtering on the variables of
  \<^term>\<open>\<Delta>\<Sigma>\<close>. One example of version that holds:\<close>
lemma
  assumes \<open>A \<in> \<Delta>\<Sigma>\<close>
  shows \<open>consistent_interp (postp {Pos A , Neg A})\<close> and
    \<open>\<not>consistent_interp {Pos A, Neg A}\<close>
  using assms \<Delta>\<Sigma>_\<Sigma>
  by (auto simp: consistent_interp_def postp_def uminus_lit_swap)

text \<open>Some more restricted version of the reverse hold, like:\<close>
lemma consistent_interp_postp_iff:
  \<open>atm_of ` I \<subseteq> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> consistent_interp I \<longleftrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def uminus_lit_swap)

lemma new_vars_different_iff[simp]:
  \<open>A \<noteq> x\<^sup>\<mapsto>\<^sup>1\<close>
  \<open>A \<noteq> x\<^sup>\<mapsto>\<^sup>0\<close>
  \<open>x\<^sup>\<mapsto>\<^sup>1 \<noteq> A\<close>
  \<open>x\<^sup>\<mapsto>\<^sup>0 \<noteq> A\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>0 \<noteq> x\<^sup>\<mapsto>\<^sup>1\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>1 \<noteq> x\<^sup>\<mapsto>\<^sup>0\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>0 = x\<^sup>\<mapsto>\<^sup>0 \<longleftrightarrow> A = x\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>1 = x\<^sup>\<mapsto>\<^sup>1 \<longleftrightarrow> A = x\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>1) \<notin> \<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>0) \<notin> \<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>1) \<notin> \<Delta>\<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>0) \<notin> \<Delta>\<Sigma>\<close>if \<open>A \<in> \<Delta>\<Sigma>\<close>  \<open>x \<in> \<Delta>\<Sigma>\<close> for A x
  using \<Delta>\<Sigma>_\<Sigma> new_vars_pos[of x] new_vars_pos[of A]  new_vars_neg[of x] new_vars_neg[of A]
    new_vars_neg new_vars_dist2[of A x] new_vars_dist2[of x A] that
  by (cases \<open>A = x\<close>; fastforce simp: comp_def; fail)+

lemma consistent_interp_upostp:
  \<open>consistent_interp I \<Longrightarrow> consistent_interp (upostp I)\<close>
  using \<Delta>\<Sigma>_\<Sigma>
  by (auto simp: consistent_interp_def upostp_def uminus_lit_swap)


lemma atm_of_upostp_subset2:
  \<open>atm_of ` I \<subseteq> \<Sigma> \<Longrightarrow> replacement_pos ` \<Delta>\<Sigma> \<union>
    replacement_neg ` \<Delta>\<Sigma> \<union> (\<Sigma> - \<Delta>\<Sigma>) \<subseteq> atm_of ` (upostp I)\<close>
  apply (auto simp: upostp_def image_Un image_image)
   apply (metis (mono_tags, lifting) imageI literal.sel(1) mem_Collect_eq)
  apply (metis (mono_tags, lifting) imageI literal.sel(2) mem_Collect_eq)
  done


lemma \<Delta>\<Sigma>_notin_upost[simp]:
   \<open>y \<in> \<Delta>\<Sigma> \<Longrightarrow> Neg y \<notin> upostp I\<close>
   \<open>y \<in> \<Delta>\<Sigma> \<Longrightarrow> Pos y \<notin> upostp I\<close>
  using \<Delta>\<Sigma>_\<Sigma> by (auto simp: upostp_def)

lemma penc_ent_upostp: (* \htmllink{ocdcl-enc-upostp-model} *)
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>I \<Turnstile>sm N\<close> and
    cons: \<open>consistent_interp I\<close> and
    atm: \<open>atm_of ` I \<subseteq> atms_of_mm N\<close>
  shows \<open>upostp I \<Turnstile>m penc N\<close>
proof -
  have [iff]: \<open>Pos (A\<^sup>\<mapsto>\<^sup>0) \<notin> I\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<notin> I\<close>
    \<open>Neg (A\<^sup>\<mapsto>\<^sup>0) \<notin> I\<close> \<open>Neg (A\<^sup>\<mapsto>\<^sup>1) \<notin> I\<close>  if \<open>A \<in> \<Delta>\<Sigma>\<close> for A
    using atm new_vars_neg[of A] new_vars_pos[of A] that
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
    if \<open>y \<in> \<Delta>\<Sigma>\<close> for y
    using that
    by (cases \<open>Pos y \<in> I\<close>; auto simp: upostp_def image_image; fail)+
  have H:
    \<open>Neg (y\<^sup>\<mapsto>\<^sup>0) \<notin> upostp I \<Longrightarrow> Neg (y\<^sup>\<mapsto>\<^sup>1) \<in> upostp I\<close>
    if \<open>y \<in> \<Delta>\<Sigma>\<close> for y
    using that cons \<Delta>\<Sigma>_\<Sigma> unfolding upostp_def consistent_interp_def
    by (cases \<open>Pos y \<in> I\<close>) (auto simp:  image_image)
  have [dest]: \<open>Neg A \<in> upostp I \<Longrightarrow> Pos A \<notin> upostp I\<close>
    \<open>Pos A \<in> upostp I \<Longrightarrow> Neg A \<notin> upostp I\<close> for A
    using consistent_interp_upostp[OF cons]
    by (auto simp: consistent_interp_def)

  have add: \<open>upostp I \<Turnstile>m additional_constraints\<close>
    using finite_\<Sigma> H
    by (auto simp: additional_constraints_def true_cls_mset_def additional_constraint_def)

  show \<open>upostp I \<Turnstile>m penc N\<close>
    using enc add unfolding penc_def by auto
qed

lemma penc_ent_postp: (*  \htmllink{ocdcl-enc-postp-model} *)
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>I \<Turnstile>sm penc N\<close> and
    cons: \<open>consistent_interp I\<close>
  shows \<open>postp I \<Turnstile>m N\<close>
proof -
  have enc: \<open>I \<Turnstile>m encode_clauses N\<close> and \<open>I \<Turnstile>m additional_constraints\<close>
    using sat unfolding penc_def
    by auto
  have [dest]: \<open>Pos (x2\<^sup>\<mapsto>\<^sup>0) \<in> I \<Longrightarrow> Neg (x2\<^sup>\<mapsto>\<^sup>1) \<in> I\<close> if \<open>x2 \<in> \<Delta>\<Sigma>\<close> for x2
    using \<open>I \<Turnstile>m additional_constraints\<close> that cons
    multi_member_split[of x2 \<open>mset_set \<Delta>\<Sigma>\<close>] finite_\<Sigma>
    unfolding additional_constraints_def additional_constraint_def
      consistent_interp_def
    by (auto simp: true_cls_mset_def)
  have [dest]: \<open>Pos (x2\<^sup>\<mapsto>\<^sup>0) \<in> I \<Longrightarrow> Pos (x2\<^sup>\<mapsto>\<^sup>1) \<notin> I\<close> if \<open>x2 \<in> \<Delta>\<Sigma>\<close> for x2
    using that cons
    unfolding consistent_interp_def
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
      using cons finite_\<Sigma> sat
        preprocess_clss_model_additional_variables2[of _ I]
        \<Sigma> \<open>C \<in># N\<close> in_m_in_literals
      apply (auto simp: encode_clause_def postp_def encode_lit_alt_def
          split: if_splits
          dest!: multi_member_split[of _ C])
          using image_iff apply fastforce
          apply (case_tac xa; auto)
          apply auto
          done
       (*TODO proof*)
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

lemma satisfiable_penc_iff:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close>
  shows \<open>satisfiable (set_mset (penc N)) \<longleftrightarrow> satisfiable (set_mset N)\<close>
  using assms satisfiable_penc satisfiable_penc_satisfiable by blast


abbreviation \<rho>\<^sub>e_filter :: \<open>'v literal multiset \<Rightarrow> 'v literal multiset\<close> where
  \<open>\<rho>\<^sub>e_filter M \<equiv> {#L \<in># poss (mset_set \<Delta>\<Sigma>). Pos (atm_of L\<^sup>\<mapsto>\<^sup>1) \<in># M#} +
     {#L \<in># negs (mset_set \<Delta>\<Sigma>). Pos (atm_of L\<^sup>\<mapsto>\<^sup>0) \<in># M#}\<close>

lemma finite_upostp: \<open>finite I  \<Longrightarrow> finite \<Sigma> \<Longrightarrow> finite (upostp I)\<close>
  using finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
  by (auto simp: upostp_def)

declare finite_\<Sigma>[simp]

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
      distinct_mset_set_def)

lemma distinct_mset_penc:
  \<open>atms_of_mm N \<subseteq> \<Sigma> \<Longrightarrow> distinct_mset_mset (penc N) \<longleftrightarrow> distinct_mset_mset N\<close>
  by (auto simp: penc_def
      distinct_mset_encodes_clause_iff)

lemma finite_postp: \<open>finite I \<Longrightarrow> finite (postp I)\<close>
  by (auto simp: postp_def)

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

definition \<rho>\<^sub>e :: \<open>'v literal multiset \<Rightarrow> 'a :: {linorder}\<close> where
  \<open>\<rho>\<^sub>e M = \<rho> (\<rho>\<^sub>e_filter M)\<close>

lemma \<Sigma>_no_weight_\<rho>\<^sub>e: \<open>atm_of C \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> \<rho>\<^sub>e (add_mset C M) = \<rho>\<^sub>e M\<close>
  using \<Sigma>_no_weight[of C \<open>\<rho>\<^sub>e_filter M\<close>]
  apply (auto simp: \<rho>\<^sub>e_def finite_\<Sigma> image_mset_mset_set inj_on_Neg inj_on_Pos)
  by (smt Collect_cong image_iff literal.sel(1) literal.sel(2) new_vars_neg new_vars_pos)

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

lemma \<rho>\<^sub>e_mono: \<open>distinct_mset B \<Longrightarrow> A \<subseteq># B \<Longrightarrow> \<rho>\<^sub>e A \<le> \<rho>\<^sub>e B\<close>
  unfolding \<rho>\<^sub>e_def
  apply (rule \<rho>_mono)
  subgoal
    by (subst distinct_mset_add)
      (auto simp: distinct_image_mset_inj distinct_mset_filter distinct_mset_mset_set inj_on_Pos
        mset_inter_empty_set_mset image_mset_mset_set inj_on_Neg)
  subgoal
    by (rule subset_mset.add_mono; rule filter_mset_mono_subset) auto
  done


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
         atm_of x \<notin> replacement_neg ` \<Delta>\<Sigma>} = mset_set I\<close>
    using I_\<Sigma> by auto
  have [simp]: \<open>finite {A \<in> \<Delta>\<Sigma>. P A}\<close> for P
    by (rule finite_subset[of _ \<Delta>\<Sigma>])
      (use \<Delta>\<Sigma>_\<Sigma> finite_\<Sigma> in auto)
  have [dest]: \<open>xa \<in> \<Delta>\<Sigma> \<Longrightarrow> Pos (xa\<^sup>\<mapsto>\<^sup>1) \<in> upostp I \<Longrightarrow> Pos (xa\<^sup>\<mapsto>\<^sup>0) \<in> upostp I \<Longrightarrow> False\<close> for xa
    using cons unfolding penc_def
    by (auto simp: additional_constraint_def additional_constraints_def
      true_cls_mset_def consistent_interp_def upostp_def)
  have \<open>?A \<le> ?B\<close>
    using assms \<Delta>\<Sigma>_\<Sigma> apply -
    unfolding \<rho>\<^sub>e_def filter_filter_mset
    apply (rule \<rho>_mono2)
    subgoal using cons by auto
    subgoal using distinct_mset_mset_set by auto
    subgoal by auto
    subgoal by auto
    apply (rule filter_mset_mono_subset)
    subgoal
      by (subst distinct_subseteq_iff[symmetric])
        (auto simp: upostp_def simp: image_mset_mset_set inj_on_Neg inj_on_Pos
           distinct_mset_add mset_inter_empty_set_mset distinct_mset_mset_set)
    subgoal for x
      by (cases \<open>x \<in> I\<close>; cases x) (auto simp: upostp_def)
    done
  moreover have \<open>?B \<le> ?A\<close>
    using assms \<Delta>\<Sigma>_\<Sigma> apply -
    unfolding \<rho>\<^sub>e_def filter_filter_mset
    apply (rule \<rho>_mono2)
    subgoal using cons by (auto intro:
      intro: consistent_interp_subset[of _ \<open>Pos ` \<Delta>\<Sigma>\<close>]
      intro: consistent_interp_subset[of _ \<open>Neg ` \<Delta>\<Sigma>\<close>]
      intro!: consistent_interp_unionI
      simp: consistent_interp_upostp finite_upostp consistent_interp_poss
        consistent_interp_negs)
    subgoal by (auto
      simp: distinct_mset_mset_set distinct_mset_add image_mset_mset_set inj_on_Pos inj_on_Neg
        mset_inter_empty_set_mset)
    subgoal by auto
    subgoal by auto (*TODO Proof *)
    apply (auto simp: image_mset_mset_set inj_on_Neg inj_on_Pos)
      apply (subst distinct_subseteq_iff[symmetric])
      apply (auto simp: distinct_mset_mset_set distinct_mset_add image_mset_mset_set inj_on_Pos inj_on_Neg
        mset_inter_empty_set_mset finite_upostp)
        apply (metis image_eqI literal.exhaust_sel)
    apply (auto simp: upostp_def image_image)
    apply (metis (mono_tags, lifting) imageI literal.collapse(1) literal.collapse(2) mem_Collect_eq)
    apply (metis (mono_tags, lifting) imageI literal.collapse(1) literal.collapse(2) mem_Collect_eq)
    apply (metis (mono_tags, lifting) imageI literal.collapse(1) literal.collapse(2) mem_Collect_eq)
    done
  ultimately show ?thesis
    by simp
qed

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
    update_additional_info
    \<Sigma> \<Delta>\<Sigma>
    \<rho>
    new_vars +
    optimal_encoding_ops
    \<Sigma> \<Delta>\<Sigma>
    new_vars \<rho>
  for
    state_eq :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
        'v clause option \<times> 'b" and
    trail :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits\<close> and
    init_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    learned_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    conflicting :: \<open>'st \<Rightarrow> 'v clause option\<close> and
    cons_trail :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    add_learned_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    update_conflicting :: \<open>'v clause option \<Rightarrow> 'st \<Rightarrow> 'st\<close> and

    init_state :: \<open>'v clauses \<Rightarrow> 'st\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close> 
begin


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

theorem full_encoding_OCDCL_correctness: (* \htmllink{ocdcl-partial-enc-correctness} *)
  assumes
    st: \<open>full enc_weight_opt.cdcl_bnb_stgy (init_state (penc N)) T\<close> and
    dist: \<open>distinct_mset_mset N\<close> and
    atms: \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> postp (set_mset (the (weight T))) \<Turnstile>sm N\<close>
    \<open>weight T \<noteq> None \<Longrightarrow> distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow>
      atms_of I \<subseteq> atms_of_mm N \<Longrightarrow> set_mset I \<Turnstile>sm N \<Longrightarrow>
      \<rho> I \<ge> \<rho> (mset_set (postp (set_mset (the (weight T)))))\<close>
    \<open>weight T \<noteq> None \<Longrightarrow> \<rho>\<^sub>e (the (enc_weight_opt.weight T)) =
      \<rho> (mset_set (postp (set_mset (the (enc_weight_opt.weight T)))))\<close>
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
      set_mset I \<Turnstile>sm ?N \<Longrightarrow> Found (\<rho>\<^sub>e I) \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
    for I
    using enc_weight_opt.full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state[of
        \<open>penc N\<close> T, OF st]
    by fast+

  show \<open>unsatisfiable (set_mset N)\<close> if \<open>weight T = None\<close>
    using unsat[OF that] satisfiable_penc[OF atms] by blast
  let ?K = \<open>postp (set_mset (the (weight T)))\<close>
  show \<open>?K \<Turnstile>sm N\<close> if \<open>weight T \<noteq> None\<close>
    using penc_ent_postp[OF atms, of \<open>set_mset (the (weight T))\<close>] model[OF that]
    by auto

  assume Some: \<open>weight T \<noteq> None\<close>
  have Some': \<open>enc_weight_opt.weight T \<noteq> None\<close>
    using Some by auto
  have cons_K: \<open>consistent_interp ?K\<close>
    using model Some by (auto simp: consistent_interp_postp)
  define J where \<open>J = the (weight T)\<close>
  then have [simp]: \<open>weight T = Some J\<close> \<open>enc_weight_opt.weight T = Some J\<close>
    using Some by auto
  have \<open>set_mset J \<Turnstile>sm additional_constraints\<close>
    using model by (auto simp: penc_def)
  then have H: \<open>x \<in> \<Delta>\<Sigma> \<Longrightarrow> Neg (replacement_pos x) \<in># J \<or> Neg (replacement_neg x) \<in># J\<close> and
    [dest]: \<open>Pos (xa\<^sup>\<mapsto>\<^sup>1) \<in># J \<Longrightarrow> Pos (xa\<^sup>\<mapsto>\<^sup>0) \<in># J \<Longrightarrow> xa \<in> \<Delta>\<Sigma> \<Longrightarrow> False\<close>  for x xa
    using model
    apply (auto simp: additional_constraints_def additional_constraint_def true_clss_def
      consistent_interp_def)
      by (metis uminus_Pos)
  have cons_f: \<open>consistent_interp (set_mset (\<rho>\<^sub>e_filter (the (weight T))))\<close>
    using model
    by (auto simp: postp_def \<rho>\<^sub>e_def \<Sigma>\<^sub>a\<^sub>d\<^sub>d_def conj_disj_distribR
        consistent_interp_poss
        consistent_interp_negs
        mset_set_Union intro!: consistent_interp_unionI
        intro: consistent_interp_subset distinct_mset_mset_set
        consistent_interp_subset[of _ \<open>Pos ` \<Delta>\<Sigma>\<close>]
        consistent_interp_subset[of _ \<open>Neg ` \<Delta>\<Sigma>\<close>])
  have dist_f: \<open>distinct_mset ((\<rho>\<^sub>e_filter (the (weight T))))\<close>
    using model
    by  (auto simp: postp_def simp: image_mset_mset_set inj_on_Neg inj_on_Pos
           distinct_mset_add mset_inter_empty_set_mset distinct_mset_mset_set)

  have \<open>enc_weight_opt.\<rho>' (weight T) \<le> Found (\<rho> (mset_set ?K))\<close>
    using Some'
    apply auto
    unfolding \<rho>\<^sub>e_def
    apply (rule \<rho>_mono2)
    subgoal
      using model Some' by (auto simp: finite_postp consistent_interp_postp)
    subgoal by (auto simp: distinct_mset_mset_set)
    subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
    subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
    subgoal
      apply (subst distinct_subseteq_iff[symmetric])
      using dist model[OF Some] H
      by (force simp: filter_filter_mset consistent_interp_def postp_def
              image_mset_mset_set inj_on_Neg inj_on_Pos finite_postp
              distinct_mset_add mset_inter_empty_set_mset distinct_mset_mset_set
            intro: distinct_mset_mono[of _ \<open>the (enc_weight_opt.weight T)\<close>])+
    done
  moreover {
    have \<open>\<rho> (mset_set ?K) \<le> \<rho>\<^sub>e (the (weight T))\<close>
      unfolding \<rho>\<^sub>e_def
      apply (rule \<rho>_mono2)
      subgoal by (rule cons_f)
      subgoal by (rule dist_f)
      subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
      subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
      subgoal
        by (subst distinct_subseteq_iff[symmetric])
        (auto simp: postp_def simp: image_mset_mset_set inj_on_Neg inj_on_Pos
           distinct_mset_add mset_inter_empty_set_mset distinct_mset_mset_set)
      done
    then have \<open>Found (\<rho> (mset_set ?K)) \<le> enc_weight_opt.\<rho>' (weight T)\<close>
      using Some by auto
    } note le =this
  ultimately show \<open>\<rho>\<^sub>e (the (weight T)) = (\<rho> (mset_set ?K))\<close>
    using Some' by auto

  show \<open>\<rho> I \<ge> \<rho> (mset_set ?K)\<close>
    if dist: \<open>distinct_mset I\<close> and
      cons: \<open>consistent_interp (set_mset I)\<close> and
      atm: \<open>atms_of I \<subseteq> atms_of_mm N\<close> and
      I_N: \<open>set_mset I \<Turnstile>sm N\<close>
  proof -
    let ?I = \<open>mset_set (upostp (set_mset I))\<close>
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
          by (auto simp: upostp_def)
        done
    }
    moreover have cons': \<open>consistent_interp (set_mset ?I)\<close>
      using cons unfolding I by (rule consistent_interp_upostp)
    ultimately have \<open>Found (\<rho>\<^sub>e ?I) \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
      using opt[of ?I] by auto
    moreover {
      have \<open>\<rho>\<^sub>e ?I = \<rho> (mset_set (set_mset I))\<close>
        by (rule \<rho>\<^sub>e_upostp_\<rho>)
          (use \<Delta>\<Sigma>_\<Sigma> atms atm cons in \<open>auto dest: multi_member_split\<close>)
      then have \<open>\<rho>\<^sub>e ?I = \<rho> I\<close>
        by (subst (asm) distinct_mset_set_mset_ident)
          (use atms dist in auto)
    }
    ultimately have \<open>Found (\<rho> I) \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
      using Some'
      by auto
    moreover {
      have \<open>\<rho>\<^sub>e (mset_set ?K) \<le> \<rho>\<^sub>e (mset_set (set_mset (the (weight T))))\<close>
        unfolding \<rho>\<^sub>e_def
        apply (rule \<rho>_mono2)
        subgoal using cons_f by auto
        subgoal using dist_f by auto
        subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
        subgoal using atms dist model[OF Some] atms \<Delta>\<Sigma>_\<Sigma> by (auto simp: postp_def)
        subgoal
          by (subst distinct_subseteq_iff[symmetric])
          (auto simp: postp_def simp: image_mset_mset_set inj_on_Neg inj_on_Pos
             distinct_mset_add mset_inter_empty_set_mset distinct_mset_mset_set)
        done
      then have \<open>Found (\<rho>\<^sub>e (mset_set ?K)) \<le> enc_weight_opt.\<rho>' (weight T)\<close>
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
        by (subst distinct_subseteq_iff[symmetric])
          (auto simp: postp_def simp: image_mset_mset_set inj_on_Neg inj_on_Pos
              distinct_mset_add mset_inter_empty_set_mset distinct_mset_mset_set)
      done
    ultimately show ?thesis
      using Some' le by auto
  qed
qed

theorem full_encoding_OCDCL_complexity: (* \htmllink{ocdcl-partial-enc-complexity} *)
  assumes
    st: \<open>full enc_weight_opt.cdcl_bnb_stgy (init_state (penc N)) T\<close> and
    dist: \<open>distinct_mset_mset N\<close> and
    atms: \<open>atms_of_mm N = \<Sigma>\<close>
  shows \<open>size (learned_clss T) \<le> 2 ^ (card (atms_of_mm N - \<Delta>\<Sigma>)) * 4^(card \<Delta>\<Sigma>)\<close>
proof -
  have [simp]: \<open>finite \<Sigma>\<close>
    unfolding atms[symmetric]
    by auto
  have [simp]: \<open>card (atms_of_mm N - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>) =
    card (atms_of_mm N - \<Delta>\<Sigma>) + card ( replacement_pos ` \<Delta>\<Sigma>) + card (replacement_neg ` \<Delta>\<Sigma>)\<close>
    by (subst card_Un_disjoint; auto simp: atms)+
  have [simp]: \<open>card (replacement_pos ` \<Delta>\<Sigma>) = card \<Delta>\<Sigma>\<close>  \<open>card (replacement_neg ` \<Delta>\<Sigma>) = card \<Delta>\<Sigma>\<close>
    by (auto intro!: card_image simp: inj_on_def)

  show ?thesis
    apply (rule order_trans[OF enc_weight_opt.cdcl_bnb_pow2_n_learned_clauses[of \<open>penc N\<close>]])
    using assms \<Delta>\<Sigma>_\<Sigma> monoid_mult_class.power_mult[of \<open>2 :: nat\<close> \<open>2 :: nat\<close> \<open>card \<Delta>\<Sigma>\<close>, unfolded mult_2]
    by (auto simp: full_def distinct_mset_penc monoid_mult_class.power_add
       enc_weight_opt.rtranclp_cdcl_bnb_stgy_cdcl_bnb atms_of_mm_penc_subset2)
qed

inductive ocdcl\<^sub>W_o_r :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
  decide: \<open>odecide S S' \<Longrightarrow> ocdcl\<^sub>W_o_r S S'\<close> |
  bj: \<open>enc_weight_opt.cdcl_bnb_bj S S' \<Longrightarrow> ocdcl\<^sub>W_o_r S S'\<close>

inductive cdcl_bnb_r :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
  cdcl_conflict: \<open>conflict S S' \<Longrightarrow> cdcl_bnb_r S S'\<close> |
  cdcl_propagate: \<open>propagate S S' \<Longrightarrow> cdcl_bnb_r S S'\<close> |
  cdcl_improve: \<open>enc_weight_opt.improvep S S' \<Longrightarrow> cdcl_bnb_r S S'\<close> |
  cdcl_conflict_opt: \<open>enc_weight_opt.conflict_opt S S' \<Longrightarrow> cdcl_bnb_r S S'\<close> |
  cdcl_o': \<open>ocdcl\<^sub>W_o_r S S' \<Longrightarrow> cdcl_bnb_r S S'\<close>

inductive cdcl_bnb_r_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
  cdcl_bnb_r_conflict: \<open>conflict S S' \<Longrightarrow> cdcl_bnb_r_stgy S S'\<close> |
  cdcl_bnb_r_propagate: \<open>propagate S S' \<Longrightarrow> cdcl_bnb_r_stgy S S'\<close> |
  cdcl_bnb_r_improve: \<open>enc_weight_opt.improvep S S' \<Longrightarrow> cdcl_bnb_r_stgy S S'\<close> |
  cdcl_bnb_r_conflict_opt: \<open>enc_weight_opt.conflict_opt S S' \<Longrightarrow> cdcl_bnb_r_stgy S S'\<close> |
  cdcl_bnb_r_other': \<open>ocdcl\<^sub>W_o_r S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> cdcl_bnb_r_stgy S S'\<close>

lemma ocdcl\<^sub>W_o_r_cases[consumes 1, case_names odecode obacktrack skip resolve]:
  assumes
    \<open>ocdcl\<^sub>W_o_r S T\<close>
    \<open>odecide S T \<Longrightarrow> P T\<close>
    \<open>enc_weight_opt.obacktrack S T \<Longrightarrow> P T\<close>
    \<open>skip S T \<Longrightarrow> P T\<close>
    \<open>resolve S T \<Longrightarrow> P T\<close>
  shows \<open>P T\<close>
  using assms by (auto simp: ocdcl\<^sub>W_o_r.simps enc_weight_opt.cdcl_bnb_bj.simps)

context
  fixes S :: 'st
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = (\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_pos ` \<Delta>\<Sigma>
     \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin

lemma odecide_decide:
  \<open>odecide S T \<Longrightarrow> decide S T\<close>
  apply (elim odecideE)
  subgoal for L
    by (rule decide.intros[of S \<open>L\<close>]) auto
  subgoal for L
    by (rule decide.intros[of S \<open>Pos (L\<^sup>\<mapsto>\<^sup>1)\<close>]) (use S_\<Sigma> \<Delta>\<Sigma>_\<Sigma> in auto)
  subgoal for L
    by (rule decide.intros[of S \<open>Pos (L\<^sup>\<mapsto>\<^sup>0)\<close>]) (use S_\<Sigma> \<Delta>\<Sigma>_\<Sigma> in auto)
  done

lemma ocdcl\<^sub>W_o_r_ocdcl\<^sub>W_o:
  \<open>ocdcl\<^sub>W_o_r S T \<Longrightarrow> enc_weight_opt.ocdcl\<^sub>W_o S T\<close>
  using S_\<Sigma> by (auto simp: ocdcl\<^sub>W_o_r.simps enc_weight_opt.ocdcl\<^sub>W_o.simps
      dest: odecide_decide)

lemma cdcl_bnb_r_cdcl_bnb:
  \<open>cdcl_bnb_r S T \<Longrightarrow> enc_weight_opt.cdcl_bnb S T\<close>
  using S_\<Sigma> by (auto simp: cdcl_bnb_r.simps enc_weight_opt.cdcl_bnb.simps
      dest: ocdcl\<^sub>W_o_r_ocdcl\<^sub>W_o)

lemma cdcl_bnb_r_stgy_cdcl_bnb_stgy:
  \<open>cdcl_bnb_r_stgy S T \<Longrightarrow> enc_weight_opt.cdcl_bnb_stgy S T\<close>
  using S_\<Sigma> by (auto simp: cdcl_bnb_r_stgy.simps enc_weight_opt.cdcl_bnb_stgy.simps
      dest: ocdcl\<^sub>W_o_r_ocdcl\<^sub>W_o)

end


context
  fixes S :: 'st
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = (\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_pos ` \<Delta>\<Sigma>
     \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin

lemma rtranclp_cdcl_bnb_r_cdcl_bnb:
  \<open>cdcl_bnb_r\<^sup>*\<^sup>* S T \<Longrightarrow> enc_weight_opt.cdcl_bnb\<^sup>*\<^sup>* S T\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using S_\<Sigma> enc_weight_opt.rtranclp_cdcl_bnb_no_more_init_clss[of S T]
    by(auto dest: cdcl_bnb_r_cdcl_bnb)
  done


lemma rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_stgy:
  \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> enc_weight_opt.cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using S_\<Sigma>
      enc_weight_opt.rtranclp_cdcl_bnb_no_more_init_clss[of S T,
        OF enc_weight_opt.rtranclp_cdcl_bnb_stgy_cdcl_bnb]
    by (auto dest: cdcl_bnb_r_stgy_cdcl_bnb_stgy)
  done


lemma rtranclp_cdcl_bnb_r_all_struct_inv:
  \<open>cdcl_bnb_r\<^sup>*\<^sup>* S T \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state T)\<close>
  using rtranclp_cdcl_bnb_r_cdcl_bnb[of T]
   enc_weight_opt.rtranclp_cdcl_bnb_stgy_all_struct_inv by blast

lemma rtranclp_cdcl_bnb_r_stgy_all_struct_inv:
  \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state T)\<close>
  using rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_stgy[of T]
    enc_weight_opt.rtranclp_cdcl_bnb_stgy_all_struct_inv[of S T]
    enc_weight_opt.rtranclp_cdcl_bnb_stgy_cdcl_bnb[of S T]
  by auto

end

lemma no_step_cdcl_bnb_r_stgy_no_step_cdcl_bnb_stgy:
  assumes
    N: \<open>init_clss S = penc N\<close> and
    \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    tr_alien: \<open>atm_of ` lits_of_l (trail S) \<subseteq> \<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
  shows
    \<open>no_step cdcl_bnb_r_stgy S \<longleftrightarrow> no_step enc_weight_opt.cdcl_bnb_stgy S\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?B
  then show \<open>?A\<close>
    using N cdcl_bnb_r_stgy_cdcl_bnb_stgy[of S] atms_of_mm_encode_clause_subset[of N]
      atms_of_mm_encode_clause_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
      atms_of_mm_penc_subset2[of N]
    by (auto simp: \<Sigma>)
next
  assume ?A
  then have
    nsd: \<open>no_step odecide S\<close> and
    nsp: \<open>no_step propagate S\<close> and
    nsc: \<open>no_step conflict S\<close> and
    nsi: \<open>no_step enc_weight_opt.improvep S\<close> and
    nsco: \<open>no_step enc_weight_opt.conflict_opt S\<close>
    by (auto simp: cdcl_bnb_r_stgy.simps ocdcl\<^sub>W_o_r.simps)
  have
    nsi': \<open>\<And>M'. conflicting S = None \<Longrightarrow> \<not>enc_weight_opt.is_improving (trail S) M' S\<close> and
    nsco': \<open>conflicting S = None \<Longrightarrow> negate_ann_lits (trail S) \<notin># enc_weight_opt.conflicting_clss S\<close>
    using nsi nsco unfolding enc_weight_opt.improvep.simps enc_weight_opt.conflict_opt.simps
    by auto
  have N_\<Sigma>: \<open>atms_of_mm (penc N) =
    (\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
    using N \<Sigma> cdcl_bnb_r_stgy_cdcl_bnb_stgy[of S] atms_of_mm_encode_clause_subset[of N]
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
       replacement_neg ` \<Delta>\<Sigma>\<close>
    proof -
      obtain A where
        \<open>A \<in> \<Delta>\<Sigma>\<close> and
        \<open>atm_of L = replacement_pos A \<or> atm_of L = replacement_neg A\<close> and
        \<open>A \<in> \<Sigma>\<close>
        using L \<Delta>\<Sigma>_\<Sigma> by auto
      then show False
        using nsd L undef T N_\<Sigma>
        using odecide.intros(2-)[of S \<open>A\<close>]
        unfolding N \<Sigma>
        by (cases L) (auto 6 5 simp: defined_lit_Neg_Pos_iff \<Sigma>)
    qed
    have defined_replacement_pos: \<open>defined_lit (trail S) (Pos (replacement_pos L))\<close>
      if \<open>L \<in> \<Delta>\<Sigma>\<close> for L
      using nsd that \<Delta>\<Sigma>_\<Sigma> odecide.intros(2-)[of S \<open>L\<close>] by (auto simp: N \<Sigma> N_\<Sigma>)
    have defined_all: \<open>defined_lit (trail S) L\<close>
      if \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma>\<close> for L
      using nsd that \<Delta>\<Sigma>_\<Sigma> odecide.intros(1)[of S \<open>L\<close>] by (force simp: N \<Sigma> N_\<Sigma>)
    have defined_replacement_neg: \<open>defined_lit (trail S) (Pos (replacement_neg L))\<close>
      if \<open>L \<in> \<Delta>\<Sigma>\<close> for L
      using nsd that \<Delta>\<Sigma>_\<Sigma> odecide.intros(2-)[of S \<open>L\<close>] by (force simp: N \<Sigma> N_\<Sigma>)
    have [simp]: \<open>{A \<in> \<Delta>\<Sigma>. A \<in> \<Sigma>} = \<Delta>\<Sigma>\<close>
      using \<Delta>\<Sigma>_\<Sigma> by auto
    have atms_tr': \<open>\<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma> \<subseteq>
       atm_of ` (lits_of_l (trail S))\<close>
      using N \<Sigma> cdcl_bnb_r_stgy_cdcl_bnb_stgy[of S] atms_of_mm_encode_clause_subset[of N]
        atms_of_mm_encode_clause_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma>
        defined_replacement_pos defined_replacement_neg defined_all
      unfolding N \<Sigma> N_\<Sigma> (*TODO proof*)
      apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
        apply (metis image_eqI literal.sel(1) literal.sel(2) uminus_Pos)
       apply (metis image_eqI literal.sel(1) literal.sel(2))
      apply (metis image_eqI literal.sel(1) literal.sel(2))
      done
    then have atms_tr: \<open>atms_of_mm (encode_clauses N) \<subseteq> atm_of ` (lits_of_l (trail S))\<close>
      using N atms_of_mm_encode_clause_subset[of N]
        atms_of_mm_encode_clause_subset2[of N, OF finite_\<Sigma>] \<Delta>\<Sigma>_\<Sigma>
      unfolding N \<Sigma> N_\<Sigma> \<open>{A \<in> \<Delta>\<Sigma>. A \<in> \<Sigma>} = \<Delta>\<Sigma>\<close>
      by (meson order_trans)
    show False
      by (metis L N N_\<Sigma> atm_lit_of_set_lits_of_l
        atms_tr' defined_lit_map subsetCE undef)
  qed
  then show ?B
    using \<open>?A\<close>
    by (auto simp: cdcl_bnb_r_stgy.simps enc_weight_opt.cdcl_bnb_stgy.simps
        ocdcl\<^sub>W_o_r.simps enc_weight_opt.ocdcl\<^sub>W_o.simps)
qed

lemma cdcl_bnb_r_stgy_init_clss:
  \<open>cdcl_bnb_r_stgy S T \<Longrightarrow> init_clss S = init_clss T\<close>
  by (auto simp: cdcl_bnb_r_stgy.simps ocdcl\<^sub>W_o_r.simps  enc_weight_opt.cdcl_bnb_bj.simps
      elim: conflictE propagateE enc_weight_opt.improveE enc_weight_opt.conflict_optE
      odecideE skipE resolveE enc_weight_opt.obacktrackE)

lemma rtranclp_cdcl_bnb_r_stgy_init_clss:
  \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> init_clss S = init_clss T\<close>
  by  (induction rule: rtranclp_induct)(auto simp:  dest: cdcl_bnb_r_stgy_init_clss)

lemma [simp]:
  \<open>enc_weight_opt.abs_state (init_state N) = abs_state (init_state N)\<close>
  by (auto simp: enc_weight_opt.abs_state_def abs_state_def)

corollary
  assumes
    \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and dist: \<open>distinct_mset_mset N\<close> and
    \<open>full cdcl_bnb_r_stgy (init_state (penc N)) T\<close>
  shows
    \<open>full enc_weight_opt.cdcl_bnb_stgy (init_state (penc N)) T\<close>
proof -
  have [simp]: \<open>atms_of_mm (CDCL_W_Abstract_State.init_clss (enc_weight_opt.abs_state T)) =
    atms_of_mm (init_clss T)\<close>
    by (auto simp: enc_weight_opt.abs_state_def init_clss.simps)
  let ?S = \<open>init_state (penc N)\<close>
  have
    st: \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* ?S T\<close> and
    ns: \<open>no_step cdcl_bnb_r_stgy T\<close>
    using assms unfolding full_def by metis+
  have st': \<open>enc_weight_opt.cdcl_bnb_stgy\<^sup>*\<^sup>* ?S T\<close>
    by (rule rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_stgy[OF _ st])
      (use atms_of_mm_penc_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma> \<Sigma> in auto)
  have [simp]:
    \<open>CDCL_W_Abstract_State.init_clss (abs_state (init_state (penc N))) =
      (penc N)\<close>
    by (auto simp: abs_state_def init_clss.simps)
  have [iff]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state ?S)\<close>
    using dist distinct_mset_penc[of N]
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def \<Sigma>
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state T)\<close>
    using enc_weight_opt.rtranclp_cdcl_bnb_stgy_all_struct_inv[of ?S T]
      enc_weight_opt.rtranclp_cdcl_bnb_stgy_cdcl_bnb[OF st']
    by auto
  then have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (enc_weight_opt.abs_state T)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (enc_weight_opt.abs_state T)\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have [simp]: \<open>init_clss T = penc N\<close>
    using rtranclp_cdcl_bnb_r_stgy_init_clss[OF st] by auto

  have \<open>no_step enc_weight_opt.cdcl_bnb_stgy T\<close>
    by (rule no_step_cdcl_bnb_r_stgy_no_step_cdcl_bnb_stgy[THEN iffD1, of _ N, OF _ _ _ _ ns])
      (use  alien atms_of_mm_penc_subset2[of N] finite_\<Sigma> \<Delta>\<Sigma>_\<Sigma> lev
        in \<open>auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def \<Sigma>
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def\<close>)
  then show \<open>full enc_weight_opt.cdcl_bnb_stgy (init_state (penc N)) T\<close>
    using st' unfolding full_def
    by auto
qed

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
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
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
  new_vars = \<open>\<lambda>n. (200 + 2*n, 200 + 2*n+1)\<close>
  by unfold_locales

lemma mult3_inj:
  \<open>2 * A = Suc (2 * Aa) \<longleftrightarrow> False\<close> for A Aa::nat
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
  new_vars = \<open>\<lambda>n. (200 + 2*n, 200 + 2*n+1)\<close>
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
  new_vars = \<open>\<lambda>n. (200 + 2*n, 200 + 2*n+1)\<close>
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
  new_vars = \<open>\<lambda>n. (200 + 2*n, 200 + 2*n+1)\<close>
  by unfold_locales (auto simp: inj_on_def mult3_inj)


end
