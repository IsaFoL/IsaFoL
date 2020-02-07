theory CDCL_W_Optimal_Model
  imports CDCL_W_BnB "HOL-Library.Extended_Nat"
begin

subsubsection \<open>OCDCL\<close>

text \<open>
  The following datatype is equivalent to \<^typ>\<open>'a option\<close>. Howover, it has the opposite
  ordering. Therefore, I decided to use a different type instead of have a second order
  which conflicts with \<^file>\<open>~~/src/HOL/Library/Option_ord.thy\<close>.
\<close>
datatype 'a optimal_model = Not_Found | is_found: Found (the_optimal: 'a)

instantiation optimal_model :: (ord) ord
begin
  fun less_optimal_model  :: \<open>'a :: ord optimal_model \<Rightarrow> 'a optimal_model \<Rightarrow> bool\<close> where
  \<open>less_optimal_model Not_Found _ = False\<close>
| \<open>less_optimal_model (Found _) Not_Found \<longleftrightarrow> True\<close>
| \<open>less_optimal_model (Found a) (Found b) \<longleftrightarrow> a < b\<close>

fun less_eq_optimal_model  :: \<open>'a :: ord optimal_model \<Rightarrow> 'a optimal_model \<Rightarrow> bool\<close> where
  \<open>less_eq_optimal_model Not_Found Not_Found = True\<close>
| \<open>less_eq_optimal_model Not_Found (Found _) = False\<close>
| \<open>less_eq_optimal_model (Found _) Not_Found \<longleftrightarrow> True\<close>
| \<open>less_eq_optimal_model (Found a) (Found b) \<longleftrightarrow> a \<le> b\<close>

instance
  by standard

end

instance optimal_model :: (preorder) preorder
  apply standard
  subgoal for a b
    by (cases a; cases b) (auto simp: less_le_not_le)
  subgoal for a
    by (cases a) auto
  subgoal for a b c
    by (cases a; cases b; cases c) (auto dest: order_trans)
  done

instance optimal_model :: (order) order
  apply standard
  subgoal for a b
    by (cases a; cases b) (auto simp: less_le_not_le)
  done

instance optimal_model :: (linorder) linorder
  apply standard
  subgoal for a b
    by (cases a; cases b) (auto simp: less_le_not_le)
  done

instantiation optimal_model :: (wellorder) wellorder
begin

lemma wf_less_optimal_model: \<open>wf {(M :: 'a optimal_model, N). M < N}\<close>
proof -
  have 1: \<open>{(M :: 'a optimal_model, N). M < N} =
    map_prod Found Found ` {(M :: 'a, N). M < N} \<union>
    {(a, b). a \<noteq> Not_Found \<and> b = Not_Found}\<close> (is \<open>?A = ?B \<union> ?C\<close>)
    apply (auto simp: image_iff)
    apply (case_tac a; case_tac b)
    apply auto
    apply (case_tac a)
    apply auto
    done
  have [simp]: \<open>inj Found\<close>
    by (auto simp:inj_on_def)
  have \<open>wf ?B\<close>
    by (rule wf_map_prod_image) (auto intro: wf)
  moreover have \<open>wf ?C\<close>
    by (rule wfI_pf) auto
  ultimately show \<open>wf (?A)\<close>
    unfolding 1
    by (rule wf_Un) (auto)
qed

instance by standard (metis CollectI split_conv wf_def wf_less_optimal_model)

end


text \<open>This locales includes only the assumption we make on the weight function.\<close>
locale ocdcl_weight =
  fixes
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close>
  assumes
    \<rho>_mono: \<open>distinct_mset B \<Longrightarrow> A \<subseteq># B \<Longrightarrow> \<rho> A \<le> \<rho> B\<close>
begin

lemma \<rho>_empty_simp[simp]:
  assumes \<open>consistent_interp (set_mset A)\<close> \<open>distinct_mset A\<close>
  shows \<open>\<rho> A \<ge> \<rho> {#}\<close> \<open>\<not>\<rho> A < \<rho> {#}\<close>  \<open>\<rho> A \<le> \<rho> {#} \<longleftrightarrow> \<rho> A = \<rho> {#}\<close>
  using \<rho>_mono[of A \<open>{#}\<close>] assms
  by auto

abbreviation \<rho>' :: \<open>'v clause option \<Rightarrow> 'a optimal_model\<close> where
  \<open>\<rho>' w \<equiv> (case w of None \<Rightarrow> Not_Found | Some w \<Rightarrow> Found (\<rho> w))\<close>

definition is_improving_int
  :: "('v literal, 'v literal, 'b) annotated_lits \<Rightarrow> ('v literal, 'v literal, 'b) annotated_lits \<Rightarrow> 'v clauses \<Rightarrow>
    'v clause option \<Rightarrow> bool"
where
  \<open>is_improving_int M M' N w \<longleftrightarrow> Found (\<rho> (lit_of `# mset M')) < \<rho>' w \<and>
    M' \<Turnstile>asm N \<and> no_dup M' \<and>
    lit_of `# mset M' \<in> simple_clss (atms_of_mm N) \<and>
    total_over_m (lits_of_l M') (set_mset N) \<and>
    (\<forall>M'. total_over_m (lits_of_l M') (set_mset N) \<longrightarrow> mset M \<subseteq># mset M' \<longrightarrow>
      lit_of `# mset M' \<in> simple_clss (atms_of_mm N) \<longrightarrow>
      \<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset M))\<close>

definition too_heavy_clauses
  :: \<open>'v clauses \<Rightarrow> 'v clause option \<Rightarrow> 'v clauses\<close>
where
  \<open>too_heavy_clauses M w =
     {#pNeg C | C \<in># mset_set (simple_clss (atms_of_mm M)). \<rho>' w \<le> Found (\<rho> C)#}\<close>

definition conflicting_clauses
  :: \<open>'v clauses \<Rightarrow> 'v clause option \<Rightarrow> 'v clauses\<close>
where
  \<open>conflicting_clauses N w =
    {#C \<in># mset_set (simple_clss (atms_of_mm N)). too_heavy_clauses N w \<Turnstile>pm C#}\<close>

lemma too_heavy_clauses_conflicting_clauses:
  \<open>C \<in># too_heavy_clauses M w \<Longrightarrow> C \<in># conflicting_clauses M w\<close>
  by (auto simp: conflicting_clauses_def too_heavy_clauses_def simple_clss_finite)

lemma too_heavy_clauses_contains_itself:
  \<open>M \<in> simple_clss (atms_of_mm N) \<Longrightarrow> pNeg M \<in># too_heavy_clauses N (Some M)\<close>
  by (auto simp: too_heavy_clauses_def simple_clss_finite)

lemma too_heavy_clause_None[simp]: \<open>too_heavy_clauses M None = {#}\<close>
  by (auto simp: too_heavy_clauses_def)

lemma atms_of_mm_too_heavy_clauses_le:
  \<open>atms_of_mm (too_heavy_clauses M I) \<subseteq> atms_of_mm M\<close>
  by (auto simp: too_heavy_clauses_def atms_of_ms_def simple_clss_finite dest: simple_clssE)

lemma
  atms_too_heavy_clauses_None:
    \<open>atms_of_mm (too_heavy_clauses M None) = {}\<close> and
  atms_too_heavy_clauses_Some:
    \<open>atms_of w \<subseteq> atms_of_mm M  \<Longrightarrow> distinct_mset w \<Longrightarrow> \<not>tautology w \<Longrightarrow>
      atms_of_mm (too_heavy_clauses M (Some w)) = atms_of_mm M\<close>
proof -
  show \<open>atms_of_mm (too_heavy_clauses M None) = {}\<close>
    by (auto simp: too_heavy_clauses_def)
  assume atms: \<open>atms_of w \<subseteq> atms_of_mm M\<close> and
    dist: \<open>distinct_mset w\<close> and
    taut: \<open>\<not>tautology w\<close>
  have \<open>atms_of_mm (too_heavy_clauses M (Some w)) \<subseteq> atms_of_mm M\<close>
    by (auto simp: too_heavy_clauses_def atms_of_ms_def simple_clss_finite)
      (auto simp: simple_clss_def)
  let ?w = \<open>w + Neg `# {#x \<in># mset_set (atms_of_mm M). x \<notin> atms_of w#}\<close>
  have [simp]: \<open>inj_on Neg A\<close> for A
    by (auto simp: inj_on_def)
  have dist: \<open>distinct_mset ?w\<close>
    using dist
    by (auto simp: distinct_mset_add distinct_image_mset_inj distinct_mset_mset_set uminus_lit_swap
      disjunct_not_in dest: multi_member_split)
  moreover have not_tauto: \<open>\<not>tautology ?w\<close>
    by (auto simp: tautology_union taut uminus_lit_swap dest: multi_member_split)
  ultimately have \<open>?w \<in> (simple_clss (atms_of_mm M))\<close>
    using atms by (auto simp: simple_clss_def)
  moreover have \<open>\<rho> ?w \<ge> \<rho> w\<close>
    by (rule \<rho>_mono) (use dist not_tauto in \<open>auto simp: consistent_interp_tuatology_mset_set tautology_decomp\<close>)
  ultimately have \<open>pNeg ?w \<in># too_heavy_clauses M (Some w)\<close>
    by (auto simp: too_heavy_clauses_def simple_clss_finite)
  then have \<open>atms_of_mm M \<subseteq> atms_of_mm (too_heavy_clauses M (Some w))\<close>
    by (auto dest!: multi_member_split)
  then show \<open>atms_of_mm (too_heavy_clauses M (Some w)) = atms_of_mm M\<close>
    using \<open>atms_of_mm (too_heavy_clauses M (Some w)) \<subseteq> atms_of_mm M\<close> by blast
qed

lemma entails_too_heavy_clauses_too_heavy_clauses: (* \htmllink{ocdcl-entails-conflicting} *)
  assumes
    \<open>consistent_interp I\<close> and
    tot: \<open>total_over_m I (set_mset (too_heavy_clauses M w))\<close> and
    \<open>I \<Turnstile>m too_heavy_clauses M w\<close> and
    w: \<open>w \<noteq> None \<Longrightarrow> atms_of (the w) \<subseteq> atms_of_mm M\<close>
      \<open>w \<noteq> None \<Longrightarrow> \<not>tautology (the w)\<close>
      \<open>w \<noteq> None \<Longrightarrow> distinct_mset (the w)\<close>
  shows \<open>I \<Turnstile>m conflicting_clauses M w\<close>
proof (cases w)
  case None
  have [simp]: \<open>{x \<in> simple_clss (atms_of_mm M). tautology x} = {}\<close>
    by (auto dest: simple_clssE)
  show ?thesis
    using None by (auto simp: conflicting_clauses_def true_clss_cls_tautology_iff
      simple_clss_finite)
next
  case w': (Some w')
  have \<open>x \<in># mset_set (simple_clss (atms_of_mm M)) \<Longrightarrow> total_over_set I (atms_of x)\<close> for x
    using tot w atms_too_heavy_clauses_Some[of w' M] unfolding w'
    by (auto simp: total_over_m_def simple_clss_finite total_over_set_alt_def
      dest!: simple_clssE)
  then show ?thesis
    using assms
    by (subst true_cls_mset_def)
      (auto simp: conflicting_clauses_def true_clss_cls_def
        dest!: spec[of _ I])
qed

lemma not_entailed_too_heavy_clauses_ge:
  \<open>C \<in> simple_clss (atms_of_mm N) \<Longrightarrow> \<not> too_heavy_clauses N w \<Turnstile>pm pNeg C \<Longrightarrow> \<not>Found (\<rho> C) \<ge> \<rho>' w\<close>
  using true_clss_cls_in[of \<open>pNeg C\<close> \<open>set_mset (too_heavy_clauses N w)\<close>]
    too_heavy_clauses_contains_itself
  by (auto simp: too_heavy_clauses_def simple_clss_finite
        image_iff)

lemma conflicting_clss_incl_init_clauses:
  \<open>atms_of_mm (conflicting_clauses N w) \<subseteq> atms_of_mm (N)\<close>
  unfolding conflicting_clauses_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def atms_of_ms_def split: if_splits)

lemma distinct_mset_mset_conflicting_clss2: \<open>distinct_mset_mset (conflicting_clauses N w)\<close>
  unfolding conflicting_clauses_def distinct_mset_set_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def)

lemma too_heavy_clauses_mono:
  \<open>\<rho> a > \<rho> (lit_of `# mset M) \<Longrightarrow> too_heavy_clauses N (Some a) \<subseteq>#
       too_heavy_clauses N (Some (lit_of `# mset M))\<close>
  by (auto simp: too_heavy_clauses_def multiset_filter_mono2
    intro!: multiset_filter_mono image_mset_subseteq_mono)

lemma is_improving_conflicting_clss_update_weight_information: \<open>is_improving_int M M' N w \<Longrightarrow>
       conflicting_clauses N w \<subseteq># conflicting_clauses N (Some (lit_of `# mset M'))\<close>
  using too_heavy_clauses_mono[of M' \<open>the w\<close> \<open>N\<close>]
  by (cases \<open>w\<close>)
    (auto simp: is_improving_int_def  conflicting_clauses_def multiset_filter_mono2
      intro!: image_mset_subseteq_mono
      intro: true_clss_cls_subset
      dest: simple_clssE)

lemma conflicting_clss_update_weight_information_in2:
  assumes \<open>is_improving_int M M' N w\<close>
  shows \<open>negate_ann_lits M' \<in># conflicting_clauses N (Some (lit_of `# mset M'))\<close>
  using assms apply (auto simp: simple_clss_finite
    conflicting_clauses_def is_improving_int_def)
  by (auto simp: is_improving_int_def conflicting_clauses_def  multiset_filter_mono2 simple_clss_def
       lits_of_def negate_ann_lits_pNeg_lit_of image_iff dest: total_over_m_atms_incl
      intro!: true_clss_cls_in too_heavy_clauses_contains_itself)

lemma atms_of_init_clss_conflicting_clauses'[simp]:
  \<open>atms_of_mm N \<union> atms_of_mm (conflicting_clauses N S) = atms_of_mm N\<close>
  using conflicting_clss_incl_init_clauses[of N] by blast

lemma entails_too_heavy_clauses_if_le:
  assumes
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm N\<close> and
    le: \<open>Found (\<rho> I) < \<rho>' (Some M')\<close>
  shows
    \<open>set_mset I \<Turnstile>m too_heavy_clauses N (Some M')\<close>
proof -
  show \<open>set_mset I \<Turnstile>m too_heavy_clauses N (Some M')\<close>
    unfolding true_cls_mset_def
  proof
    fix C
    assume \<open>C \<in># too_heavy_clauses N (Some M')\<close>
    then obtain x where
      [simp]: \<open>C = pNeg x\<close> and
      x: \<open>x \<in> simple_clss (atms_of_mm N)\<close> and
      we: \<open>\<rho> M' \<le> \<rho> x\<close>
      unfolding too_heavy_clauses_def
      by (auto simp: simple_clss_finite)
    then have \<open>x \<noteq> I\<close>
      using le by auto
    then have \<open>set_mset x \<noteq> set_mset I\<close>
      using distinct_set_mset_eq_iff[of x I] x dist
      by (auto simp: simple_clss_def)
    then have \<open>\<exists>a. ((a \<in># x \<and> a \<notin># I) \<or> (a \<in># I \<and> a \<notin># x))\<close>
      by auto
    moreover have not_incl: \<open>\<not>set_mset x \<subseteq> set_mset I\<close>
      using \<rho>_mono[of I \<open>x\<close>] we le distinct_set_mset_eq_iff[of x I] simple_clssE[OF x]
        dist cons
      by auto
    moreover have \<open>x \<noteq> {#}\<close>
      using we le cons dist not_incl by auto
    ultimately obtain L where
      L_x: \<open>L \<in># x\<close> and
      \<open>L \<notin># I\<close>
      by auto
    moreover have \<open>atms_of x \<subseteq> atms_of I\<close>
      using simple_clssE[OF x] tot atm_iff_pos_or_neg_lit[of a I] atm_iff_pos_or_neg_lit[of a x]
      by (auto dest!: multi_member_split)
    ultimately have \<open>-L \<in># I\<close>
      using tot simple_clssE[OF x] atm_of_notin_atms_of_iff by auto
    then show \<open>set_mset I \<Turnstile> C\<close>
      using L_x by (auto simp: simple_clss_finite pNeg_def dest!: multi_member_split)
  qed
qed

lemma entails_conflicting_clauses_if_le:
  fixes M''
  defines \<open>M' \<equiv> lit_of `# mset M''\<close>
  assumes
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm N\<close> and
    le: \<open>Found (\<rho> I) < \<rho>' (Some M')\<close> and
    \<open>is_improving_int M M'' N w\<close>
  shows
    \<open>set_mset I \<Turnstile>m conflicting_clauses N (Some (lit_of `# mset M''))\<close>
  apply (rule entails_too_heavy_clauses_too_heavy_clauses[OF cons])
  subgoal
    using assms unfolding is_improving_int_def
    by (auto simp: total_over_m_alt_def M'_def atms_of_def lit_in_set_iff_atm
          atms_too_heavy_clauses_Some eq_commute[of _ \<open>atms_of_mm N\<close>]
        dest: multi_member_split dest!: simple_clssE)
  by (use assms  entails_too_heavy_clauses_if_le[OF assms(2-5)] in
    \<open>auto simp: M'_def lits_of_def image_image is_improving_int_def dest!: simple_clssE\<close>)

end


locale conflict_driven_clause_learning\<^sub>W_optimal_weight =
  conflict_driven_clause_learning\<^sub>W
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting
      \<comment> \<open>get state:\<close>
    init_state +
  ocdcl_weight \<rho>
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
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close>  +
  fixes
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close>
  assumes
    update_additional_info:
      \<open>state S = (M, N, U, C, K) \<Longrightarrow> state (update_additional_info K' S) = (M, N, U, C, K')\<close> and
    weight_init_state:
      \<open>\<And>N :: 'v clauses. fst (additional_info (init_state N)) = None\<close>
begin

definition update_weight_information :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st\<close> where
  \<open>update_weight_information M S =
    update_additional_info (Some (lit_of `# mset M), snd (additional_info S)) S\<close>

lemma
  trail_update_additional_info[simp]: \<open>trail (update_additional_info w S) = trail S\<close> and
  init_clss_update_additional_info[simp]:
    \<open>init_clss (update_additional_info w S) = init_clss S\<close> and
  learned_clss_update_additional_info[simp]:
    \<open>learned_clss (update_additional_info w S) = learned_clss S\<close> and
  backtrack_lvl_update_additional_info[simp]:
    \<open>backtrack_lvl (update_additional_info w S) = backtrack_lvl S\<close> and
  conflicting_update_additional_info[simp]:
    \<open>conflicting (update_additional_info w S) = conflicting S\<close> and
  clauses_update_additional_info[simp]:
    \<open>clauses (update_additional_info w S) = clauses S\<close>
  using update_additional_info[of S] unfolding clauses_def
  by (subst (asm) state_prop; subst (asm) state_prop; auto; fail)+

lemma
  trail_update_weight_information[simp]:
    \<open>trail (update_weight_information w S) = trail S\<close> and
  init_clss_update_weight_information[simp]:
    \<open>init_clss (update_weight_information w S) = init_clss S\<close> and
  learned_clss_update_weight_information[simp]:
    \<open>learned_clss (update_weight_information w S) = learned_clss S\<close> and
  backtrack_lvl_update_weight_information[simp]:
    \<open>backtrack_lvl (update_weight_information w S) = backtrack_lvl S\<close> and
  conflicting_update_weight_information[simp]:
    \<open>conflicting (update_weight_information w S) = conflicting S\<close> and
  clauses_update_weight_information[simp]:
    \<open>clauses (update_weight_information w S) = clauses S\<close>
  using update_additional_info[of S] unfolding update_weight_information_def by auto

definition weight :: \<open>'st \<Rightarrow> 'v clause option\<close> where
  \<open>weight S = fst (additional_info S)\<close>

lemma
  additional_info_update_additional_info[simp]:
  \<open>additional_info (update_additional_info w S) = w\<close>
  unfolding additional_info_def using update_additional_info[of S]
  by (cases \<open>state S\<close>; auto; fail)+

lemma
  weight_cons_trail2[simp]: \<open>weight (cons_trail L S) = weight S\<close> and
  clss_tl_trail2[simp]: \<open>weight (tl_trail S) = weight S\<close> and
  weight_add_learned_cls_unfolded:
    \<open>weight (add_learned_cls U S) = weight S\<close>
    and
  weight_update_conflicting2[simp]: \<open>weight (update_conflicting D S) = weight S\<close> and
  weight_remove_cls2[simp]:
    \<open>weight (remove_cls C S) = weight S\<close> and
  weight_add_learned_cls2[simp]:
    \<open>weight (add_learned_cls C S) = weight S\<close> and
  weight_update_weight_information2[simp]:
    \<open>weight (update_weight_information M S) = Some (lit_of `# mset M)\<close>
  by (auto simp: update_weight_information_def weight_def)


sublocale conflict_driven_clause_learning_with_adding_init_clause_bnb\<^sub>W_no_state
  where
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
    weight = weight and
    update_weight_information = update_weight_information and
    is_improving_int = is_improving_int and
    conflicting_clauses = conflicting_clauses
  by unfold_locales

lemma state_additional_info':
  \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close>
  unfolding additional_info'_def by (cases \<open>state S\<close>; auto simp: state_prop weight_def)

lemma state_update_weight_information:
  \<open>state S = (M, N, U, C, w, other) \<Longrightarrow>
    \<exists>w'. state (update_weight_information T S) = (M, N, U, C, w', other)\<close>
  unfolding update_weight_information_def by (cases \<open>state S\<close>; auto simp: state_prop weight_def)

lemma atms_of_init_clss_conflicting_clauses[simp]:
  \<open>atms_of_mm (init_clss S) \<union> atms_of_mm (conflicting_clss S) = atms_of_mm (init_clss S)\<close>
  using conflicting_clss_incl_init_clauses[of \<open>(init_clss S)\<close>] unfolding conflicting_clss_def by blast

lemma lit_of_trail_in_simple_clss: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
         lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def abs_state_def
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
  by (auto simp: simple_clss_def cdcl\<^sub>W_restart_mset_state atms_of_def pNeg_def lits_of_def
      dest: no_dup_not_tautology no_dup_distinct)

lemma pNeg_lit_of_trail_in_simple_clss: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
         pNeg (lit_of `# mset (trail S)) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def abs_state_def
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
  by (auto simp: simple_clss_def cdcl\<^sub>W_restart_mset_state atms_of_def pNeg_def lits_of_def
      dest: no_dup_not_tautology_uminus no_dup_distinct_uminus)

lemma conflict_clss_update_weight_no_alien:
  \<open>atms_of_mm (conflicting_clss (update_weight_information M S))
    \<subseteq> atms_of_mm (init_clss S)\<close>
  by (auto simp: conflicting_clss_def conflicting_clauses_def atms_of_ms_def
      cdcl\<^sub>W_restart_mset_state simple_clss_finite
    dest: simple_clssE)

sublocale state\<^sub>W_no_state
  where
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
    init_state = init_state
  by unfold_locales

sublocale state\<^sub>W_no_state
  where
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
    init_state = init_state
  by unfold_locales

sublocale conflict_driven_clause_learning\<^sub>W
  where
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
    init_state = init_state
  by unfold_locales

lemma is_improving_conflicting_clss_update_weight_information': \<open>is_improving M M' S \<Longrightarrow>
       conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M' S)\<close>
  using is_improving_conflicting_clss_update_weight_information[of M M' \<open>init_clss S\<close> \<open>weight S\<close>]
  unfolding conflicting_clss_def
  by auto

lemma conflicting_clss_update_weight_information_in2':
  assumes \<open>is_improving M M' S\<close>
  shows \<open>negate_ann_lits M' \<in># conflicting_clss (update_weight_information M' S)\<close>
  using conflicting_clss_update_weight_information_in2[of M M' \<open>init_clss S\<close> \<open>weight S\<close>] assms
  unfolding conflicting_clss_def
  by auto

sublocale conflict_driven_clause_learning_with_adding_init_clause_bnb\<^sub>W_ops
  where
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
    weight = weight and
    update_weight_information = update_weight_information and
    is_improving_int = is_improving_int and
    conflicting_clauses = conflicting_clauses
  apply unfold_locales
  subgoal by (rule state_additional_info')
  subgoal by (rule state_update_weight_information)
  subgoal unfolding conflicting_clss_def by (rule conflicting_clss_incl_init_clauses)
  subgoal unfolding conflicting_clss_def by (rule distinct_mset_mset_conflicting_clss2)
  subgoal by (rule is_improving_conflicting_clss_update_weight_information')
  subgoal by (rule conflicting_clss_update_weight_information_in2'; assumption)
  done

lemma wf_cdcl_bnb_fixed:
   \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bnb S T
      \<and> init_clss S = N}\<close>
  apply (rule wf_cdcl_bnb[of N id \<open>{(I', I). I' \<noteq> None \<and>
     (the I') \<in> simple_clss (atms_of_mm N) \<and> (\<rho>' I', \<rho>' I) \<in> {(j, i). j < i}}\<close>])
  subgoal for S T
    by (cases \<open>weight S\<close>; cases \<open>weight T\<close>)
      (auto simp: improvep.simps is_improving_int_def split: enat.splits)
  subgoal
    apply (rule wf_finite_segments)
    subgoal by (auto simp: irrefl_def)
    subgoal
      apply (auto simp: irrefl_def trans_def intro: less_trans[of \<open>Found _\<close> \<open>Found _\<close>])
      apply (rule less_trans[of \<open>Found _\<close> \<open>Found _\<close>])
      apply auto
      done
    subgoal for x
      by (subgoal_tac \<open>{y. (y, x)
         \<in> {(I', I). I' \<noteq> None \<and> the I' \<in> simple_clss (atms_of_mm N) \<and>
            (\<rho>' I', \<rho>' I) \<in> {(j, i). j < i}}} =
        Some ` {y. (y, x) \<in> {(I', I).
             I' \<in> simple_clss (atms_of_mm N) \<and>
            (\<rho>' (Some I'), \<rho>' I) \<in> {(j, i). j < i}}}\<close>)
       (auto simp: finite_image_iff intro: finite_subset[OF _ simple_clss_finite[of \<open>atms_of_mm N\<close>]])
    done
  done

lemma wf_cdcl_bnb2:
  \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)
     \<and> cdcl_bnb S T}\<close>
  by (subst wf_cdcl_bnb_fixed_iff[symmetric]) (intro allI, rule wf_cdcl_bnb_fixed)

lemma can_always_improve:
  assumes
    ent: \<open>trail S \<Turnstile>asm clauses S\<close> and
    total: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close> and
    n_s: \<open>no_step conflict_opt S\<close> and
    confl[simp]: \<open>conflicting S = None\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
   shows \<open>Ex (improvep S)\<close>
proof -
  have H: \<open>(lit_of `# mset (trail S)) \<in># mset_set (simple_clss (atms_of_mm (init_clss S)))\<close>
    \<open>(lit_of `# mset (trail S)) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    \<open>no_dup (trail S)\<close>
    apply (subst finite_set_mset_mset_set[OF simple_clss_finite])
    using all_struct by (auto simp: simple_clss_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        no_strange_atm_def atms_of_def lits_of_def image_image
        cdcl\<^sub>W_M_level_inv_def clauses_def
      dest: no_dup_not_tautology no_dup_distinct)
  then have le: \<open>Found (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using n_s total
    by (auto simp: conflict_opt.simps conflicting_clss_def lits_of_def
         conflicting_clauses_def clauses_def negate_ann_lits_pNeg_lit_of simple_clss_finite
       dest: not_entailed_too_heavy_clauses_ge)
  have tr: \<open>trail S \<Turnstile>asm init_clss S\<close>
    using ent by (auto simp: clauses_def)
  have tot': \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
    using total all_struct by (auto simp: total_over_m_def total_over_set_def
       cdcl\<^sub>W_all_struct_inv_def clauses_def no_strange_atm_def)
  have M': \<open>\<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset (trail S))\<close>
      if \<open>total_over_m (lits_of_l M') (set_mset (init_clss S))\<close> and
        incl: \<open>mset (trail S) \<subseteq># mset M'\<close> and
        \<open>lit_of `# mset M' \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      for M'
    proof -
      have [simp]: \<open>lits_of_l M' = set_mset (lit_of `# mset M')\<close>
        by (auto simp: lits_of_def)
      obtain A where A: \<open>mset M' = A + mset (trail S)\<close>
        using incl by (auto simp: mset_subset_eq_exists_conv)
      have M': \<open>lits_of_l M' = lit_of ` set_mset A \<union> lits_of_l (trail S)\<close>
        unfolding lits_of_def
        by (metis A image_Un set_mset_mset set_mset_union)
      have \<open>mset M' = mset (trail S)\<close>
        using that tot' total unfolding A total_over_m_alt_def
        apply (case_tac A)
        apply (auto simp: A simple_clss_def distinct_mset_add M' image_Un
            tautology_union mset_inter_empty_set_mset atms_of_def atms_of_s_def
            atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_image
            tautology_add_mset)
        by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
           subsetCE lits_of_def)
      then show ?thesis
        using total by auto
    qed
  have \<open>is_improving (trail S) (trail S) S\<close>
    if \<open>Found (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using that total H confl tr tot' M' unfolding is_improving_int_def lits_of_def by fast
  then show \<open>Ex (improvep S)\<close>
    using improvep.intros[of S \<open>trail S\<close> \<open>update_weight_information (trail S) S\<close>] le confl by fast
qed

lemma no_step_cdcl_bnb_stgy_empty_conflict2:
  assumes
    n_s: \<open>no_step cdcl_bnb S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close>
  shows \<open>conflicting S = Some {#}\<close>
  by (rule no_step_cdcl_bnb_stgy_empty_conflict[OF can_always_improve assms])


lemma cdcl_bnb_larger_still_larger:
  assumes
    \<open>cdcl_bnb S T\<close>
  shows \<open>\<rho>' (weight S) \<ge> \<rho>' (weight T)\<close>
  using assms apply (cases rule: cdcl_bnb.cases)
  by (auto simp: improvep.simps is_improving_int_def conflict_opt.simps ocdcl\<^sub>W_o.simps
      cdcl_bnb_bj.simps skip.simps resolve.simps obacktrack.simps elim: rulesE)

lemma obacktrack_model_still_model:
  assumes
    \<open>obacktrack S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close> \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close> and
    le: \<open>Found (\<rho> I) < \<rho>' (weight T)\<close>
  shows
    \<open>set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T\<close>
  using assms(1)
proof (cases rule: obacktrack.cases)
  case (obacktrack_rule L D K M1 M2 D' i) note confl = this(1) and DD' = this(7) and
    clss_L_D' = this(8) and T = this(9)
  have H: \<open>total_over_m I (set_mset (clauses S + conflicting_clss S) \<union> {add_mset L D'}) \<Longrightarrow>
      consistent_interp I \<Longrightarrow>
      I \<Turnstile>sm clauses S + conflicting_clss S \<Longrightarrow> I \<Turnstile> add_mset L D'\<close> for I
    using clss_L_D'
    unfolding true_clss_cls_def
    by blast
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have \<open>total_over_m (set_mset I) (set_mset (init_clss S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)

  then have 1: \<open>total_over_m (set_mset I) (set_mset (clauses S + conflicting_clss S) \<union>
       {add_mset L D'})\<close>
    using alien T confl tot DD' opt_struct
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def total_over_m_def total_over_set_def
    apply (auto simp: cdcl\<^sub>W_restart_mset_state abs_state_def atms_of_def clauses_def
      cdcl_bnb_struct_invs_def dest: multi_member_split)
    by blast
  have 2: \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close>
    using tot cons ent(2) by auto
  have \<open>set_mset I \<Turnstile> add_mset L D'\<close>
    using H[OF 1 cons] 2 ent by auto
  then show ?thesis
    using ent obacktrack_rule 2 by auto
qed


lemma entails_conflicting_clauses_if_le':
  fixes M''
  defines \<open>M' \<equiv> lit_of `# mset M''\<close>
  assumes
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    le: \<open>Found (\<rho> I) < \<rho>' (Some M')\<close> and
    \<open>is_improving M M'' S\<close> and
    \<open>N = init_clss S\<close>
  shows
    \<open>set_mset I \<Turnstile>m conflicting_clauses N (weight (update_weight_information M'' S))\<close>
  using entails_conflicting_clauses_if_le[OF assms(2-6)[unfolded M'_def]] assms(7)
  unfolding conflicting_clss_def by auto

lemma improve_model_still_model:
  assumes
    \<open>improvep S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close>  \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close> and
    le: \<open>Found (\<rho> I) < \<rho>' (weight T)\<close>
  shows
    \<open>set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T\<close>
  using assms(1)
proof (cases rule: improvep.cases)
  case (improve_rule M') note imp = this(1) and confl = this(2) and T = this(3)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have atm_trail: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien by (auto simp: no_strange_atm_def lits_of_def atms_of_def)
  have dist2: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    taut2: \<open>\<not> tautology (lit_of `# mset (trail S))\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto dest: no_dup_distinct no_dup_not_tautology)
  have tot2: \<open>total_over_m (set_mset I) (set_mset (init_clss S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)
  have atm_trail: \<open>atms_of (lit_of `# mset M') \<subseteq> atms_of_mm (init_clss S)\<close> and
    dist2: \<open>distinct_mset (lit_of `# mset M')\<close> and
    taut2: \<open>\<not> tautology (lit_of `# mset M')\<close>
    using imp by (auto simp: no_strange_atm_def lits_of_def atms_of_def is_improving_int_def
      simple_clss_def)

  have tot2: \<open>total_over_m (set_mset I) (set_mset (init_clss S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)
  have
      \<open>set_mset I \<Turnstile>m conflicting_clauses (init_clss S) (weight (update_weight_information M' S))\<close>
    apply (rule entails_conflicting_clauses_if_le'[unfolded conflicting_clss_def])
    using T dist cons tot le imp by (auto intro!: )
  then have \<open>set_mset I \<Turnstile>m conflicting_clss (update_weight_information M' S)\<close>
    by (auto simp: update_weight_information_def conflicting_clss_def)
  then show ?thesis
    using ent improve_rule T by auto
qed

lemma cdcl_bnb_still_model:
  assumes
    \<open>cdcl_bnb S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close> \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close>
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T) \<or> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using assms
proof (cases rule: cdcl_bnb.cases)
  case cdcl_improve
  from improve_model_still_model[OF this all_struct ent dist cons tot opt_struct]
  show ?thesis
    by (auto simp: improvep.simps)
next
  case cdcl_other'
  then show ?thesis
  proof (induction rule: ocdcl\<^sub>W_o_all_rules_induct)
    case (backtrack T)
    from obacktrack_model_still_model[OF this all_struct ent dist cons tot opt_struct]
    show ?case
      by auto
  qed (use ent in \<open>auto elim: rulesE\<close>)
qed (auto simp: conflict_opt.simps elim: rulesE)

lemma rtranclp_cdcl_bnb_still_model:
  assumes
    st: \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm conflicting_clss S) \<or> Found (\<rho> I) \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close>
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T) \<or> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using st
proof (induction rule: rtranclp_induct)
  case base
  then show ?case
    using ent by auto
next
  case (step T U) note star = this(1) and st = this(2) and IH = this(3)
  have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bnb_stgy_all_struct_inv[OF star all_struct] .

  have 2: \<open>cdcl_bnb_struct_invs T\<close>
    using rtranclp_cdcl_bnb_cdcl_bnb_struct_invs[OF star opt_struct] .
  have 3: \<open>atms_of I = atms_of_mm (init_clss T)\<close>
    using tot rtranclp_cdcl_bnb_no_more_init_clss[OF star] by auto
  show ?case
    using cdcl_bnb_still_model[OF st 1 _ _ dist cons 3 2] IH
      cdcl_bnb_larger_still_larger[OF st]
    by auto
qed

lemma full_cdcl_bnb_stgy_larger_or_equal_weight:
  assumes
    st: \<open>full cdcl_bnb_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm conflicting_clss S) \<or> Found (\<rho> I) \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close>
  shows
    \<open>Found (\<rho> I) \<ge> \<rho>' (weight T)\<close> and
    \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
proof -
  have ns: \<open>no_step cdcl_bnb_stgy T\<close> and
    st: \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close> and
    st': \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close>
    using st unfolding full_def by (auto intro: rtranclp_cdcl_bnb_stgy_cdcl_bnb)
  have ns': \<open>no_step cdcl_bnb T\<close>
    by (meson cdcl_bnb.cases cdcl_bnb_stgy.simps no_confl_prop_impr.elims(3) ns)
  have struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bnb_stgy_all_struct_inv[OF st' all_struct] .
  have stgy_T: \<open>cdcl_bnb_stgy_inv T\<close>
    using rtranclp_cdcl_bnb_stgy_stgy_inv[OF st all_struct stgy_inv] .
  have confl: \<open>conflicting T = Some {#}\<close>
    using no_step_cdcl_bnb_stgy_empty_conflict2[OF ns' struct_T stgy_T] .

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state T)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state T)\<close>
    using struct_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have ent': \<open>set_mset (clauses T + conflicting_clss T) \<Turnstile>p {#}\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
    by auto
  have atms_eq: \<open>atms_of I \<union> atms_of_mm (conflicting_clss T) = atms_of_mm (init_clss T)\<close>
    using tot[symmetric] atms_of_conflicting_clss[of T] alien
    unfolding rtranclp_cdcl_bnb_no_more_init_clss[OF st'] cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: clauses_def total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit
      abs_state_def cdcl\<^sub>W_restart_mset_state)

  have \<open>\<not> (set_mset I \<Turnstile>sm clauses T + conflicting_clss T)\<close>
  proof
    assume ent'': \<open>set_mset I \<Turnstile>sm clauses T + conflicting_clss T\<close>
    moreover have \<open>total_over_m (set_mset I) (set_mset (clauses T + conflicting_clss T))\<close>
      using tot[symmetric] atms_of_conflicting_clss[of T] alien
      unfolding rtranclp_cdcl_bnb_no_more_init_clss[OF st'] cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: clauses_def total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit
              abs_state_def cdcl\<^sub>W_restart_mset_state atms_eq)
    then show False
      using ent' cons ent'' unfolding true_clss_cls_def by auto
  qed
  then show \<open>\<rho>' (weight T) \<le> Found (\<rho> I)\<close>
    using rtranclp_cdcl_bnb_still_model[OF st' all_struct ent dist cons tot opt_struct]
    by auto

  show \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
  proof
    assume \<open>satisfiable (set_mset (clauses T + conflicting_clss T))\<close>
    then obtain I where
      ent'': \<open>I \<Turnstile>sm clauses T + conflicting_clss T\<close> and
      tot: \<open>total_over_m I (set_mset (clauses T + conflicting_clss T))\<close> and
      \<open>consistent_interp I\<close>
      unfolding satisfiable_def
      by blast
    then show \<open>False\<close>
      using ent' cons unfolding true_clss_cls_def by auto
  qed
qed


lemma full_cdcl_bnb_stgy_unsat2:
  assumes
    st: \<open>full cdcl_bnb_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close>
  shows
    \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
proof -
  have ns: \<open>no_step cdcl_bnb_stgy T\<close> and
    st: \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close> and
    st': \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close>
    using st unfolding full_def by (auto intro: rtranclp_cdcl_bnb_stgy_cdcl_bnb)
  have ns': \<open>no_step cdcl_bnb T\<close>
    by (meson cdcl_bnb.cases cdcl_bnb_stgy.simps no_confl_prop_impr.elims(3) ns)
  have struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bnb_stgy_all_struct_inv[OF st' all_struct] .
  have stgy_T: \<open>cdcl_bnb_stgy_inv T\<close>
    using rtranclp_cdcl_bnb_stgy_stgy_inv[OF st all_struct stgy_inv] .
  have confl: \<open>conflicting T = Some {#}\<close>
    using no_step_cdcl_bnb_stgy_empty_conflict2[OF ns' struct_T stgy_T] .

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state T)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state T)\<close>
    using struct_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have ent': \<open>set_mset (clauses T + conflicting_clss T) \<Turnstile>p {#}\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
    by auto

  show \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
  proof
    assume \<open>satisfiable (set_mset (clauses T + conflicting_clss T))\<close>
    then obtain I where
      ent'': \<open>I \<Turnstile>sm clauses T + conflicting_clss T\<close> and
      tot: \<open>total_over_m I (set_mset (clauses T + conflicting_clss T))\<close> and
      \<open>consistent_interp I\<close>
      unfolding satisfiable_def
      by blast
    then show \<open>False\<close>
      using ent' unfolding true_clss_cls_def by auto
  qed
qed

lemma weight_init_state2[simp]: \<open>weight (init_state S) = None\<close> and
  conflicting_clss_init_state[simp]:
    \<open>conflicting_clss (init_state N) = {#}\<close>
  unfolding weight_def conflicting_clss_def conflicting_clauses_def
  by (auto simp: weight_init_state true_clss_cls_tautology_iff simple_clss_finite
    filter_mset_empty_conv mset_set_empty_iff dest: simple_clssE)

text \<open>First part of \cwref{theo:prop:cdclmmcorrect}{Theorem 2.15.6}\<close>
lemma full_cdcl_bnb_stgy_no_conflicting_clause_unsat:
  assumes
    st: \<open>full cdcl_bnb_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close> and
    [simp]: \<open>weight T = None\<close> and
    ent: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>unsatisfiable (set_mset (init_clss S))\<close>
proof -
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    \<open>conflicting_clss T = {#}\<close>
    using ent by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      cdcl\<^sub>W_learned_clauses_entailed_by_init_def abs_state_def cdcl\<^sub>W_restart_mset_state
      conflicting_clss_def conflicting_clauses_def true_clss_cls_tautology_iff simple_clss_finite
      filter_mset_empty_conv mset_set_empty_iff dest: simple_clssE)
  then show ?thesis
    using full_cdcl_bnb_stgy_no_conflicting_clss_unsat[OF _ st all_struct
     stgy_inv] by (auto simp: can_always_improve)
qed

definition annotation_is_model where
  \<open>annotation_is_model S \<longleftrightarrow>
     (weight S \<noteq> None \<longrightarrow> (set_mset (the (weight S)) \<Turnstile>sm init_clss S \<and>
       consistent_interp (set_mset (the (weight S))) \<and>
       atms_of (the (weight S)) \<subseteq> atms_of_mm (init_clss S) \<and>
       total_over_m (set_mset (the (weight S))) (set_mset (init_clss S)) \<and>
       distinct_mset (the (weight S))))\<close>

lemma cdcl_bnb_annotation_is_model:
  assumes
    \<open>cdcl_bnb S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>annotation_is_model S\<close>
  shows \<open>annotation_is_model T\<close>
proof -
  have [simp]: \<open>atms_of (lit_of `# mset M) = atm_of ` lit_of ` set M\<close> for M
    by (auto simp: atms_of_def)
  have \<open>consistent_interp (lits_of_l (trail S)) \<and>
       atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (init_clss S) \<and>
       distinct_mset (lit_of `# mset (trail S))\<close>
    using assms(2) by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      abs_state_def cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      dest: no_dup_distinct)
  with assms(1,3)
  show ?thesis
    apply (cases rule: cdcl_bnb.cases)
    subgoal
      by (auto simp: conflict.simps annotation_is_model_def)
    subgoal
      by (auto simp: propagate.simps annotation_is_model_def)
    subgoal
      by (force simp: annotation_is_model_def true_annots_true_cls lits_of_def
             improvep.simps is_improving_int_def image_Un image_image simple_clss_def
             consistent_interp_tuatology_mset_set
           dest!: consistent_interp_unionD intro: distinct_mset_union2)
    subgoal
      by (auto simp: annotation_is_model_def conflict_opt.simps)
    subgoal
      by (auto simp: annotation_is_model_def
              ocdcl\<^sub>W_o.simps cdcl_bnb_bj.simps obacktrack.simps
              skip.simps resolve.simps decide.simps)
    done
qed

lemma rtranclp_cdcl_bnb_annotation_is_model:
  \<open>cdcl_bnb\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
     annotation_is_model S \<Longrightarrow> annotation_is_model T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: cdcl_bnb_annotation_is_model rtranclp_cdcl_bnb_stgy_all_struct_inv)


text \<open>\cwref{theo:prop:cdclmmcorrect}{Theorem 2.15.6}\<close>
theorem full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state:
  assumes
    st: \<open>full cdcl_bnb_stgy (init_state N) T\<close> and
    dist: \<open>distinct_mset_mset N\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> (is \<open>?B \<Longrightarrow> ?A\<close>) and
    \<open>weight T \<noteq> None \<Longrightarrow> consistent_interp (set_mset (the (weight T))) \<and>
       atms_of (the (weight T)) \<subseteq> atms_of_mm N \<and> set_mset (the (weight T)) \<Turnstile>sm N \<and>
       total_over_m (set_mset (the (weight T))) (set_mset N) \<and>
       distinct_mset (the (weight T))\<close> and
    \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
proof -
  let ?S = \<open>init_state N\<close>
  have \<open>distinct_mset C\<close> if \<open>C \<in># N\<close> for C
    using dist that by (auto simp: distinct_mset_set_def dest: multi_member_split)
  then have dist: \<open>distinct_mset_mset N\<close>
    by (auto simp: distinct_mset_set_def)
  then have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ([], N, {#}, None)\<close>
    unfolding init_state.simps[symmetric]
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
  moreover have [iff]: \<open>cdcl_bnb_struct_invs ?S\<close> and [simp]: \<open>cdcl_bnb_stgy_inv ?S\<close>
    by (auto simp: cdcl_bnb_struct_invs_def conflict_is_false_with_level_def cdcl_bnb_stgy_inv_def)
  moreover have ent: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init ?S\<close>
    by (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  moreover have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state (init_state N))\<close>
    unfolding CDCL_W_Abstract_State.init_state.simps abs_state_def
    by auto
  ultimately show \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close>
    using full_cdcl_bnb_stgy_no_conflicting_clause_unsat[OF st]
    by auto
  have \<open>annotation_is_model ?S\<close>
    by (auto simp: annotation_is_model_def)
  then have \<open>annotation_is_model T\<close>
    using rtranclp_cdcl_bnb_annotation_is_model[of ?S T] st
    unfolding full_def by (auto dest: rtranclp_cdcl_bnb_stgy_cdcl_bnb)
  moreover have \<open>init_clss T = N\<close>
    using rtranclp_cdcl_bnb_no_more_init_clss[of ?S T] st
    unfolding full_def by (auto dest: rtranclp_cdcl_bnb_stgy_cdcl_bnb)
  ultimately show \<open>weight T \<noteq> None \<Longrightarrow> consistent_interp (set_mset (the (weight T))) \<and>
       atms_of (the (weight T)) \<subseteq> atms_of_mm N \<and> set_mset (the (weight T)) \<Turnstile>sm N \<and>
       total_over_m (set_mset (the (weight T))) (set_mset N) \<and>
       distinct_mset (the (weight T))\<close>
    by (auto simp: annotation_is_model_def)

  show \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
    using full_cdcl_bnb_stgy_larger_or_equal_weight[of ?S T I] st unfolding full_def
    by auto
qed

lemma pruned_clause_in_conflicting_clss:
  assumes
    ge: \<open>\<And>M'. total_over_m (set_mset (mset (M @ M'))) (set_mset (init_clss S)) \<Longrightarrow>
      distinct_mset (atm_of `# mset (M @ M')) \<Longrightarrow>
      consistent_interp (set_mset (mset (M @ M'))) \<Longrightarrow>
      Found (\<rho> (mset (M @ M'))) \<ge> \<rho>' (weight S)\<close> and
    atm: \<open>atms_of (mset M) \<subseteq> atms_of_mm (init_clss S)\<close> and
    dist: \<open>distinct M\<close> and
    cons: \<open>consistent_interp (set M)\<close>
  shows \<open>pNeg (mset M) \<in># conflicting_clss S\<close>
proof -
  have 0: \<open>(pNeg o mset o ((@) M))` {M'.
      distinct_mset (atm_of `# mset (M @ M')) \<and> consistent_interp (set_mset (mset (M @ M'))) \<and>
      atms_of_s (set (M @ M')) \<subseteq> (atms_of_mm (init_clss S)) \<and>
      card (atms_of_mm (init_clss S)) = n + card (atms_of (mset (M @ M')))} \<subseteq>
    set_mset (conflicting_clss S)\<close> (is \<open>_ ` ?A n \<subseteq> ?H\<close>)for n
  proof (induction n)
    case 0
    show ?case
    proof clarify
      fix x :: \<open>'v literal multiset\<close> and xa :: \<open>'v literal multiset\<close> and
        xb :: \<open>'v literal list\<close> and xc :: \<open>'v literal list\<close>
      assume
        dist: \<open>distinct_mset (atm_of `# mset (M @ xc))\<close> and
        cons: \<open>consistent_interp (set_mset (mset (M @ xc)))\<close> and
        atm': \<open>atms_of_s (set (M @ xc)) \<subseteq> atms_of_mm (init_clss S)\<close> and
        0: \<open>card (atms_of_mm (init_clss S)) = 0 + card (atms_of (mset (M @ xc)))\<close>
      have D[dest]:
        \<open>A \<in> set M \<Longrightarrow> A \<notin> set xc\<close> \<open>A \<in> set M \<Longrightarrow> -A \<notin> set xc\<close>
        for A
        using dist multi_member_split[of A \<open>mset M\<close>] multi_member_split[of \<open>-A\<close> \<open>mset xc\<close>]
          multi_member_split[of \<open>-A\<close> \<open>mset M\<close>] multi_member_split[of \<open>A\<close> \<open>mset xc\<close>]
        by (auto simp: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
      have dist2: \<open>distinct xc\<close> \<open>distinct_mset (atm_of `# mset xc)\<close>
        \<open>distinct_mset (mset M + mset xc)\<close>
        using dist distinct_mset_atm_ofD[OF dist]
        unfolding mset_append[symmetric] distinct_mset_mset_distinct
        by (auto dest: distinct_mset_union2 distinct_mset_atm_ofD)
      have eq: \<open>card (atms_of_s (set M) \<union> atms_of_s (set xc)) =
        card (atms_of_s (set M)) + card (atms_of_s (set xc))\<close>
              by (subst card_Un_Int) auto
      let ?M = \<open>M @ xc\<close>

      have H1: \<open>atms_of_s (set ?M) = atms_of_mm (init_clss S)\<close>
        using eq atm card_mono[OF _ atm'] card_subset_eq[OF _ atm'] 0
        by (auto simp: atms_of_s_def image_Un)
      moreover have tot2: \<open>total_over_m (set ?M) (set_mset (init_clss S))\<close>
        using H1 by (auto simp: total_over_m_def total_over_set_def lit_in_set_iff_atm)
      moreover have \<open>\<not>tautology (mset ?M)\<close>
        using cons unfolding consistent_interp_tautology[symmetric]
        by auto
      ultimately have \<open>mset ?M \<in> simple_clss (atms_of_mm (init_clss S))\<close>
        using dist atm cons H1 dist2
        by (auto simp: simple_clss_def consistent_interp_tautology atms_of_s_def)
      moreover have tot2: \<open>total_over_m (set ?M) (set_mset (init_clss S))\<close>
        using H1 by (auto simp: total_over_m_def total_over_set_def lit_in_set_iff_atm)
      ultimately show \<open>(pNeg \<circ> mset \<circ> (@) M) xc \<in># conflicting_clss S\<close>
        using ge[of \<open>xc\<close>] dist 0 cons card_mono[OF _ atm] tot2 cons
        by (auto simp: conflicting_clss_def too_heavy_clauses_def simple_clss_finite
            intro!: too_heavy_clauses_conflicting_clauses imageI)
    qed
  next
    case (Suc n) note IH = this(1)
    let ?H = \<open>?A n\<close>
    show ?case
    proof clarify
      fix x :: \<open>'v literal multiset\<close> and xa :: \<open>'v literal multiset\<close> and
        xb :: \<open>'v literal list\<close> and xc :: \<open>'v literal list\<close>
      assume
        dist: \<open>distinct_mset (atm_of `# mset (M @ xc))\<close> and
        cons: \<open>consistent_interp (set_mset (mset (M @ xc)))\<close> and
        atm': \<open>atms_of_s (set (M @ xc)) \<subseteq> atms_of_mm (init_clss S)\<close> and
        0: \<open>card (atms_of_mm (init_clss S)) = Suc n + card (atms_of (mset (M @ xc)))\<close>
      then obtain a where
        a: \<open>a \<in> atms_of_mm (init_clss S)\<close> and
        a_notin: \<open>a \<notin> atms_of_s (set (M @ xc))\<close>
        by (metis Suc_n_not_le_n add_Suc_shift atms_of_mmltiset atms_of_s_def le_add2
            subsetI subset_antisym)
      have dist2: \<open>distinct xc\<close> \<open>distinct_mset (atm_of `# mset xc)\<close>
        \<open>distinct_mset (mset M + mset xc)\<close>
        using dist distinct_mset_atm_ofD[OF dist]
        unfolding mset_append[symmetric] distinct_mset_mset_distinct
        by (auto dest: distinct_mset_union2 distinct_mset_atm_ofD)
      let ?xc1 = \<open>Pos a # xc\<close>
      let ?xc2 = \<open>Neg a # xc\<close>
      have \<open>?xc1 \<in> ?H\<close>
        using dist cons atm' 0 dist2 a_notin a
        by (auto simp: distinct_mset_add mset_inter_empty_set_mset
            lit_in_set_iff_atm card_insert_if)
      from set_mp[OF IH imageI[OF this]]
      have 1: \<open>too_heavy_clauses (init_clss S) (weight S) \<Turnstile>pm add_mset (-(Pos a)) (pNeg (mset (M @ xc)))\<close>
        unfolding conflicting_clss_def unfolding conflicting_clauses_def
        by (auto simp: pNeg_simps)
      have \<open>?xc2 \<in> ?H\<close>
        using dist cons atm' 0 dist2 a_notin a
        by (auto simp: distinct_mset_add mset_inter_empty_set_mset
            lit_in_set_iff_atm card_insert_if)
      from set_mp[OF IH imageI[OF this]]
      have 2: \<open>too_heavy_clauses (init_clss S) (weight S) \<Turnstile>pm add_mset (Pos a) (pNeg (mset (M @ xc)))\<close>
        unfolding conflicting_clss_def unfolding conflicting_clauses_def
        by (auto simp: pNeg_simps)

      have \<open>\<not>tautology (mset (M @ xc))\<close>
        using cons unfolding consistent_interp_tautology[symmetric]
        by auto
      then have \<open>\<not>tautology (pNeg (mset M) + pNeg (mset xc))\<close>
        unfolding mset_append[symmetric] pNeg_simps[symmetric]
        by (auto simp del: mset_append)
      then have \<open>pNeg (mset M) + pNeg (mset xc) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
        using atm' dist2 by (auto simp: simple_clss_def atms_of_s_def simp flip: pNeg_simps)
      then show \<open>(pNeg \<circ> mset \<circ> (@) M) xc \<in># conflicting_clss S\<close>
        using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[OF 1 2] apply -
        unfolding conflicting_clss_def conflicting_clauses_def
        by (subst (asm) true_clss_cls_remdups_mset[symmetric])
          (auto simp: simple_clss_finite pNeg_simps intro: true_clss_cls_cong_set_mset
            simp del: true_clss_cls_remdups_mset)
    qed
  qed
  have \<open>[] \<in> {M'.
     distinct_mset (atm_of `# mset (M @ M')) \<and>
     consistent_interp (set_mset (mset (M @ M'))) \<and>
     atms_of_s (set (M @ M')) \<subseteq> atms_of_mm (init_clss S) \<and>
     card (atms_of_mm (init_clss S)) =
     card (atms_of_mm (init_clss S)) - card (atms_of (mset M)) +
     card (atms_of (mset (M @ M')))}\<close>
    using card_mono[OF _ assms(2)] assms by (auto dest: card_mono distinct_consistent_distinct_atm)

  from set_mp[OF 0 imageI[OF this]]
  show \<open>pNeg (mset M) \<in># conflicting_clss S\<close>
    by auto
qed

end

end
