theory Superposition
  imports
    Main
    "Ordered_Resolution_Prover.Abstract_Substitution"
    "Saturation_Framework.Calculus"
    "Saturation_Framework.Lifting_to_Non_Ground_Calculi"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "Abstract_Substitution_Extra"
begin

section \<open>Wellfounded_Extra\<close>

definition lex_prodp where
  "lex_prodp R\<^sub>A R\<^sub>B x y \<longleftrightarrow> R\<^sub>A (fst x) (fst y) \<or> fst x = fst y \<and> R\<^sub>B (snd x) (snd y)"

lemma lex_prodp_lex_prod_iff[pred_set_conv]:
  "lex_prodp R\<^sub>A R\<^sub>B x y \<longleftrightarrow> (x, y) \<in> lex_prod {(x, y). R\<^sub>A x y} {(x, y). R\<^sub>B x y}"
  unfolding lex_prodp_def lex_prod_def by auto

lemma lex_prod_lex_prodp_iff:
  "lex_prod {(x, y). R\<^sub>A x y} {(x, y). R\<^sub>B x y} = {(x, y). lex_prodp R\<^sub>A R\<^sub>B x y}"
  unfolding lex_prodp_def lex_prod_def by auto

lemma transp_lex_prodp: "transp R\<^sub>A \<Longrightarrow> transp R\<^sub>B \<Longrightarrow> transp (lex_prodp R\<^sub>A R\<^sub>B)"
  by (metis (full_types) lex_prodp_def transpD transpI)

lemma wfP_lex_prodp: "wfP R\<^sub>A \<Longrightarrow> wfP R\<^sub>B \<Longrightarrow> wfP (lex_prodp R\<^sub>A R\<^sub>B)"
  by (metis lex_prod_lex_prodp_iff wfP_def wf_lex_prod)


section \<open>Abstract Substitutions\<close>

lemma (in substitution_ops)
  assumes "\<And>L. L \<in># C \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L \<cdot>a \<tau>"
  shows subst_cls_cong: "subst_cls C \<sigma> = subst_cls C \<tau>"
  unfolding subst_cls_def
proof (rule multiset.map_cong0)
  fix L assume "L \<in># C"
  with assms have "atm_of L \<cdot>a \<sigma> = atm_of L \<cdot>a \<tau>"
    by simp
  thus "L \<cdot>l \<sigma> = L \<cdot>l \<tau>"
    by (metis atm_of_subst_lit literal.expand literal.map_disc_iff subst_lit_def)
qed


section \<open>Superposition Calculus\<close>

hide_type Inference_System.inference
hide_const Inference_System.prems_of Inference_System.concl_of Inference_System.main_prem_of

type_synonym 't atom = "'t \<times> 't"

locale superposition_calculus =
  term_subst: basic_substitution subst_trm id_subst comp_subst
  for
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    subst_trm :: "'t \<Rightarrow> 's \<Rightarrow> 't" (infixl "\<cdot>t" 67) and
    subst_trm_set :: "'t set \<Rightarrow> 's \<Rightarrow> 't set" (infixl "\<cdot>ts" 67)  +
  fixes less_trm :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    wfP_less_trm[simp]: "wfP (\<prec>\<^sub>t)"
begin

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

abbreviation less_atm :: "'t atom \<Rightarrow> 't atom \<Rightarrow> bool" (infix "\<prec>\<^sub>a" 50) where
  "less_atm \<equiv> lex_prodp (\<prec>\<^sub>t) (\<prec>\<^sub>t)"

abbreviation lesseq_atm (infix "\<preceq>\<^sub>a" 50) where
  "lesseq_atm \<equiv> (\<prec>\<^sub>a)\<^sup>=\<^sup>="

abbreviation less_lit :: "'t atom literal \<Rightarrow> 't atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit \<equiv> Clausal_Logic.less_lit (\<prec>\<^sub>a)"

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_cls :: "'t atom clause \<Rightarrow> 't atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

abbreviation subst_atm (infixl "\<cdot>a" 67) where
  "subst_atm A \<sigma> \<equiv> map_prod (\<lambda>t. subst_trm t \<sigma>) (\<lambda>t. subst_trm t \<sigma>) A"

interpretation substitution_ops "(\<cdot>a)" id_subst comp_subst .

notation subst_cls (infixl "\<cdot>" 67)

interpretation substitution "(\<cdot>a)" id_subst comp_subst
proof unfold_locales
  show "\<And>A. A \<cdot>a id_subst = A"
    by (simp add: prod.map_ident)
next
  show "\<And>A \<sigma> \<tau>. A \<cdot>a (\<sigma> \<odot> \<tau>) = A \<cdot>a \<sigma> \<cdot>a \<tau>"
    by (simp add: prod.map_comp comp_def)
next
  show "\<And>\<sigma> \<tau>. (\<And>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    by (rule term_subst.subst_ext) force
next
  fix C :: "'t atom clause" and \<sigma> :: 's
  define T :: "'t set" where
    "T = (\<Union>L \<in> set_mset C. {fst (atm_of L), snd (atm_of L)})"

  assume ground_C_\<sigma>: "is_ground_cls (subst_cls C \<sigma>)"
  have "term_subst.is_ground_set (term_subst.subst_set T \<sigma>)"
    unfolding term_subst.is_ground_set_def
  proof (rule ballI)
    fix t' assume "t' \<in> term_subst.subst_set T \<sigma>"
    then obtain t where "t \<in> T" and "t' = t \<cdot>t \<sigma>"
      unfolding term_subst.subst_set_def by auto
    then obtain L where "L \<in># C" and t_in: "t \<in> {fst (atm_of L), snd (atm_of L)}"
      unfolding T_def by auto

    from \<open>L \<in># C\<close> have "is_ground_lit (subst_lit L \<sigma>)"
      using ground_C_\<sigma> is_ground_cls_def multi_member_split by fastforce
    hence "is_ground_atm (subst_atm (atm_of L) \<sigma>)"
      by (simp add: is_ground_lit_def)
    then show "term_subst.is_ground t'"
      unfolding \<open>t' = t \<cdot>t \<sigma>\<close>
      using t_in
      apply (cases "atm_of L")
      apply simp_all
      apply (simp add: is_ground_atm_def term_subst.is_ground_def)
      using term_subst.is_ground_def is_ground_atm_def by force
  qed
  then obtain \<gamma> where
    gr_\<gamma>: "term_subst.is_ground_subst \<gamma>" and
    subst_\<gamma>_eq_subst_\<sigma>: "\<forall>x\<in>T. x \<cdot>t \<gamma> = x \<cdot>t \<sigma>"
    using term_subst.make_ground_subst[of T \<sigma>] by auto

  show "\<exists>\<gamma>. is_ground_subst \<gamma> \<and> subst_cls C \<gamma> = subst_cls C \<sigma>"
  proof (intro exI conjI)
    show "is_ground_subst \<gamma>"
      using gr_\<gamma>
      unfolding substitution_ops.is_ground_subst_def
      by (smt (verit, best) prod.map_ident_strong prod.set_map imageE is_ground_atm_def
          term_subst.is_ground_def term_subst.is_ground_subst_def)
  next
    show "subst_cls C \<gamma> = subst_cls C \<sigma>"
    proof (rule subst_cls_cong)
      fix L assume "L \<in># C"
      then show "subst_atm (atm_of L) \<gamma> = subst_atm (atm_of L) \<sigma>"
        using subst_\<gamma>_eq_subst_\<sigma>
        by (cases "atm_of L") (auto simp: T_def)
    qed
  qed
qed
      

section \<open>Rules\<close>


inductive superposition :: "'t atom clause \<Rightarrow> 't atom clause \<Rightarrow> 't atom clause \<Rightarrow> bool" where
  superpositionI: "
    \<not> (P\<^sub>2 \<preceq>\<^sub>c P\<^sub>1) \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    (\<forall>L \<in># add_mset L\<^sub>1 P\<^sub>1'. \<not> (L\<^sub>1 \<preceq>\<^sub>l L)) \<Longrightarrow>
    (\<forall>L \<in># add_mset L\<^sub>2 P\<^sub>2'. \<not> (L\<^sub>1 \<preceq>\<^sub>l L)) \<Longrightarrow>
    L\<^sub>2 = Pos (t\<^sub>2, t\<^sub>2') \<or> L\<^sub>2 = Pos (t\<^sub>2', t\<^sub>2) \<Longrightarrow>
    \<not> (t\<^sub>2 \<preceq>\<^sub>t t\<^sub>2') \<Longrightarrow>
    superposition P\<^sub>1 P\<^sub>2 C"

inductive eq_resolution :: "'t atom clause \<Rightarrow> 't atom clause \<Rightarrow> bool" where
  eq_resolutionI: "
    P = add_mset L P' \<Longrightarrow>
    L = Neg (t\<^sub>1, t\<^sub>2) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}} \<Longrightarrow>
    C = P' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution P C"

inductive eq_factoring :: "'t atom clause \<Rightarrow> 't atom clause \<Rightarrow> bool" where
  eq_factoringI: "
    P = add_mset L\<^sub>1 (add_mset L\<^sub>2 P') \<Longrightarrow>
    (\<forall>L \<in># add_mset L\<^sub>2 P'. \<not> (L\<^sub>1 \<prec>\<^sub>l L)) \<Longrightarrow>
    L\<^sub>1 = Pos (s\<^sub>1, t\<^sub>1) \<or> L\<^sub>1 = Pos (t\<^sub>1, s\<^sub>1) \<Longrightarrow>
    L\<^sub>2 = Pos (s\<^sub>2, t\<^sub>2) \<or> L\<^sub>2 = Pos (t\<^sub>2, s\<^sub>2) \<Longrightarrow>
    \<not> (s\<^sub>1 \<preceq>\<^sub>t t\<^sub>1) \<Longrightarrow>
    \<not> (s\<^sub>2 \<preceq>\<^sub>t t\<^sub>2) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, s\<^sub>2}} \<Longrightarrow>
    C = add_mset (Pos (s\<^sub>1, s\<^sub>2)) (add_mset (Neg (t\<^sub>1, t\<^sub>2)) P') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring P C"


section \<open>Ground Layer\<close>

abbreviation G_Inf :: "'t atom clause inference set" where
  "G_Inf \<equiv> {}"

abbreviation G_Bot :: "'t atom clause set" where
  "G_Bot \<equiv> {{#}}"

abbreviation G_entails :: "'t atom clause set \<Rightarrow> 't atom clause set \<Rightarrow> bool" where
  "G_entails \<equiv> (\<TTurnstile>e)"

interpretation G: sound_inference_system G_Inf G_Bot G_entails
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> G_entails (set (prems_of \<iota>)) {concl_of \<iota>}"
    sorry
qed

interpretation G: calculus_with_finitary_standard_redundancy G_Inf G_Bot G_entails "(\<prec>\<^sub>c)"
proof unfold_locales
  have "transp (\<prec>\<^sub>a)"
    using transp_less_trm transp_lex_prodp by blast
  hence "transp (\<prec>\<^sub>l)"
    using transp_less_lit by blast
  thus "transp (\<prec>\<^sub>c)"
    using transp_multp by blast
next
  have "wfP (\<prec>\<^sub>a)"
    using wfP_less_trm wfP_lex_prodp by blast
  hence "wfP (\<prec>\<^sub>l)"
    using wfP_less_lit by blast
  thus "wfP (\<prec>\<^sub>c)"
    using wfP_multp by blast
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
    sorry
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    sorry
qed

interpretation G: statically_complete_calculus G_Bot G_Inf G_entails G.Red_I G.Red_F
proof unfold_locales
  show "\<And>B N. B \<in> G_Bot \<Longrightarrow> G.saturated N \<Longrightarrow> G_entails N {B} \<Longrightarrow> \<exists>B'\<in>G_Bot. B' \<in> N"
    sorry
qed


section \<open>First-Order Layer\<close>


abbreviation F_Inf :: "'t atom clause inference set" where
  "F_Inf \<equiv> {}"

abbreviation F_Bot :: "'t atom clause set" where
  "F_Bot \<equiv> {{#}}"

abbreviation F_entails :: "'t atom clause set \<Rightarrow> 't atom clause set \<Rightarrow> bool" where
  "F_entails \<equiv> (\<TTurnstile>e)"

typedecl Q

definition \<G>_F :: "Q \<Rightarrow> 't atom clause \<Rightarrow> 't atom clause set" where
  "\<G>_F \<equiv> \<lambda>_ _. {}"

definition \<G>_I :: "Q \<Rightarrow> 't atom clause inference \<Rightarrow> 't atom clause inference set option" where
  "\<G>_I \<equiv> \<lambda>_ _. None"

definition Prec_F :: "'t atom clause \<Rightarrow> 't atom clause \<Rightarrow> 't atom clause \<Rightarrow> bool" where
  "Prec_F \<equiv> \<lambda>_ _ _. False"

interpretation F: lifting_intersection F_Inf G_Bot "UNIV :: Q set" "\<lambda>(_ :: Q). G_Inf"
  "\<lambda>(_ :: Q). G_entails" "\<lambda>(_ :: Q). G.Red_I" "\<lambda>(_ :: Q). G.Red_F" F_Bot \<G>_F \<G>_I Prec_F
proof unfold_locales
  show "UNIV \<noteq> {}"
    by simp
next
  show "\<forall>q\<in>UNIV. consequence_relation F_Bot F_entails"
    sorry
next
  show "\<forall>q\<in>UNIV. tiebreaker_lifting F_Bot F_Inf F_Bot F_entails F_Inf G.Red_I G.Red_F (\<G>_F q)
    (\<G>_I q) Prec_F"
    sorry
qed

interpretation F: sound_inference_system F_Inf F_Bot F.entails_\<G>
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> F.entails_\<G> (set (prems_of \<iota>)) {concl_of \<iota>}"
    sorry
qed

interpretation F: statically_complete_calculus F_Bot F_Inf F.entails_\<G> F.Red_I_\<G> F.Red_F_\<G>
proof unfold_locales
  show "\<And>B N. B \<in> F_Bot \<Longrightarrow> F.saturated N \<Longrightarrow> F.entails_\<G> N {B} \<Longrightarrow> \<exists>B' \<in> F_Bot. B' \<in> N"
    sorry
qed

end

end