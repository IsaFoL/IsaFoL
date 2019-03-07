(*
    Author: Andreas Halkjær From, DTU Compute, 2019
    Contributors: Alexander Birch Jensen, Anders Schlichtkrull & Jørgen Villadsen
*)

section \<open>Tableau Calculus\<close>

theory WoLLIC_Tableau imports WoLLIC_FOL begin

inductive TC :: \<open>('a, 'b) form list \<Rightarrow> bool\<close> ("\<stileturn> _" 0) where
  Basic: \<open>\<stileturn> Pre i l # Neg (Pre i l) # G\<close>
| BasicFF: \<open>\<stileturn> \<bottom> # G\<close>
| BasicNegTT: \<open>\<stileturn> Neg TT # G\<close>
| AlphaNegNeg: \<open>\<stileturn> A # G \<Longrightarrow> \<stileturn> Neg (Neg A) # G\<close>
| AlphaAnd: \<open>\<stileturn> A # B # G \<Longrightarrow> \<stileturn> Con A B # G\<close>
| AlphaNegOr: \<open>\<stileturn> Neg A # Neg B # G \<Longrightarrow> \<stileturn> Neg (Dis A B) # G\<close>
| AlphaNegImpl: \<open>\<stileturn> A # Neg B # G \<Longrightarrow> \<stileturn> Neg (Imp A B) # G\<close>
| BetaNegAnd: \<open>\<stileturn> Neg A # G \<Longrightarrow> \<stileturn> Neg B # G \<Longrightarrow> \<stileturn> Neg (Con A B) # G\<close>
| BetaOr: \<open>\<stileturn> A # G \<Longrightarrow> \<stileturn> B # G \<Longrightarrow> \<stileturn> Dis A B # G\<close>
| BetaImpl: \<open>\<stileturn> Neg A # G \<Longrightarrow> \<stileturn> B # G \<Longrightarrow> \<stileturn> Imp A B # G\<close>
| GammaForall: \<open>\<stileturn> subst A t 0 # G \<Longrightarrow> \<stileturn> Uni A # G\<close>
| GammaNegExists: \<open>\<stileturn> Neg (subst A t 0) # G \<Longrightarrow> \<stileturn> Neg (Exi A) # G\<close>
| DeltaExists: \<open>\<stileturn> subst A (Fun n []) 0 # G \<Longrightarrow> news n (A # G) \<Longrightarrow> \<stileturn> Exi A # G\<close>
| DeltaNegForall: \<open>\<stileturn> Neg (subst A (Fun n []) 0) # G \<Longrightarrow> news n (A # G) \<Longrightarrow> \<stileturn> Neg (Uni A) # G\<close>
| Order: \<open>\<stileturn> G \<Longrightarrow> set G \<subseteq> set G' \<Longrightarrow> \<stileturn> G'\<close>

lemma Shift: \<open>\<stileturn> rotate1 G \<Longrightarrow> \<stileturn> G\<close>
  by (simp add: Order)

lemma Swap: \<open>\<stileturn> B # A # G \<Longrightarrow> \<stileturn> A # B # G\<close>
  by (simp add: Order insert_commute)

definition tableauproof :: \<open>('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> bool\<close> where
  \<open>tableauproof ps p \<equiv> (\<stileturn> Neg p # ps)\<close>

theorem tableauNotAA: \<open>\<stileturn> [Neg (Pre ''A'' []) , Pre ''A'' []]\<close>
  by (rule Shift, simp) (rule Basic)

theorem AndAnd:
  \<open>\<stileturn> [Con (Pre ''A'' []) (Pre ''B'' []), Neg (Con (Pre ''B'' []) (Pre ''A'' []))]\<close>
  apply (rule AlphaAnd)
  apply (rule Shift, rule Shift, simp)
  apply (rule BetaNegAnd)
   apply (rule Shift, rule Shift, simp)
   apply (rule Basic)
  apply (rule Swap)
  apply (rule Basic)
  done

subsection \<open>Soundness\<close>

lemma TC_soundness:
  \<open>\<stileturn> G \<Longrightarrow> \<exists>p \<in> set G. \<not> semantics e f g p\<close>
proof (induct G arbitrary: f rule: TC.induct)
  case (DeltaExists A n G)
  show ?case
  proof (rule ccontr)
    assume \<open>\<not> (\<exists>p \<in> set (Exi A # G). \<not> semantics e f g p)\<close>
    then have *: \<open>\<forall>p \<in> set (Exi A # G). semantics e f g p\<close>
      by simp

    then obtain x where \<open>semantics (shift e 0 x) (f(n := \<lambda>w. x)) g A\<close>
      using \<open>news n (A # G)\<close> by auto
    then have **: \<open>semantics e (f(n := \<lambda>w. x)) g (subst A (Fun n []) 0)\<close>
      by simp

    have \<open>\<exists>p \<in> set (subst A (Fun n []) 0 # G). \<not> semantics e (f(n := \<lambda>w. x)) g p\<close>
      using DeltaExists by fast
    then consider
      \<open>\<not> semantics e (f(n := \<lambda>w. x)) g (subst A (Fun n []) 0)\<close> |
      \<open>\<exists>p \<in> set G. \<not> semantics e (f(n := \<lambda>w. x)) g p\<close>
      by auto
    then show False
    proof cases
      case 1
      then show ?thesis
        using ** by simp
    next
      case 2
      then obtain p where \<open>\<not> semantics e (f(n := \<lambda>w. x)) g p\<close> \<open>p \<in> set G\<close>
        by blast
      then have \<open>\<not> semantics e f g p\<close>
        using \<open>news n (A # G)\<close> by (metis Ball_set set_subset_Cons subsetCE upd_lemma)
      then show False
        using * \<open>p \<in> set G\<close> by simp
    qed
  qed
next
  case (DeltaNegForall A n G)
  show ?case
  proof (rule ccontr)
    assume \<open>\<not> (\<exists>p \<in> set (Neg (Uni A) # G). \<not> semantics e f g p)\<close>
    then have *: \<open>\<forall>p \<in> set (Neg (Uni A) # G). semantics e f g p\<close>
      by simp

    then obtain x where \<open>semantics (shift e 0 x) (f(n := \<lambda>w. x)) g (Neg A)\<close>
      using \<open>news n (A # G)\<close> by auto
    then have **: \<open>semantics e (f(n := \<lambda>w. x)) g (Neg (subst A (Fun n []) 0))\<close>
      by simp

    have \<open>\<exists>p \<in> set (Neg (subst A (Fun n []) 0) # G). \<not> semantics e (f(n := \<lambda>w. x)) g p\<close>
      using DeltaNegForall by fast
    then consider
      \<open>\<not> semantics e (f(n := \<lambda>w. x)) g (Neg (subst A (Fun n []) 0))\<close> |
      \<open>\<exists>p \<in> set G. \<not> semantics e (f(n := \<lambda>w. x)) g p\<close>
      by auto
    then show False
    proof cases
      case 1
      then show ?thesis
        using ** by simp
    next
      case 2
      then obtain p where \<open>\<not> semantics e (f(n := \<lambda>w. x)) g p\<close> \<open>p \<in> set G\<close>
        by blast
      then have \<open>\<not> semantics e f g p\<close>
        using \<open>news n (A # G)\<close> by (metis Ball_set set_subset_Cons subsetCE upd_lemma)
      then show False
        using * \<open>p \<in> set G\<close> by simp
    qed
  qed
qed auto

theorem tableau_soundness:
  \<open>tableauproof ps p \<Longrightarrow> list_all (semantics e f g) ps \<Longrightarrow> semantics e f g p\<close>
  using TC_soundness unfolding tableauproof_def list_all_def by fastforce

subsection \<open>Completeness\<close>

theorem infinite_nonempty: \<open>infinite A \<Longrightarrow> \<exists>x. x \<in> A\<close>
  by (simp add: ex_in_conv infinite_imp_nonempty)

theorem TCd_consistency:
  assumes inf_param: \<open>infinite (UNIV::'a set)\<close>
  shows \<open>consistency {S::('a, 'b) form set. \<exists>G. S = set G \<and> \<not> (\<stileturn> G)}\<close>
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S :: \<open>('a, 'b) form set\<close>
  assume \<open>S \<in> {set G |G. \<not> (\<stileturn> G)}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G :: \<open>('a, 'b) form list\<close>
    where *: \<open>S = set G\<close> and \<open>\<not> (\<stileturn> G)\<close>
    by blast

  { fix p ts
    assume \<open>Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S\<close>
    then show False
      using * Basic Order \<open>\<not> (\<stileturn> G)\<close> by fastforce }

  { assume \<open>\<bottom> \<in> S\<close>
    then show False
      using * BasicFF Order \<open>\<not> (\<stileturn> G)\<close> by fastforce }

  { assume \<open>Neg TT \<in> S\<close>
    then show False
      using * BasicNegTT Order \<open>\<not> (\<stileturn> G)\<close> by fastforce }

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Z # G)\<close>
      using * AlphaNegNeg Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>S \<union> {Z} = set (Z # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Z} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Con A B \<in> S\<close>
    then have \<open>\<not> (\<stileturn> A # B # G)\<close>
      using * AlphaAnd Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>S \<union> {A, B} = set (A # B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Dis A B) \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Neg A # Neg B # G)\<close>
      using * AlphaNegOr Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>S \<union> {Neg A, Neg B} = set (Neg A # Neg B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Neg A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Imp A B) \<in> S\<close>
    then have \<open>\<not> (\<stileturn> A # Neg B # G)\<close>
      using * AlphaNegImpl Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>{A, Neg B} \<union> S = set (A # Neg B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Dis A B \<in> S\<close>
    then have \<open>\<not> (\<stileturn> A # G) \<or> \<not> (\<stileturn> B # G)\<close>
      using * BetaOr Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    then show \<open>S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      using * by auto }

  { fix A B
    assume \<open>Neg (Con A B) \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Neg A # G) \<or> \<not> (\<stileturn> Neg B # G)\<close>
      using * BetaNegAnd Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    then show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C\<close>
      using * by auto }

  { fix A B
    assume \<open>Imp A B \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Neg A # G) \<or> \<not> (\<stileturn> B # G)\<close>
      using * BetaImpl Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    then show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      using * by auto }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Uni P \<in> S\<close>
    then have \<open>\<not> (\<stileturn> subst P t 0 # G)\<close>
      using * GammaForall Order\<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>S \<union> {subst P t 0} = set (subst P t 0 # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {subst P t 0} \<in> ?C\<close>
      by blast }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Neg (Exi P) \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Neg (subst P t 0) # G)\<close>
      using * GammaNegExists Order \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>S \<union> {Neg (subst P t 0)} = set (Neg (subst P t 0) # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Neg (subst P t 0)} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Exi P \<in> S\<close>
    have \<open>finite ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      by simp
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      using inf_param Diff_infinite_finite finite_compl infinite_UNIV_listI by blast
    then obtain x where **: \<open>x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      using infinite_imp_nonempty by blast
    then have \<open>news x (P # G)\<close>
      using Ball_set_list_all by auto
    then have \<open>\<not> (\<stileturn> subst P (Fun x []) 0 # G)\<close>
      using * \<open>Exi P \<in> S\<close> Order DeltaExists \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>S \<union> {subst P (Fun x []) 0} = set (subst P (Fun x []) 0 # G)\<close>
      using * by simp
    ultimately show \<open>\<exists>x. S \<union> {subst P (Fun x []) 0} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Neg (Uni P) \<in> S\<close>
    have \<open>finite ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      by simp
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      using inf_param Diff_infinite_finite finite_compl infinite_UNIV_listI by blast
    then obtain x where **: \<open>x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      using infinite_imp_nonempty by blast
    then have \<open>news x (P # G)\<close>
      using Ball_set_list_all by auto
    then have \<open>\<not> (\<stileturn> Neg (subst P (Fun x []) 0) # G)\<close>
      using * \<open>Neg (Uni P) \<in> S\<close> Order DeltaNegForall \<open>\<not> (\<stileturn> G)\<close>
      by (metis insert_absorb list.set(2) order_refl)
    moreover have \<open>S \<union> {Neg (subst P (Fun x []) 0)} = set (Neg (subst P (Fun x []) 0) # G)\<close>
      using * by simp
    ultimately show \<open>\<exists>x. S \<union> {Neg (subst P (Fun x []) 0)} \<in> ?C\<close>
      by blast }
qed

theorem tableau_completeness':
  fixes p :: \<open>(nat, nat) form\<close>
  assumes \<open>closed 0 p\<close>
    and \<open>list_all (closed 0) ps\<close>
    and mod: \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. list_all (semantics e f g) ps \<longrightarrow> semantics e f g p\<close>
  shows \<open>tableauproof ps p\<close>
proof (rule ccontr)
  fix e
  assume \<open>\<not> tableauproof ps p\<close>

  let ?S = \<open>set (Neg p # ps)\<close>
  let ?C = \<open>{set (G :: (nat, nat) form list) | G. \<not> (\<stileturn> G)}\<close>
  let ?f = HFun
  let ?g = \<open>(\<lambda>a ts. Pre a (terms_of_hterms ts) \<in> Extend ?S
              (mk_finite_char (mk_alt_consistency (close ?C))) from_nat)\<close>

  from \<open>list_all (closed 0) ps\<close>
  have \<open>\<forall>p \<in> set ps. closed 0 p\<close>
    by (simp add: list_all_iff)

  { fix x
    assume \<open>x \<in> ?S\<close>
    moreover have \<open>consistency ?C\<close>
      using TCd_consistency by blast
    moreover have \<open>?S \<in> ?C\<close>
      using \<open>\<not> tableauproof ps p\<close> unfolding tableauproof_def by blast
    moreover have \<open>infinite (- (\<Union>p \<in> ?S. params p))\<close>
      by (simp add: Compl_eq_Diff_UNIV infinite_UNIV_listI)
    moreover note \<open>closed 0 p\<close> \<open>\<forall>p \<in> set ps. closed 0 p\<close> \<open>x \<in> ?S\<close>
    then have \<open>closed 0 x\<close> by auto
    ultimately have \<open>semantics e ?f ?g x\<close>
      using model_existence by blast }
  then have \<open>list_all (semantics e ?f ?g) (Neg p # ps)\<close>
    by (simp add: list_all_iff)
  moreover have \<open>semantics e ?f ?g (Neg p)\<close>
    using calculation by simp
  moreover have \<open>list_all (semantics e ?f ?g) ps\<close>
    using calculation by simp
  then have \<open>semantics e ?f ?g p\<close>
    using mod by blast
  ultimately show False by simp
qed

subsection \<open>Open Formulas\<close>

lemma TC_psubst:
  fixes f :: \<open>'a \<Rightarrow> 'a\<close>
  assumes inf_params: \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>\<stileturn> G \<Longrightarrow> \<stileturn> map (psubst f) G\<close>
proof (induct G arbitrary: f rule: TC.induct)
  case (DeltaExists A n G)
  let ?params = \<open>params A \<union> (\<Union>p \<in> set G. params p)\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where *: \<open>fresh \<notin> ?params \<union> {n} \<union> image f ?params\<close>
    using ex_new_if_finite inf_params
    by (metis finite.emptyI finite.insertI finite_UnI finite_imageI)

  let ?f = \<open>f(n := fresh)\<close>

  have \<open>news n (A # G)\<close>
    using DeltaExists by blast
  then have \<open>new fresh (psubst ?f A)\<close> \<open>news fresh (map (psubst ?f) G)\<close>
    using * new_psubst_image news_psubst by (fastforce simp add: image_Un)+
  then have G: \<open>map (psubst ?f) G = map (psubst f) G\<close>
    using DeltaExists
    by (metis (mono_tags, lifting) Ball_set insertCI list.set(2) map_eq_conv psubst_upd)

  have \<open>\<stileturn> psubst ?f (subst A (Fun n []) 0) # map (psubst ?f) G\<close>
    using DeltaExists by (metis list.simps(9))
  then have \<open>\<stileturn> subst (psubst ?f A) (Fun fresh []) 0 # map (psubst ?f) G\<close>
    by simp
  moreover have \<open>news fresh (map (psubst ?f) (A # G))\<close>
    using \<open>new fresh (psubst ?f A)\<close> \<open>news fresh (map (psubst ?f) G)\<close> by simp
  then have \<open>news fresh (psubst ?f A # map (psubst ?f) G)\<close>
    by simp
  ultimately have \<open>\<stileturn> map (psubst ?f) (Exi A # G)\<close>
    using TC.DeltaExists by fastforce
  then show ?case
    using DeltaExists G by simp
next
  case (DeltaNegForall A n G)
  let ?params = \<open>params A \<union> (\<Union>p \<in> set G. params p)\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where *: \<open>fresh \<notin> ?params \<union> {n} \<union> image f ?params\<close>
    using ex_new_if_finite inf_params
    by (metis finite.emptyI finite.insertI finite_UnI finite_imageI)

  let ?f = \<open>f(n := fresh)\<close>

  have \<open>news n (A # G)\<close>
    using DeltaNegForall by blast
  then have \<open>new fresh (psubst ?f A)\<close> \<open>news fresh (map (psubst ?f) G)\<close>
    using * new_psubst_image news_psubst by (fastforce simp add: image_Un)+
  then have G: \<open>map (psubst ?f) G = map (psubst f) G\<close>
    using DeltaNegForall
    by (metis (mono_tags, lifting) Ball_set insertCI list.set(2) map_eq_conv psubst_upd)

  have \<open>\<stileturn> psubst ?f (Neg (subst A (Fun n []) 0)) # map (psubst ?f) G\<close>
    using DeltaNegForall by (metis list.simps(9))
  then have \<open>\<stileturn> Neg (subst (psubst ?f A) (Fun fresh []) 0) # map (psubst ?f) G\<close>
    by simp
  moreover have \<open>news fresh (map (psubst ?f) (A # G))\<close>
    using \<open>new fresh (psubst ?f A)\<close> \<open>news fresh (map (psubst ?f) G)\<close> by simp
  then have \<open>news fresh (psubst ?f A # map (psubst ?f) G)\<close>
    by simp
  ultimately have \<open>\<stileturn> map (psubst ?f) (Neg (Uni A) # G)\<close>
    using TC.DeltaNegForall by fastforce
  then show ?case
    using DeltaNegForall G by simp
next
  case (Order G G')
  then show ?case
    using TC.Order
  proof -
    have \<open>set (map (psubst f) G) \<subseteq> set (map (psubst f) G')\<close>
      using Order.hyps(3) by fastforce
    then show ?thesis
      using Order.hyps(2) TC.Order by blast
  qed
qed (auto intro: TC.intros)

lemma subcs_map: \<open>subcs c s G = map (subc c s) G\<close>
  by (induct G) simp_all

lemma TC_subcs:
  fixes G :: \<open>('a, 'b) form list\<close>
  assumes inf_params: \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>\<stileturn> G \<Longrightarrow> \<stileturn> subcs c s G\<close>
proof (induct G arbitrary: c s rule: TC.induct)
  case (GammaForall A t G)
  let ?params = \<open>params A \<union> (\<Union>p \<in> set G. params p) \<union> paramst s \<union> paramst t \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    using ex_new_if_finite inf_params by metis

  let ?f = \<open>id(c := fresh)\<close>
  let ?g = \<open>id(fresh := c)\<close>
  let ?s = \<open>psubstt ?f s\<close>

  have s: \<open>psubstt ?g ?s = s\<close>
    using fresh psubst_new_away' by simp
  have \<open>subc (?g c) (psubstt ?g ?s) (psubst ?g (Uni A)) = subc c s (Uni A)\<close>
    using fresh by simp
  then have A: \<open>psubst ?g (subc c ?s (Uni A)) = subc c s (Uni A)\<close>
    using fun_upd_apply id_def subc_psubst UnCI fresh params.simps(8) by metis
  have \<open>\<forall>x \<in> (\<Union>p \<in> set (Uni A # G). params p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  moreover have \<open>map (psubst ?g) (Uni A # G) = Uni A # G\<close>
    using fresh by (induct G) simp_all
  ultimately have G: \<open>map (psubst ?g) (subcs c ?s (Uni A # G)) = subcs c s (Uni A # G)\<close>
    using s A by (simp add: subcs_psubst)

  have \<open>new_term c ?s\<close>
    using fresh psubst_new_free' by fast
  then have \<open>\<stileturn> subc c ?s (subst A (subc_term c ?s t) 0) # subcs c ?s G\<close>
    using GammaForall by (metis new_subc_put subcs.simps(2))
  moreover have \<open>new_term c (subc_term c ?s t)\<close>
    using \<open>new_term c ?s\<close> new_subc_same' by simp
  ultimately have \<open>\<stileturn> subst (subc c (liftt ?s) A) (subc_term c ?s t) 0 # subcs c ?s G\<close>
    by simp
  moreover have \<open>Uni (subc c (liftt ?s) A) \<in> set (subcs c ?s (Uni A # G))\<close>
    by simp
  ultimately have \<open>\<stileturn> subcs c ?s (Uni A # G)\<close>
    using TC.GammaForall by simp
  then have \<open>\<stileturn> map (psubst ?g) (subcs c ?s (Uni A # G))\<close>
    using TC_psubst inf_params by blast
  then show \<open>\<stileturn> subcs c s (Uni A # G)\<close>
    using G by simp
next
  case (GammaNegExists A t G)
  let ?params = \<open>params A \<union> (\<Union>p \<in> set G. params p) \<union> paramst s \<union> paramst t \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    using ex_new_if_finite inf_params by metis

  let ?f = \<open>id(c := fresh)\<close>
  let ?g = \<open>id(fresh := c)\<close>
  let ?s = \<open>psubstt ?f s\<close>

  have s: \<open>psubstt ?g ?s = s\<close>
    using fresh psubst_new_away' by simp
  have \<open>subc (?g c) (psubstt ?g ?s) (psubst ?g (Neg (Exi A))) = subc c s (Neg (Exi A))\<close>
    using fresh by simp
  then have A: \<open>psubst ?g (subc c ?s (Neg (Exi A))) = subc c s (Neg (Exi A))\<close>
    using fun_upd_apply id_def subc_psubst UnCI fresh params.simps(7,9) by metis

  have \<open>\<forall>x \<in> (\<Union>p \<in> set (Neg (Exi A) # G). params p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  moreover have \<open>map (psubst ?g) (Neg (Exi A) # G) = Neg (Exi A) # G\<close>
    using fresh by (induct G) simp_all
  ultimately have G: \<open>map (psubst ?g) (subcs c ?s (Neg (Exi A) # G)) =
      subcs c s (Neg (Exi A) # G)\<close>
    using s A by (simp add: subcs_psubst)

  have \<open>new_term c ?s\<close>
    using fresh psubst_new_free' by fast
  then have \<open>\<stileturn> Neg (subc c ?s (subst A (subc_term c ?s t) 0)) # subcs c ?s G\<close>
    using GammaNegExists by (metis new_subc_put subc.simps(4) subcs.simps(2))
  moreover have \<open>new_term c (subc_term c ?s t)\<close>
    using \<open>new_term c ?s\<close> new_subc_same' by simp
  ultimately have \<open>\<stileturn> Neg (subst (subc c (liftt ?s) A) (subc_term c ?s t) 0) # subcs c ?s G\<close>
    by simp
  moreover have \<open>Neg (Exi (subc c (liftt ?s) A)) \<in> set (subcs c ?s (Neg (Exi A) # G))\<close>
    by simp
  ultimately have \<open>\<stileturn> subcs c ?s (Neg (Exi A) # G)\<close>
    using TC.GammaNegExists by simp
  then have \<open>\<stileturn> map (psubst ?g) (subcs c ?s (Neg (Exi A) # G))\<close>
    using TC_psubst inf_params by blast
  then show \<open>\<stileturn> subcs c s (Neg (Exi A) # G)\<close>
    using G by simp
next
  case (DeltaExists A n G)
  then show ?case
  proof (cases \<open>c = n\<close>)
    case True
    then have \<open>\<stileturn> Exi A # G\<close>
      using DeltaExists TC.DeltaExists by metis
    moreover have \<open>new c A\<close> and \<open>news c G\<close>
      using DeltaExists True by simp_all
    ultimately show ?thesis
      by (simp add: subcs_news)
  next
    case False
    let ?params = \<open>params A \<union> (\<Union>p \<in> set G. params p) \<union> paramst s \<union> {c} \<union> {n}\<close>

    have \<open>finite ?params\<close>
      by simp
    then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
      using ex_new_if_finite inf_params by metis

    let ?s = \<open>psubstt (id(n := fresh)) s\<close>
    let ?f = \<open>id(n := fresh, fresh := n)\<close>

    have f: \<open>\<forall>x \<in> ?params. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using fresh by simp

    have \<open>new_term n ?s\<close>
      using fresh psubst_new_free' by fast
    then have \<open>psubstt ?f ?s = psubstt (id(fresh := n)) ?s\<close>
      by (metis fun_upd_twist psubstt_upd(1))
    then have psubst_s: \<open>psubstt ?f ?s = s\<close>
      using fresh psubst_new_away' by simp

    have \<open>?f c = c\<close> and \<open>new_term c (Fun fresh [])\<close>
      using False fresh by auto

    have \<open>psubst ?f (subc c ?s (subst A (Fun n []) 0)) =
      subc (?f c) (psubstt ?f ?s) (psubst ?f (subst A (Fun n []) 0))\<close>
      by (simp add: subc_psubst)
    also have \<open>\<dots> = subc c s (subst (psubst ?f A) (Fun fresh []) 0)\<close>
      using \<open>?f c = c\<close> psubst_subst psubst_s by simp
    also have \<open>\<dots> = subc c s (subst A (Fun fresh []) 0)\<close>
      using DeltaExists fresh by simp
    finally have psubst_A: \<open>psubst ?f (subc c ?s (subst A (Fun n []) 0)) =
        subst (subc c (liftt s) A) (Fun fresh []) 0\<close>
      using \<open>new_term c (Fun fresh [])\<close> by simp

    have \<open>news n G\<close>
      using DeltaExists by simp
    moreover have \<open>news fresh G\<close>
      using fresh by (induct G) simp_all
    ultimately have \<open>map (psubst ?f) G = G\<close>
      by (induct G) simp_all
    moreover have \<open>\<forall>x \<in> \<Union>p \<in> set G. params p. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      by auto
    ultimately have psubst_G: \<open>map (psubst ?f) (subcs c ?s G) = subcs c s G\<close>
      using \<open>?f c = c\<close> psubst_s by (simp add: subcs_psubst)

    have \<open>\<stileturn> subc c ?s (subst A (Fun n []) 0) # subcs c ?s G\<close>
      using DeltaExists by simp
    then have \<open>\<stileturn> psubst ?f (subc c ?s (subst A (Fun n []) 0)) # map (psubst ?f) (subcs c ?s G)\<close>
      using TC_psubst inf_params DeltaExists.hyps(3) by fastforce
    then have \<open>\<stileturn> psubst ?f (subc c ?s (subst A (Fun n []) 0)) # subcs c s G\<close>
      using psubst_G by simp
    then have sub_A: \<open>\<stileturn> subst (subc c (liftt s) A) (Fun fresh []) 0 # subcs c s G\<close>
      using psubst_A by simp

    have \<open>new_term fresh s\<close>
      using fresh by simp
    then have \<open>new_term fresh (liftt s)\<close>
      by simp
    then have \<open>new fresh (subc c (liftt s) A)\<close>
      using fresh new_subc by simp
    moreover have \<open>news fresh (subcs c s G)\<close>
      using \<open>news fresh G\<close> \<open>new_term fresh s\<close> news_subcs by fast
    ultimately show \<open>\<stileturn> subcs c s (Exi A # G)\<close>
      using TC.DeltaExists sub_A by fastforce
  qed
next
  case (DeltaNegForall A n G)
  then show ?case
  proof (cases \<open>c = n\<close>)
    case True
    then have \<open>\<stileturn> Neg (Uni A) # G\<close>
      using DeltaNegForall TC.DeltaNegForall by metis
    moreover have \<open>new c A\<close> and \<open>news c G\<close>
      using DeltaNegForall True by simp_all
    ultimately show ?thesis
      by (simp add: subcs_news)
  next
    case False
    let ?params = \<open>params A \<union> (\<Union>p \<in> set G. params p) \<union> paramst s \<union> {c} \<union> {n}\<close>

    have \<open>finite ?params\<close>
      by simp
    then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
      using ex_new_if_finite inf_params by metis

    let ?s = \<open>psubstt (id(n := fresh)) s\<close>
    let ?f = \<open>id(n := fresh, fresh := n)\<close>

    have f: \<open>\<forall>x \<in> ?params. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using fresh by simp

    have \<open>new_term n ?s\<close>
      using fresh psubst_new_free' by fast
    then have \<open>psubstt ?f ?s = psubstt (id(fresh := n)) ?s\<close>
      using fun_upd_twist psubstt_upd(1) by metis
    then have psubst_s: \<open>psubstt ?f ?s = s\<close>
      using fresh psubst_new_away' by simp

    have \<open>?f c = c\<close> and \<open>new_term c (Fun fresh [])\<close>
      using False fresh by auto

    have \<open>psubst ?f (subc c ?s (Neg (subst A (Fun n []) 0))) =
      subc (?f c) (psubstt ?f ?s) (psubst ?f (Neg (subst A (Fun n []) 0)))\<close>
      by (simp add: subc_psubst)
    also have \<open>\<dots> = subc c s (Neg (subst (psubst ?f A)(Fun fresh []) 0))\<close>
      using \<open>?f c = c\<close> psubst_subst psubst_s by simp
    also have \<open>\<dots> = subc c s (Neg (subst A (Fun fresh []) 0))\<close>
      using DeltaNegForall fresh by simp
    finally have psubst_A: \<open>psubst ?f (subc c ?s (Neg (subst A (Fun n []) 0))) =
        Neg (subst (subc c (liftt s) A) (Fun fresh []) 0)\<close>
      using \<open>new_term c (Fun fresh [])\<close> by simp

    have \<open>news n G\<close>
      using DeltaNegForall by simp
    moreover have \<open>news fresh G\<close>
      using fresh by (induct G) simp_all
    ultimately have \<open>map (psubst ?f) G = G\<close>
      by (induct G) simp_all
    moreover have \<open>\<forall>x \<in> \<Union>p \<in> set G. params p. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      by auto
    ultimately have psubst_G: \<open>map (psubst ?f) (subcs c ?s G) = subcs c s G\<close>
      using \<open>?f c = c\<close> psubst_s by (simp add: subcs_psubst)

    have \<open>\<stileturn> subc c ?s (Neg (subst A (Fun n []) 0)) # subcs c ?s G\<close>
      using DeltaNegForall by simp
    then have \<open>\<stileturn> psubst ?f (subc c ?s (Neg (subst A (Fun n []) 0)))
                # map (psubst ?f) (subcs c ?s G)\<close>
      using TC_psubst inf_params DeltaNegForall.hyps(3) by fastforce
    then have \<open>\<stileturn> psubst ?f (subc c ?s (Neg (subst A (Fun n []) 0))) # subcs c s G\<close>
      using psubst_G by simp
    then have sub_A: \<open>\<stileturn> Neg (subst (subc c (liftt s) A) (Fun fresh []) 0) # subcs c s G\<close>
      using psubst_A by simp

    have \<open>new_term fresh s\<close>
      using fresh by simp
    then have \<open>new_term fresh (liftt s)\<close>
      by simp
    then have \<open>new fresh (subc c (liftt s) A)\<close>
      using fresh new_subc by simp
    moreover have \<open>news fresh (subcs c s G)\<close>
      using \<open>news fresh G\<close> \<open>new_term fresh s\<close> news_subcs by fast
    ultimately show \<open>\<stileturn> subcs c s (Neg (Uni A) # G)\<close>
      using TC.DeltaNegForall sub_A by fastforce
  qed
next
  case (Order G G')
  then have \<open>set (subcs c s G) \<subseteq> set (subcs c s G')\<close>
    using set_map subcs_map subset_image_iff by (metis (no_types, lifting))
  then show ?case
    using Order TC.Order by blast
qed (auto intro: TC.intros)

lemma TC_map_subc:
  fixes G :: \<open>('a, 'b) form list\<close>
  assumes inf_params: \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>\<stileturn> G \<Longrightarrow> \<stileturn> map (subc c s) G\<close>
  using assms TC_subcs subcs_map by metis

lemma ex_all_closed: \<open>\<exists>m. list_all (closed m) G\<close>
proof (induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    unfolding list_all_def
    using ex_closed closed_mono
    by (metis Ball_set list_all_simps(1) nat_le_linear)
qed

primrec sub_consts :: \<open>'a list \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form\<close> where
  \<open>sub_consts [] p = p\<close>
| \<open>sub_consts (c # cs) p = sub_consts cs (subst p (Fun c []) (length cs))\<close>

lemma valid_sub_consts:
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g p\<close>
  shows \<open>semantics (e :: nat => 'a) f g (sub_consts cs p)\<close>
  using assms by (induct cs arbitrary: p) simp_all

lemma closed_sub' [simp]:
  assumes \<open>k \<le> m\<close> shows
    \<open>closedt (Suc m) t = closedt m (substt t (Fun c []) k)\<close>
    \<open>closedts (Suc m) l = closedts m (substts l (Fun c []) k)\<close>
  using assms by (induct t and l rule: closedt.induct closedts.induct) auto

lemma closed_sub: \<open>k \<le> m \<Longrightarrow> closed (Suc m) p = closed m (subst p (Fun c []) k)\<close>
  by (induct p arbitrary: m k) simp_all

lemma closed_sub_consts: \<open>length cs = k \<Longrightarrow> closed m (sub_consts cs p) = closed (m + k) p\<close>
proof (induct cs arbitrary: k p)
  case Nil
  then show ?case
    by simp
next
  case (Cons c cs)
  then show ?case
    using closed_sub by fastforce
qed

lemma map_sub_consts_Nil: \<open>map (sub_consts []) G = G\<close>
  by (induct G) simp_all

primrec conjoin :: \<open>('a, 'b) form list \<Rightarrow> ('a, 'b) form\<close> where
  \<open>conjoin [] = Neg \<bottom>\<close>
| \<open>conjoin (p # ps) = Con p (conjoin ps)\<close>

lemma eval_conjoin: \<open>list_all (semantics e f g) G = semantics e f g (conjoin G)\<close>
  by (induct G) simp_all

lemma valid_sub:
  fixes e :: \<open>nat \<Rightarrow> 'a\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g p \<longrightarrow> semantics e f g q\<close>
  shows \<open>semantics e f g (subst p t m) \<longrightarrow> semantics e f g (subst q t m)\<close>
  using assms by simp

lemma eval_sub_consts:
  fixes e :: \<open>nat \<Rightarrow> 'a\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g p \<longrightarrow> semantics e f g q\<close>
    and \<open>semantics e f g (sub_consts cs p)\<close>
  shows \<open>semantics e f g (sub_consts cs q)\<close>
  using assms
proof (induct cs arbitrary: p q)
  case Nil
  then show ?case
    by simp
next
  case (Cons c cs)
  then show ?case
    by (metis sub_consts.simps(2) subst_lemma)
qed

lemma sub_consts_And [simp]: \<open>sub_consts cs (Con p q) = Con (sub_consts cs p) (sub_consts cs q)\<close>
  by (induct cs arbitrary: p q) simp_all

lemma sub_consts_conjoin:
  \<open>semantics e f g (sub_consts cs (conjoin G)) = semantics e f g (conjoin (map (sub_consts cs) G))\<close>
proof (induct G)
  case Nil
  then show ?case
    by (induct cs) simp_all
next
  case (Cons p G)
  then show ?case
    using sub_consts_And by simp
qed

lemma all_sub_consts_conjoin:
  \<open>list_all (semantics e f g) (map (sub_consts cs) G) = semantics e f g (sub_consts cs (conjoin G))\<close>
  by (induct G) (simp_all add: valid_sub_consts)

lemma valid_all_sub_consts:
  fixes e :: \<open>nat \<Rightarrow> 'a\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. list_all (semantics e f g) G \<longrightarrow> semantics e f g p\<close>
  shows \<open>list_all (semantics e f g) (map (sub_consts cs) G) \<longrightarrow> semantics e f g (sub_consts cs p)\<close>
  using assms eval_conjoin eval_sub_consts all_sub_consts_conjoin by metis

lemma TC_vars_for_consts:
  fixes G :: \<open>('a, 'b) form list\<close>
  assumes \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>\<stileturn> G \<Longrightarrow> \<stileturn> map (\<lambda>p. vars_for_consts p cs) G\<close>
proof (induct cs)
  case Nil
  then show ?case
    by simp
next
  case (Cons c cs)
  have \<open>(\<stileturn> map (\<lambda>p. vars_for_consts p (c # cs)) G) =
      (\<stileturn> map (\<lambda>p. subc c (Var (length cs)) (vars_for_consts p cs)) G)\<close>
    by simp
  also have \<open>\<dots> = (\<stileturn> map (subc c (Var (length cs)) o (\<lambda>p. vars_for_consts p cs)) G)\<close>
    unfolding comp_def by simp
  also have \<open>\<dots> = (\<stileturn> map (subc c (Var (length cs))) (map (\<lambda>p. vars_for_consts p cs) G))\<close>
    by simp
  finally show ?case
    using Cons TC_map_subc assms by metis
qed

lemma vars_for_consts_sub_consts:
  \<open>closed (length cs) p \<Longrightarrow> list_all (\<lambda>c. new c p) cs \<Longrightarrow> distinct cs \<Longrightarrow>
   vars_for_consts (sub_consts cs p) cs = p\<close>
proof (induct cs arbitrary: p)
  case (Cons c cs)
  then show ?case
    using subst_new_all closed_sub by force
qed simp

lemma all_vars_for_consts_sub_consts:
  \<open>list_all (closed (length cs)) G \<Longrightarrow> list_all (\<lambda>c. list_all (new c) G) cs \<Longrightarrow> distinct cs \<Longrightarrow>
   map (\<lambda>p. vars_for_consts p cs) (map (sub_consts cs) G) = G\<close>
  using vars_for_consts_sub_consts unfolding list_all_def
  by (induct G) fastforce+

lemma new_conjoin: \<open>new c (conjoin G) \<Longrightarrow> list_all (new c) G\<close>
  by (induct G) simp_all

lemma all_fresh_constants:
  fixes G :: \<open>('a, 'b) form list\<close>
  assumes \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>\<exists>cs. length cs = m \<and> list_all (\<lambda>c. list_all (new c) G) cs \<and> distinct cs\<close>
proof -
  obtain cs where \<open>length cs = m\<close> \<open>list_all (\<lambda>c. new c (conjoin G)) cs\<close> \<open>distinct cs\<close>
    using assms fresh_constants by blast
  then show ?thesis
    using new_conjoin unfolding list_all_def by metis
qed

lemma sub_consts_Neg: \<open>sub_consts cs (Neg p) = Neg (sub_consts cs p)\<close>
  by (induct cs arbitrary: p) simp_all

theorem tableau_completeness:
  fixes G :: \<open>(nat, nat) form list\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. list_all (semantics e f g) G \<longrightarrow> semantics e f g p\<close>
  shows \<open>tableauproof G p\<close>
proof -
  obtain m where *: \<open>list_all (closed m) (p # G)\<close>
    using ex_all_closed by blast
  moreover obtain cs where **:
    \<open>length cs = m\<close>
    \<open>distinct cs\<close>
    \<open>list_all (\<lambda>c. list_all (new c) (p # G)) cs\<close>
    using all_fresh_constants by blast
  ultimately have \<open>closed 0 (sub_consts cs p)\<close>
    using closed_sub_consts by fastforce
  moreover have \<open>list_all (closed 0) (map (sub_consts cs) G)\<close>
    using closed_sub_consts * \<open>length cs = m\<close> by (induct G) fastforce+

  moreover have \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. list_all (semantics e f g) (map (sub_consts cs) G) \<longrightarrow>
    semantics e f g (sub_consts cs p)\<close>
    using assms valid_all_sub_consts by blast
  ultimately have \<open>\<stileturn> Neg (sub_consts cs p) # map (sub_consts cs) G\<close>
    using tableau_completeness' unfolding tableauproof_def by simp
  then have \<open>\<stileturn> map (sub_consts cs) (Neg p # G)\<close>
    by (simp add: sub_consts_Neg)
  then have \<open>\<stileturn> map (\<lambda>p. vars_for_consts p cs) (map (sub_consts cs) (Neg p # G))\<close>
    using TC_vars_for_consts by blast
  then show ?thesis
    unfolding tableauproof_def
    using all_vars_for_consts_sub_consts[where G=\<open>Neg p # G\<close>] * ** by simp
qed

corollary
  fixes p :: \<open>(nat, nat) form\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p\<close>
  shows \<open>\<stileturn> [Neg p]\<close>
  using assms tableau_completeness unfolding tableauproof_def by simp

subsection \<open>Acknowledgements\<close>

text \<open>

\<^item> Mordechai (Moti) Ben-Ari:
Mathematical Logic for Computer Science.
\<^url>\<open>https://www.springer.com/gp/book/9781447141280\<close>

\<close>

end
