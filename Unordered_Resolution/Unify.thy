theory Unify imports
  "$ISAFOR/Rewriting/Unification" Resolution
begin

(* This theory obtains a proof of the unification lemma (the existence of mgus) by encoding literals as the terms used in IsaFoR. 
   Then the theory uses the unification lemma from IsaFoR.
   
   Here are two suggestions for other ways to solve the problem:
     1. Prove the unification lemma by adapting the relevant parts of IsaFoR in to this file.
        A clear advantage would be that this could lead to a smaller theory, since IsaFoR is quite big.
     2. Integrate the Unordered_Resolution project more closely with IsaFoR. That is, instead of having a definition of terms, 
        substitutions, unifiers, etc., this project could import these definitions from IsaFoR.
        A clear advantage is that then the two projects could take advantage of each others theorems. And it is (almost) always nice
        to reuse the work of others.
 *)

definition set_to_list :: "'a set \<Rightarrow> 'a list" where
  "set_to_list \<equiv> inv set"

lemma set_set_to_list: "finite xs \<Longrightarrow> set (set_to_list xs) = xs"
proof (induction rule: finite.induct)
  case (emptyI) 
  have "set [] = {}" by auto
  then show ?case unfolding set_to_list_def inv_into_def by auto
next
  case (insertI A a)
  then have "set (a#(set_to_list A)) = insert a A" by auto
  then show ?case unfolding set_to_list_def inv_into_def by (metis (mono_tags, lifting) UNIV_I someI) 
qed

fun iterm_to_fterm :: "(fun_sym, var_sym) term \<Rightarrow> fterm" where
  "iterm_to_fterm (Term.Var x) = Var x"
| "iterm_to_fterm (Term.Fun f ts) = Fun f (map iterm_to_fterm ts)"

fun fterm_to_iterm :: "fterm \<Rightarrow> (fun_sym, var_sym) term" where
  "fterm_to_iterm (Var x) = Term.Var x"
| "fterm_to_iterm (Fun f ts) = Term.Fun f (map fterm_to_iterm ts)"

lemma iterm_to_fterm_cancel[simp]: "iterm_to_fterm (fterm_to_iterm t) = t"
  by (induction t) (auto simp add: map_idI)

lemma fterm_to_iterm_cancel[simp]: "fterm_to_iterm (iterm_to_fterm t) = t"
  by (induction t) (auto simp add: map_idI)

abbreviation(input) fsub_to_isub :: "substitution \<Rightarrow> (fun_sym, var_sym) subst" where
  "fsub_to_isub \<sigma> == \<lambda>x. fterm_to_iterm (\<sigma> x)"

abbreviation(input) isub_to_fsub :: "(fun_sym, var_sym) subst \<Rightarrow> substitution" where
  "isub_to_fsub \<sigma> == \<lambda>x. iterm_to_fterm (\<sigma> x)"

lemma iterm_to_fterm_subt: "(iterm_to_fterm t1) {\<sigma>}\<^sub>t = iterm_to_fterm (t1 \<cdot> (\<lambda>x. fterm_to_iterm (\<sigma> x)))"
  by (induction t1) auto

lemma unifiert_unifiers:
  assumes "unifierts \<sigma> ts"
  shows "fsub_to_isub \<sigma> \<in> unifiers (fterm_to_iterm ` ts \<times> fterm_to_iterm ` ts)"
proof -
  have "\<forall>t1 \<in> fterm_to_iterm ` ts. \<forall>t2 \<in> fterm_to_iterm ` ts. t1 \<cdot> (fsub_to_isub \<sigma>) = t2 \<cdot> (fsub_to_isub \<sigma>)"
    proof (rule ballI;rule ballI)
      fix t1 t2 
      assume t1_p: "t1 \<in> fterm_to_iterm ` ts" assume t2_p: "t2 \<in> fterm_to_iterm ` ts"
      from t1_p t2_p have "iterm_to_fterm t1 \<in> ts \<and> iterm_to_fterm t2 \<in> ts" by auto 
      then have "(iterm_to_fterm t1) {\<sigma>}\<^sub>t = (iterm_to_fterm t2) {\<sigma>}\<^sub>t" using assms unfolding unifierts_def by auto
      then have "iterm_to_fterm (t1 \<cdot> (fsub_to_isub \<sigma>)) = iterm_to_fterm (t2 \<cdot> (fsub_to_isub \<sigma>))" using iterm_to_fterm_subt by auto 
      then have "fterm_to_iterm (iterm_to_fterm (t1 \<cdot> (fsub_to_isub \<sigma>))) = fterm_to_iterm (iterm_to_fterm (t2 \<cdot> (fsub_to_isub \<sigma>)))" by auto
      then show "t1 \<cdot> (fsub_to_isub \<sigma>) = t2 \<cdot> (fsub_to_isub \<sigma>)" using fterm_to_iterm_cancel by auto
    qed
  then have "\<forall>p\<in>fterm_to_iterm ` ts \<times> fterm_to_iterm ` ts. fst p \<cdot> (fsub_to_isub \<sigma>) = snd p \<cdot> (fsub_to_isub \<sigma>)" by (metis mem_Times_iff) 
  then show ?thesis unfolding unifiers_def by blast
qed

abbreviation(input) get_mgut :: "fterm list \<Rightarrow> substitution option" where
  "get_mgut ts \<equiv> map_option (isub_to_fsub \<circ> subst_of) (unify (List.product (map fterm_to_iterm ts) (map fterm_to_iterm ts)) [])"

lemma unify_unification:
  assumes "\<sigma> \<in> unifiers (set E)"
  shows "\<exists>\<theta>. is_imgu \<theta> (set E)"
proof -
  from assms have "\<exists>cs. unify E [] = Some cs" using unify_complete by auto
  then show ?thesis using unify_sound by auto
qed

lemma fterm_to_iterm_subst: "(fterm_to_iterm t1) \<cdot> \<sigma> =fterm_to_iterm (t1{isub_to_fsub \<sigma>}\<^sub>t)"
  by (induction t1) auto

lemma unifiers_unifiert:
  assumes "\<sigma> \<in> unifiers (fterm_to_iterm ` ts \<times> fterm_to_iterm ` ts)"
  shows "unifierts (isub_to_fsub \<sigma>) ts"
proof (cases "ts={}")
  assume "ts = {}"
  then show "unifierts (isub_to_fsub \<sigma>) ts" unfolding unifierts_def by auto
next
  assume "ts \<noteq> {}"
  then obtain t' where t'_p: "t' \<in> ts" by auto

  have "\<forall>t1\<in>ts. \<forall>t2\<in>ts. t1 {isub_to_fsub \<sigma>}\<^sub>t = t2 {isub_to_fsub \<sigma>}\<^sub>t"
    proof (rule ballI ; rule ballI)
      fix t1 t2 
      assume "t1 \<in> ts" "t2 \<in> ts" 
      then have "fterm_to_iterm t1 \<in> fterm_to_iterm ` ts" "fterm_to_iterm t2 \<in> fterm_to_iterm ` ts" by auto
      then have "(fterm_to_iterm t1, fterm_to_iterm t2) \<in> (fterm_to_iterm ` ts \<times> fterm_to_iterm ` ts)" by auto
      then have "(fterm_to_iterm t1) \<cdot> \<sigma> = (fterm_to_iterm t2) \<cdot> \<sigma>" using assms unfolding unifiers_def
         by (metis (no_types, lifting) assms fst_conv member_unifiersE snd_conv) 
      then have "fterm_to_iterm (t1{isub_to_fsub \<sigma>}\<^sub>t) = fterm_to_iterm (t2{isub_to_fsub \<sigma>}\<^sub>t)" using fterm_to_iterm_subst by auto
      then have "iterm_to_fterm (fterm_to_iterm (t1{isub_to_fsub \<sigma>}\<^sub>t)) =iterm_to_fterm (fterm_to_iterm (t2{isub_to_fsub \<sigma>}\<^sub>t))" by auto
      then show "t1{isub_to_fsub \<sigma>}\<^sub>t = t2{isub_to_fsub \<sigma>}\<^sub>t" by auto
    qed
  then have "\<forall>t2\<in>ts. t' {isub_to_fsub \<sigma>}\<^sub>t = t2 {isub_to_fsub \<sigma>}\<^sub>t" using t'_p by blast            
  then show "unifierts (isub_to_fsub \<sigma>) ts" unfolding unifierts_def by metis
qed

lemma icomp_fcomp: "\<theta> \<circ>\<^sub>s i = fsub_to_isub ((isub_to_fsub \<theta>) \<cdot> (isub_to_fsub i))"
  unfolding composition_def subst_compose_def
proof
  fix x
  show "\<theta> x \<cdot> i = fterm_to_iterm (iterm_to_fterm (\<theta> x){\<lambda>x. iterm_to_fterm (i x)}\<^sub>t)" using iterm_to_fterm_subt by auto
qed


lemma is_mgu_mguts: 
  assumes "finite ts"
  assumes "is_imgu \<theta> (fterm_to_iterm ` ts \<times> fterm_to_iterm ` ts)"
  shows "mguts (isub_to_fsub \<theta>) ts"
proof -
  from assms have "unifierts (isub_to_fsub \<theta>) ts" unfolding is_imgu_def using unifiers_unifiert by auto
  moreover have "\<forall>u. unifierts u ts \<longrightarrow> (\<exists>i. u = (isub_to_fsub \<theta>) \<cdot> i)"
    proof (rule allI; rule impI)
      fix u
      assume "unifierts u ts"
      then have "fsub_to_isub u \<in> unifiers (fterm_to_iterm ` ts \<times> fterm_to_iterm ` ts)" using unifiert_unifiers by auto
      then have "\<exists>i. fsub_to_isub u = \<theta> \<circ>\<^sub>s i" using assms unfolding is_imgu_def by auto
      then obtain i where "fsub_to_isub u = \<theta> \<circ>\<^sub>s i" by auto 
      then have "fsub_to_isub u =  fsub_to_isub ((isub_to_fsub \<theta>) \<cdot> (isub_to_fsub i))" using icomp_fcomp by auto
      then have "isub_to_fsub (fsub_to_isub u) = isub_to_fsub (fsub_to_isub ((isub_to_fsub \<theta>) \<cdot> (isub_to_fsub i)))" by metis
      then have "u = (isub_to_fsub \<theta>) \<cdot> (isub_to_fsub i)" by auto
      then show "\<exists>i. u = (isub_to_fsub \<theta>) \<cdot> i" by metis
    qed
  ultimately show ?thesis unfolding mguts_def by auto
qed

lemma unification':
  assumes "finite ts"
  assumes  "unifierts \<sigma> ts"
  shows "\<exists>\<theta>. mguts \<theta> ts"
proof -
  let ?E = "fterm_to_iterm ` ts \<times> fterm_to_iterm ` ts"
  let ?lE = "set_to_list ?E"
  from assms have "fsub_to_isub \<sigma> \<in> unifiers ?E" using unifiert_unifiers by auto
  then have "\<exists>\<theta>. is_imgu \<theta> ?E"
    using unify_unification[of "fsub_to_isub \<sigma>" ?lE] assms by (simp add: set_set_to_list)
  then obtain \<theta> where "is_imgu \<theta> ?E" unfolding set_to_list_def by auto
  then have "mguts (isub_to_fsub \<theta>) ts" using assms is_mgu_mguts by auto
  then show ?thesis by auto
qed

fun literal_to_term :: "fterm literal \<Rightarrow> fterm" where
  "literal_to_term (Pos p ts) = Fun ''Pos'' [Fun p ts]"
| "literal_to_term (Neg p ts) = Fun ''Neg'' [Fun p ts]"

fun term_to_literal :: "fterm \<Rightarrow> fterm literal" where
  "term_to_literal (Fun s [Fun p ts]) = (if s=''Pos'' then Pos else Neg) p ts"

lemma term_to_literal_cancel[simp]: "term_to_literal (literal_to_term l) = l"
  by (cases l) auto

lemma literal_to_term_sub: "literal_to_term (l{\<sigma>}\<^sub>l) = (literal_to_term l) {\<sigma>}\<^sub>t"
  by (induction l) auto


lemma unifierls_unifierts:
  assumes "unifierls \<sigma> L"
  shows "unifierts \<sigma> (literal_to_term `  L)"
proof -
  from assms obtain l' where "\<forall>l\<in>L. l{\<sigma>}\<^sub>l = l'" unfolding unifierls_def by auto
  then have "\<forall>l\<in>L. literal_to_term (l{\<sigma>}\<^sub>l) = literal_to_term l'" by auto
  then have "\<forall>l\<in>L. (literal_to_term l) {\<sigma>}\<^sub>t = literal_to_term l'" using literal_to_term_sub by auto
  then have "\<forall>t\<in>literal_to_term ` L. t{\<sigma>}\<^sub>t = literal_to_term l'" by auto 
  then show ?thesis unfolding unifierts_def by auto
qed

lemma unifiert_unifierls:
  assumes "unifierts \<sigma> (literal_to_term `  L)"
  shows "unifierls \<sigma> L"
proof -
  from assms obtain t' where "\<forall>t\<in>literal_to_term ` L. t{\<sigma>}\<^sub>t = t'" unfolding unifierts_def by auto
  then have "\<forall>t\<in>literal_to_term ` L. term_to_literal (t{\<sigma>}\<^sub>t) = term_to_literal t'"  by auto
  then have "\<forall>l\<in> L. term_to_literal ((literal_to_term l){\<sigma>}\<^sub>t) = term_to_literal t'" by auto
  then have "\<forall>l\<in> L. term_to_literal ((literal_to_term (l{\<sigma>}\<^sub>l))) = term_to_literal t'" using literal_to_term_sub by auto
  then have "\<forall>l\<in> L. l{\<sigma>}\<^sub>l = term_to_literal t'" by auto 
  then show ?thesis unfolding unifierls_def by auto
qed

lemma mguts_mguls:
  assumes "mguts \<theta> (literal_to_term `  L)"
  shows "mguls \<theta> L"
proof -
  from assms have "unifierts \<theta> (literal_to_term `  L)" unfolding mguts_def by auto
  then have "unifierls \<theta> L" using unifiert_unifierls by auto
  moreover
  {
    fix u
    assume "unifierls u L"
    then have "unifierts u (literal_to_term `  L)" using unifierls_unifierts by auto
    then have "\<exists>i. u = \<theta> \<cdot> i" using assms unfolding mguts_def by auto
  }
  ultimately show ?thesis unfolding mguls_def by auto
qed

lemma unification:
  assumes fin: "finite L"
  assumes uni: "unifierls \<sigma> L"
  shows "\<exists>\<theta>. mguls \<theta> L"
proof -
  from uni have "unifierts \<sigma> (literal_to_term `  L)" using unifierls_unifierts by auto
  then obtain \<theta> where "mguts \<theta> (literal_to_term `  L)" using fin unification' by blast
  then have "mguls \<theta> L" using mguts_mguls by auto
  then show ?thesis by auto
qed
  
end