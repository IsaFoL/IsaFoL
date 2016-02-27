theory Resolution imports TermsAndLiterals Tree "~~/src/HOL/IMP/Star" begin

section {* Terms and literals *}

fun complement :: "'t literal \<Rightarrow> 't literal" ("_\<^sup>c" [300] 300) where
  "(Pos P ts)\<^sup>c = Neg P ts"  
| "(Neg P ts)\<^sup>c = Pos P ts"

lemma cancel_comp1: "(l\<^sup>c)\<^sup>c = l" by (cases l) auto   

lemma cancel_comp2:
  assumes asm: "l\<^sub>1\<^sup>c = l\<^sub>2\<^sup>c"
  shows "l\<^sub>1 = l\<^sub>2"
proof -
  from asm have "(l\<^sub>1\<^sup>c)\<^sup>c = (l\<^sub>2\<^sup>c)\<^sup>c" by auto
  then have "l\<^sub>1 = (l\<^sub>2\<^sup>c)\<^sup>c" using cancel_comp1[of l\<^sub>1] by auto
  then show ?thesis using cancel_comp1[of l\<^sub>2] by auto
qed

lemma comp_exi1: "\<exists>l'. l' = l\<^sup>c" by (cases l) auto 

lemma comp_exi2: "\<exists>l. l' = l\<^sup>c"
proof
  show "l' = (l'\<^sup>c)\<^sup>c" using cancel_comp1[of l'] by auto
qed

lemma comp_swap: "l\<^sub>1\<^sup>c = l\<^sub>2 \<longleftrightarrow> l\<^sub>1 = l\<^sub>2\<^sup>c" 
proof -
  have "l\<^sub>1\<^sup>c = l\<^sub>2 \<Longrightarrow> l\<^sub>1 = l\<^sub>2\<^sup>c" using cancel_comp1[of l\<^sub>1] by auto
  moreover
  have "l\<^sub>1 = l\<^sub>2\<^sup>c \<Longrightarrow> l\<^sub>1\<^sup>c = l\<^sub>2" using cancel_comp1 by auto
  ultimately
  show ?thesis by auto
qed

lemma sign_comp: "sign l1 \<noteq> sign l2 \<and> get_pred l1 = get_pred l2 \<and> get_terms l1 = get_terms l2 \<longleftrightarrow> l2 = l1\<^sup>c"
apply (cases l1)
apply (cases l2)
apply auto
done

section {* Clauses *}

type_synonym 't clause = "'t literal set"
(* I Could also use fset or list or (finite) multisets of literals*)

abbreviation complementls :: "'t literal set \<Rightarrow> 't literal set" ("_\<^sup>C" [300] 300) where 
  "L\<^sup>C \<equiv> complement ` L"

lemma cancel_compls1: "(L\<^sup>C)\<^sup>C = L"
apply auto
apply (simp add: cancel_comp1)
apply (metis imageI cancel_comp1) 
done

lemma cancel_compls2:
  assumes asm: "L\<^sub>1\<^sup>C = L\<^sub>2\<^sup>C"
  shows "L\<^sub>1 = L\<^sub>2"
proof -
  from asm have "(L\<^sub>1\<^sup>C)\<^sup>C = (L\<^sub>2\<^sup>C)\<^sup>C" by auto
  then show ?thesis using cancel_compls1[of L\<^sub>1] cancel_compls1[of L\<^sub>2] by simp
qed

primrec varst  :: "fterm \<Rightarrow> var_sym set" (* I could use map here *)
and varsts :: "fterm list \<Rightarrow> var_sym set" where 
  "varst (Var x) = {x}"
| "varst (Fun f ts) = varsts ts"
| "varsts [] = {}"
| "varsts (t # ts) = (varst t) \<union> (varsts ts)"

definition varsl :: "fterm literal \<Rightarrow> var_sym set" where 
  "varsl l = varsts (get_terms l)"

definition varsls :: "fterm literal set \<Rightarrow> var_sym set" where 
  "varsls L \<equiv> \<Union>l\<in>L. varsl l"

abbreviation groundls :: "fterm clause \<Rightarrow> bool" where
  "groundls L \<equiv> \<forall> l \<in> L. groundl l"

lemma ground_varst: "ground t \<Longrightarrow> varst t = {}"  "grounds ts \<Longrightarrow> varsts ts = {}"
  by (induct t and ts rule: varst.induct varsts.induct) auto

lemma groundl_varsl: "groundl l \<Longrightarrow> varsl l = {}" unfolding varsl_def using ground_varst by auto

lemma groundls_varsls: "groundls ls \<Longrightarrow> varsls ls = {}" unfolding varsls_def using groundl_varsl by auto

lemma ground_comp: "groundl (l\<^sup>c) \<longleftrightarrow> groundl l" by (cases l) auto

lemma  ground_compls: "groundls (L\<^sup>C) \<longleftrightarrow> groundls L" using ground_comp by auto

(* Alternative - Collect variables with vars and see if empty set *)

section {* Semantics *}

type_synonym 'u fun_denot  = "fun_sym  \<Rightarrow> 'u list \<Rightarrow> 'u"
type_synonym 'u pred_denot = "pred_sym \<Rightarrow> 'u list \<Rightarrow> bool"
type_synonym 'u var_denot  = "var_sym  \<Rightarrow> 'u"

fun evalt  :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> fterm \<Rightarrow> 'u" where
  "evalt E F (Var x) = E x"
| "evalt E F (Fun f ts) = F f (map (evalt E F) ts)"

abbreviation evalts :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> fterm list \<Rightarrow> 'u list" where
  "evalts E F ts \<equiv> map (evalt E F) ts"

fun evall :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> 'u pred_denot \<Rightarrow> fterm literal \<Rightarrow> bool" where
  "evall E F G (Pos p ts) \<longleftrightarrow>  (G p (evalts E F ts))"
| "evall E F G (Neg p ts) \<longleftrightarrow> \<not>(G p (evalts E F ts))"

definition evalc :: "'u fun_denot \<Rightarrow> 'u pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "evalc F G C \<longleftrightarrow> (\<forall>E. \<exists>l \<in> C. evall E F G l)"

definition evalcs :: "'u fun_denot \<Rightarrow> 'u pred_denot \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "evalcs F G Cs \<longleftrightarrow> (\<forall>C \<in> Cs. evalc F G C)"

definition validcs :: "fterm clause set \<Rightarrow> bool" where
  "validcs Cs \<longleftrightarrow> (\<forall>F G. evalcs F G Cs)"

subsection {* Semantics of Ground Terms *}

lemma ground_var_denott: "ground t \<Longrightarrow> (evalt E F t = evalt E' F t)"
proof (induction t)
  case (Var x)
  then have "False" by auto
  then show ?case by auto
next
  case (Fun f ts)
  then have "\<forall>t \<in> set ts. ground t" by auto 
  then have "\<forall>t \<in> set ts. evalt E F t = evalt E' F t" using Fun by auto
  then have "evalts E F ts = evalts E' F ts" by auto
  then have "F f (map (evalt E F) ts) = F f (map (evalt E' F) ts)" by metis
  then show ?case by simp
qed

lemma ground_var_denotts: "grounds ts \<Longrightarrow> (evalts E F ts = evalts E' F ts)"
  using ground_var_denott by (metis map_eq_conv)


lemma ground_var_denot: "groundl l \<Longrightarrow> (evall E F G l = evall E' F G l)"
proof (induction l)
  case Pos then show ?case using ground_var_denotts by (metis evall.simps(1) literal.sel(3))
next
  case Neg then show ?case using ground_var_denotts by (metis evall.simps(2) literal.sel(4))
qed


section {* Substitutions *}

type_synonym substitution = "var_sym \<Rightarrow> fterm" 

(* Alternatives: 
    some more Concrete datastructure, e.g. association list
    var \<Rightarrow> Some fterm
   Both of those are Closer to both Ben-Ari and Chang&Lee, but they are more Complicated
*)

(* Another opportunity to use map. Mix-fix? *)
fun sub  :: "fterm \<Rightarrow> substitution \<Rightarrow> fterm" ("_{_}\<^sub>t" [300,0] 300) where
  "(Var x){\<sigma>}\<^sub>t = \<sigma> x"
| "(Fun f ts){\<sigma>}\<^sub>t = Fun f (map (\<lambda>t. t {\<sigma>}\<^sub>t) ts)"

abbreviation subs :: "fterm list \<Rightarrow> substitution \<Rightarrow> fterm list" ("_{_}\<^sub>t\<^sub>s" [300,0] 300) where
  "ts{\<sigma>}\<^sub>t\<^sub>s \<equiv> (map (\<lambda>t. t {\<sigma>}\<^sub>t) ts)"

fun subl :: "fterm literal \<Rightarrow> substitution \<Rightarrow> fterm literal" ("_{_}\<^sub>l" [300,0] 300) where
  "(Pos p ts){\<sigma>}\<^sub>l = Pos p (ts{\<sigma>}\<^sub>t\<^sub>s)"
| "(Neg p ts){\<sigma>}\<^sub>l = Neg p (ts{\<sigma>}\<^sub>t\<^sub>s)"

abbreviation subls :: "fterm literal set \<Rightarrow> substitution \<Rightarrow> fterm literal set" ("_{_}\<^sub>l\<^sub>s" [300,0] 300) where
  "L {\<sigma>}\<^sub>l\<^sub>s \<equiv> (\<lambda>l. l {\<sigma>}\<^sub>l) ` L"

lemma subls_def2: "L {\<sigma>}\<^sub>l\<^sub>s = {l {\<sigma>}\<^sub>l|l. l \<in> L}" by auto

definition instance_oft :: "fterm \<Rightarrow> fterm \<Rightarrow> bool" where
  "instance_oft t\<^sub>1 t\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. t\<^sub>1 = t\<^sub>2{\<sigma>}\<^sub>t)"

definition instance_ofts :: "fterm list \<Rightarrow> fterm list \<Rightarrow> bool" where
  "instance_ofts ts\<^sub>1 ts\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. ts\<^sub>1 = ts\<^sub>2{\<sigma>}\<^sub>t\<^sub>s)"

definition instance_ofl :: "fterm literal \<Rightarrow> fterm literal \<Rightarrow> bool" where
  "instance_ofl l\<^sub>1 l\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. l\<^sub>1 = l\<^sub>2{\<sigma>}\<^sub>l)"

definition instance_ofls :: "fterm clause \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "instance_ofls C\<^sub>1 C\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. C\<^sub>1 = C\<^sub>2{\<sigma>}\<^sub>l\<^sub>s)"

lemma comp_sub: "(l\<^sup>c) {\<sigma>}\<^sub>l=(l {\<sigma>}\<^sub>l)\<^sup>c" 
by (cases l) auto

lemma compls_subls: "(L\<^sup>C) {\<sigma>}\<^sub>l\<^sub>s=(L {\<sigma>}\<^sub>l\<^sub>s)\<^sup>C" 
using comp_sub apply auto
apply (metis image_eqI)
done

lemma subls_union: "(L\<^sub>1 \<union> L\<^sub>2) {\<sigma>}\<^sub>l\<^sub>s = L\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s \<union> L\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s" by auto

(* This definition Could be tighter. For instance with this definition we allow
  x \<rightarrow> Var x
  y \<rightarrow> Var x
   that two variable point to the same. We could and should perhaps disallow this.
   It could be done something like
   var_renaming \<sigma> \<longleftrightarrow> (\<exists>b. bijection b (UNIV::var_symbol) (UNIV::var_symbol) \<and> \<forall>x. \<sigma> x = Var (b x))

  Simple idea: Variable_renaming takes two clauses, and sees if they can be substituted to each other. I use this simple idea.
 *)

(* definition var_renaming :: "substitution \<Rightarrow> bool" where 
  "var_renaming \<sigma> \<longleftrightarrow> (\<forall>x. \<exists>y. \<sigma> x = Var y)" *)

definition var_renaming_of :: "fterm clause \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "var_renaming_of C1 C2 \<longleftrightarrow> instance_ofls C1 C2 \<and> instance_ofls C2 C1"

subsection {* The Empty Substitution *}

abbreviation \<epsilon> :: "substitution" where
  "\<epsilon> \<equiv> Var"

lemma empty_subt: "(t :: fterm){\<epsilon>}\<^sub>t = t" 
apply (induction t)
apply (auto simp add: map_idI)
done

lemma empty_subts: "ts {\<epsilon>}\<^sub>t\<^sub>s = ts" 
using empty_subt by auto

lemma empty_subl: "l {\<epsilon>}\<^sub>l = l" 
using empty_subts by (cases l) auto

lemma empty_subls: "L {\<epsilon>}\<^sub>l\<^sub>s = L" 
using empty_subl by auto

lemma instance_oft_self: "instance_oft t t"
unfolding instance_oft_def
proof 
  show "t = t{\<epsilon>}\<^sub>t" using empty_subt by auto
qed

lemma instance_ofts_self: "instance_ofts ts ts"
unfolding instance_ofts_def
proof 
  show "ts = ts{\<epsilon>}\<^sub>t\<^sub>s" using empty_subts by auto
qed

lemma instance_ofl_self: "instance_ofl l l"
unfolding instance_ofl_def
proof 
  show "l = l{\<epsilon>}\<^sub>l" using empty_subl by auto
qed

lemma instance_ofls_self: "instance_ofls L L"
unfolding instance_ofls_def
proof
  show "L = L{\<epsilon>}\<^sub>l\<^sub>s" using empty_subls by auto
qed

subsection {* Substitutions and Ground Terms *}

lemma ground_sub: "ground t \<Longrightarrow> t {\<sigma>}\<^sub>t = t"
apply (induction t)
apply (auto simp add: map_idI)
done

lemma ground_subs: "grounds ts \<Longrightarrow> ts {\<sigma>}\<^sub>t\<^sub>s = ts" 
using ground_sub by (simp add: map_idI)

lemma groundl_subs: "groundl l \<Longrightarrow> l {\<sigma>}\<^sub>l = l" 
using ground_subs by (cases l) auto

lemma groundls_subls:
  assumes ground: "groundls L"
  shows "L {\<sigma>}\<^sub>l\<^sub>s = L"
proof -
  {
    fix l
    assume l_L: "l \<in> L"
    then have "groundl l" using ground by auto
    then have "l = l{\<sigma>}\<^sub>l" using groundl_subs by auto
    moreover
    then have "l {\<sigma>}\<^sub>l \<in> L {\<sigma>}\<^sub>l\<^sub>s" using l_L by auto
    ultimately
    have "l \<in> L {\<sigma>}\<^sub>l\<^sub>s" by auto
  }
  moreover
  {
    fix l
    assume l_L: "l \<in> L {\<sigma>}\<^sub>l\<^sub>s"
    then obtain l' where l'_p: "l' \<in> L \<and> l' {\<sigma>}\<^sub>l = l" by auto
    then have "l' = l" using ground groundl_subs by auto
    from l_L l'_p this have "l \<in> L" by auto
  } 
  ultimately show ?thesis by auto
qed

subsection {* Composition *}

(* apply \<sigma>\<^sub>2 to all the range of \<sigma>\<^sub>1 
  - because of the substitution definition, this is different from (and simpler than) in the books. *)
definition composition :: "substitution \<Rightarrow> substitution \<Rightarrow> substitution"  (infixl "\<cdot>" 55) where
  "(\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) x = (\<sigma>\<^sub>1 x){\<sigma>\<^sub>2}\<^sub>t"

lemma composition_conseq2t:  "t{\<sigma>\<^sub>1}\<^sub>t{\<sigma>\<^sub>2}\<^sub>t = t{\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2}\<^sub>t" 
proof (induction t)
  case (Var x) 
  have "(Var x){\<sigma>\<^sub>1}\<^sub>t{\<sigma>\<^sub>2}\<^sub>t = (\<sigma>\<^sub>1 x){\<sigma>\<^sub>2}\<^sub>t" by simp
  also have " ... = (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) x" unfolding composition_def by simp
  finally show ?case by auto
next
  case (Fun t ts)
  then show ?case unfolding composition_def by auto
qed

lemma composition_conseq2ts: "ts{\<sigma>\<^sub>1}\<^sub>t\<^sub>s{\<sigma>\<^sub>2}\<^sub>t\<^sub>s = ts{\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2}\<^sub>t\<^sub>s"
  using composition_conseq2t by auto

lemma composition_conseq2l: "l{\<sigma>\<^sub>1}\<^sub>l{\<sigma>\<^sub>2}\<^sub>l = l{\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2}\<^sub>l" 
  using composition_conseq2t by (cases l) auto 

lemma composition_conseq2ls: "L{\<sigma>\<^sub>1}\<^sub>l\<^sub>s{\<sigma>\<^sub>2}\<^sub>l\<^sub>s = L{\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2}\<^sub>l\<^sub>s" 
using composition_conseq2l apply auto
apply (metis imageI) 
done
  

lemma composition_assoc: "\<sigma>\<^sub>1 \<cdot> (\<sigma>\<^sub>2 \<cdot> \<sigma>\<^sub>3) = (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) \<cdot> \<sigma>\<^sub>3" 
proof
  fix x
  show "(\<sigma>\<^sub>1 \<cdot> (\<sigma>\<^sub>2 \<cdot> \<sigma>\<^sub>3)) x = ((\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) \<cdot> \<sigma>\<^sub>3) x" unfolding composition_def using composition_conseq2t by simp
qed

lemma empty_comp1: "(\<sigma> \<cdot> \<epsilon>) = \<sigma>" 
proof
  fix x
  show "(\<sigma> \<cdot> \<epsilon>) x = \<sigma> x" unfolding composition_def using empty_subt by auto 
qed

lemma empty_comp2: "(\<epsilon> \<cdot> \<sigma>) = \<sigma>" 
proof
  fix x
  show "(\<epsilon> \<cdot> \<sigma>) x = \<sigma> x" unfolding composition_def by simp
qed

lemma instance_oft_trans : 
  assumes t\<^sub>1\<^sub>2: "instance_oft t\<^sub>1 t\<^sub>2"
  assumes t\<^sub>2\<^sub>3: "instance_oft t\<^sub>2 t\<^sub>3"
  shows "instance_oft t\<^sub>1 t\<^sub>3"
proof -
  from t\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "t\<^sub>1 = t\<^sub>2 {\<sigma>\<^sub>1\<^sub>2}\<^sub>t" 
    unfolding instance_oft_def by auto
  moreover
  from t\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "t\<^sub>2 = t\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>t" 
    unfolding instance_oft_def by auto
  ultimately
  have "t\<^sub>1 = t\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>t {\<sigma>\<^sub>1\<^sub>2}\<^sub>t" by auto
  then have "t\<^sub>1 = t\<^sub>3 {\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2}\<^sub>t" using composition_conseq2t by simp
  then show ?thesis unfolding instance_oft_def by auto
qed

lemma instance_ofts_trans : 
  assumes ts\<^sub>1\<^sub>2: "instance_ofts ts\<^sub>1 ts\<^sub>2"
  assumes ts\<^sub>2\<^sub>3: "instance_ofts ts\<^sub>2 ts\<^sub>3"
  shows "instance_ofts ts\<^sub>1 ts\<^sub>3"
proof -
  from ts\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "ts\<^sub>1 = ts\<^sub>2 {\<sigma>\<^sub>1\<^sub>2}\<^sub>t\<^sub>s" 
    unfolding instance_ofts_def by auto
  moreover
  from ts\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "ts\<^sub>2 = ts\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>t\<^sub>s" 
    unfolding instance_ofts_def by auto
  ultimately
  have "ts\<^sub>1 = ts\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>t\<^sub>s {\<sigma>\<^sub>1\<^sub>2}\<^sub>t\<^sub>s" by auto
  then have "ts\<^sub>1 = ts\<^sub>3 {\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2}\<^sub>t\<^sub>s" using composition_conseq2ts by simp
  then show ?thesis unfolding instance_ofts_def by auto
qed

lemma instance_ofl_trans : 
  assumes l\<^sub>1\<^sub>2: "instance_ofl l\<^sub>1 l\<^sub>2"
  assumes l\<^sub>2\<^sub>3: "instance_ofl l\<^sub>2 l\<^sub>3"
  shows "instance_ofl l\<^sub>1 l\<^sub>3"
proof -
  from l\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "l\<^sub>1 = l\<^sub>2 {\<sigma>\<^sub>1\<^sub>2}\<^sub>l" 
    unfolding instance_ofl_def by auto
  moreover
  from l\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "l\<^sub>2 = l\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>l" 
    unfolding instance_ofl_def by auto
  ultimately
  have "l\<^sub>1 = l\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>l {\<sigma>\<^sub>1\<^sub>2}\<^sub>l" by auto
  then have "l\<^sub>1 = l\<^sub>3 {\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2}\<^sub>l" using composition_conseq2l by simp
  then show ?thesis unfolding instance_ofl_def by auto
qed

lemma instance_ofls_trans : 
  assumes L\<^sub>1\<^sub>2: "instance_ofls L\<^sub>1 L\<^sub>2"
  assumes L\<^sub>2\<^sub>3: "instance_ofls L\<^sub>2 L\<^sub>3"
  shows "instance_ofls L\<^sub>1 L\<^sub>3"
proof -
  from L\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "L\<^sub>1 = L\<^sub>2 {\<sigma>\<^sub>1\<^sub>2}\<^sub>l\<^sub>s" 
    unfolding instance_ofls_def by auto
  moreover
  from L\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "L\<^sub>2 = L\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>l\<^sub>s" 
    unfolding instance_ofls_def by auto
  ultimately
  have "L\<^sub>1 = L\<^sub>3 {\<sigma>\<^sub>2\<^sub>3}\<^sub>l\<^sub>s {\<sigma>\<^sub>1\<^sub>2}\<^sub>l\<^sub>s" by auto
  then have "L\<^sub>1 = L\<^sub>3 {\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2}\<^sub>l\<^sub>s" using composition_conseq2ls by simp
  then show ?thesis unfolding instance_ofls_def by auto
qed

subsection {* Merging substitutions *}
lemma project_sub:
  assumes inst_C:"C {\<mu>}\<^sub>l\<^sub>s = C'" (* lmbd instead of mu would fit better with below proofs *) (* This equality could be removed from the lemma *)
  assumes L'sub: "L' \<subseteq> C'"
  shows "\<exists>L \<subseteq> C. L {\<mu>}\<^sub>l\<^sub>s = L' \<and> (C-L) {\<mu>}\<^sub>l\<^sub>s = C' - L'"
proof -
  let ?L = "{l \<in> C. \<exists>l' \<in> L'. l {\<mu>}\<^sub>l = l'}"
  have "?L \<subseteq> C" by auto
  moreover
  have "?L {\<mu>}\<^sub>l\<^sub>s = L'"
    proof (rule Orderings.order_antisym; rule Set.subsetI)
      fix l'
      assume l'L: "l' \<in> L'"
      from inst_C have "{l {\<mu>}\<^sub>l|l. l \<in> C} = C'" unfolding subls_def2 by -
      then have "\<exists>l. l' = l {\<mu>}\<^sub>l \<and> l \<in> C \<and> l{\<mu>}\<^sub>l \<in> L'" using L'sub l'L by auto
      then have " l' \<in> {l \<in> C. l{\<mu>}\<^sub>l \<in> L'}{\<mu>}\<^sub>l\<^sub>s" by auto
      then show " l' \<in> {l \<in> C. \<exists>l'\<in>L'. l{\<mu>}\<^sub>l = l'}{\<mu>}\<^sub>l\<^sub>s" by auto
    qed auto
  moreover
  have "(C-?L) {\<mu>}\<^sub>l\<^sub>s = C' - L'" using inst_C by auto
  moreover
  ultimately show ?thesis by auto
qed

lemma relevant_vars_subt:
  "\<forall>x \<in> varst t. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x \<Longrightarrow> t {\<sigma>\<^sub>1}\<^sub>t = t {\<sigma>\<^sub>2}\<^sub>t" (* "\<forall>x \<in> varsts ts. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x \<Longrightarrow> ts {\<sigma>\<^sub>1}\<^sub>t\<^sub>s = ts {\<sigma>\<^sub>2}\<^sub>t\<^sub>s"*)
proof (induction t)
  case (Fun f ts)
  have f: "\<And>t. t \<in> set ts \<Longrightarrow> varst t \<subseteq> varsts ts" by (induction ts) auto
  have "\<forall>t\<in>set ts. t{\<sigma>\<^sub>1}\<^sub>t = t{\<sigma>\<^sub>2}\<^sub>t" 
    proof
      fix t
      assume tints: "t \<in> set ts"
      then have "\<forall>x\<in>varst t. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x" using f Fun(2) by auto
      then show "t{\<sigma>\<^sub>1}\<^sub>t = t{\<sigma>\<^sub>2}\<^sub>t" using Fun tints by auto
    qed
  then have "ts{\<sigma>\<^sub>1}\<^sub>t\<^sub>s = ts{\<sigma>\<^sub>2}\<^sub>t\<^sub>s" by auto
  then show ?case by auto
qed auto

lemma relevant_vars_subts: (* copy paste from above proof *)
  assumes asm: "\<forall>x \<in> varsts ts. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
  shows "ts {\<sigma>\<^sub>1}\<^sub>t\<^sub>s = ts {\<sigma>\<^sub>2}\<^sub>t\<^sub>s" 
proof -
   have f: "\<And>t. t \<in> set ts \<Longrightarrow> varst t \<subseteq> varsts ts" by (induction ts) auto
   have "\<forall>t\<in>set ts. t{\<sigma>\<^sub>1}\<^sub>t = t{\<sigma>\<^sub>2}\<^sub>t" 
    proof
      fix t
      assume tints: "t \<in> set ts"
      then have "\<forall>x\<in>varst t. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x" using f asm by auto
      then show "t{\<sigma>\<^sub>1}\<^sub>t = t{\<sigma>\<^sub>2}\<^sub>t" using relevant_vars_subt tints by auto
    qed
  then show ?thesis by auto
qed

lemma relevant_vars_subl:
  "\<forall>x \<in> varsl l. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x \<Longrightarrow> l {\<sigma>\<^sub>1}\<^sub>l = l {\<sigma>\<^sub>2}\<^sub>l"
proof (induction l)
  case (Pos p ts)
  then show ?case using relevant_vars_subts unfolding varsl_def by auto
next
  case (Neg p ts)
  then show ?case using relevant_vars_subts unfolding varsl_def by auto
qed

lemma relevant_vars_subls: (* in many ways a mirror of relevant_vars_subts  *)
  assumes asm: "\<forall>x \<in> varsls L. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
  shows "L {\<sigma>\<^sub>1}\<^sub>l\<^sub>s = L {\<sigma>\<^sub>2}\<^sub>l\<^sub>s"
proof -
  have f: "\<And>l. l \<in> L \<Longrightarrow> varsl l \<subseteq> varsls L" unfolding varsls_def by auto
  have "\<forall>l \<in> L. l {\<sigma>\<^sub>1}\<^sub>l = l {\<sigma>\<^sub>2}\<^sub>l"
    proof
      fix l
      assume linls: "l\<in>L"
      then have "\<forall>x\<in>varsl l. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x" using f asm by auto
      then show "l{\<sigma>\<^sub>1}\<^sub>l = l{\<sigma>\<^sub>2}\<^sub>l" using relevant_vars_subl linls by auto
    qed
  then show ?thesis by (meson image_cong) 
qed

lemma merge_sub: (* To prove this I should make a lemma that says literals only care about the variables that are in them *)
  assumes dist: "varsls C \<inter> varsls D = {}"
  assumes CC': "C {lmbd}\<^sub>l\<^sub>s = C'"
  assumes DD': "D {\<mu>}\<^sub>l\<^sub>s = D'"
  shows "\<exists>\<eta>. C {\<eta>}\<^sub>l\<^sub>s = C' \<and> D {\<eta>}\<^sub>l\<^sub>s = D'"
proof -
  let ?\<eta> = "\<lambda>x. if x \<in> varsls C then lmbd x else \<mu> x"
  have " \<forall>x\<in>varsls C. ?\<eta> x = lmbd x" by auto
  then have "C {?\<eta>}\<^sub>l\<^sub>s = C {lmbd}\<^sub>l\<^sub>s" using relevant_vars_subls[of C ?\<eta> lmbd] by auto
  then have "C {?\<eta>}\<^sub>l\<^sub>s = C'" using CC' by auto
  moreover
  have " \<forall>x\<in>varsls D. ?\<eta> x = \<mu> x" using dist by auto
  then have "D {?\<eta>}\<^sub>l\<^sub>s = D {\<mu>}\<^sub>l\<^sub>s" using relevant_vars_subls[of D ?\<eta> \<mu>] by auto
  then have "D {?\<eta>}\<^sub>l\<^sub>s = D'" using DD' by auto
  ultimately
  show ?thesis by auto
qed

subsection {* Standardizing apart *}

abbreviation std1 :: "fterm clause \<Rightarrow> fterm clause" where
  "std1 C == C{\<lambda>x. Var (''1'' @ x)}\<^sub>l\<^sub>s"

abbreviation std2 :: "fterm clause \<Rightarrow> fterm clause" where
  "std2 C == C{\<lambda>x. Var (''2'' @ x)}\<^sub>l\<^sub>s"

definition std_apart :: "fterm clause \<Rightarrow> fterm clause \<Rightarrow> (fterm clause * fterm clause)" where
  "std_apart C\<^sub>1 C\<^sub>2 = (std1 C\<^sub>1, std2 C\<^sub>2)"

lemma std_apart'': 
  "x\<in>varst  (t  {\<lambda>x::char list. Var (y @ x) }\<^sub>t ) \<Longrightarrow> \<exists>x'. x=y@x'"
  "x\<in>varsts (ts {\<lambda>x::char list. Var (y @ x) }\<^sub>t\<^sub>s) \<Longrightarrow> \<exists>x'. x=y@x'"
by (induct t and ts rule: varst.induct varsts.induct) auto

lemma std_apart': "x\<in>varsl (l {\<lambda>x::char list. Var  (y@x) }\<^sub>l) \<Longrightarrow> \<exists>x'. x=y@x'"
unfolding varsl_def using std_apart'' by (cases l) auto

lemma std_apart_apart': "varsls (std1 C1) \<inter> varsls (std2 C2) = {}"
proof -
  {
    fix x
    assume xin: "x \<in> varsls (std1 C1) \<inter> varsls (std2 C2)"
    from xin have "x \<in> varsls (std1 C1)" by auto
    then have "\<exists>x'.  x=''1'' @ x'" 
      using std_apart'[of x _ "''1''"] unfolding varsls_def by auto
    moreover
    from xin have "x \<in> varsls (std2 C2)" by auto
    then have "\<exists>x'. x= ''2'' @x' " 
      using std_apart'[of x _ "''2''"] unfolding varsls_def by auto
    ultimately have "False" by auto
    then have "x \<in> {}" by auto
  }
  then show ?thesis by auto 
qed

lemma std_apart_apart:
  assumes  "std_apart C1 C2 = (C1',C2')"
  shows "varsls C1' \<inter> varsls C2' = {}"
proof -
  from assms have C1'_x0: "C1' = C1{\<lambda>x. Var (''1'' @ x) }\<^sub>l\<^sub>s" unfolding std_apart_def by auto
  moreover
  from assms have C2'_x1: "C2' = C2{\<lambda>x. Var (''2'' @ x) }\<^sub>l\<^sub>s" unfolding std_apart_def by auto
  ultimately show ?thesis using std_apart_apart' by auto
qed

lemma std_apart_instance_ofls1': "instance_ofls C1 (std1 C1)"
proof -
  have empty: "(\<lambda>x. Var (''1''@x)) \<cdot> (\<lambda>x. Var (tl x)) = \<epsilon>" using composition_def by auto

  have "C1 {\<epsilon>}\<^sub>l\<^sub>s = C1" using empty_subls by auto
  then have "C1{(\<lambda>x. Var (''1''@x)) \<cdot> (\<lambda>x. Var (tl x)) }\<^sub>l\<^sub>s = C1" using empty by auto
  then have "C1{\<lambda>x. Var (''1''@x) }\<^sub>l\<^sub>s {\<lambda>x. Var (tl x) }\<^sub>l\<^sub>s = C1" using composition_conseq2ls by auto
  then have "C1 = (std1 C1) {\<lambda>x. Var (tl x) }\<^sub>l\<^sub>s" by auto
  then show "instance_ofls C1 (std1 C1)" unfolding instance_ofls_def by auto
qed

lemma std_apart_instance_ofls2': "instance_ofls C2 (std2 C2)"
proof -
  have empty: "(\<lambda>x. Var (''2''@x)) \<cdot> (\<lambda>x. Var (tl x)) = \<epsilon>" using composition_def by auto

  have "C2 {\<epsilon>}\<^sub>l\<^sub>s = C2" using empty_subls by auto
  then have "C2{(\<lambda>x. Var (''2''@x)) \<cdot> (\<lambda>x. Var (tl x)) }\<^sub>l\<^sub>s = C2" using empty by auto
  then have "C2{\<lambda>x. Var (''2''@x) }\<^sub>l\<^sub>s {\<lambda>x. Var (tl x) }\<^sub>l\<^sub>s = C2" using composition_conseq2ls by auto
  then have "C2 = (std2 C2) {\<lambda>x. Var (tl x) }\<^sub>l\<^sub>s" by auto
  then show "instance_ofls C2 (std2 C2)" unfolding instance_ofls_def by auto
qed

lemma std_apart_instance_ofls:
  assumes "std_apart C1 C2 = (C1', C2')"
  shows "instance_ofls C1 C1' \<and> instance_ofls C2 C2'"
proof -
  from assms have "C1' = C1{\<lambda>x. Var (''1''@x) }\<^sub>l\<^sub>s" unfolding std_apart_def by auto
  moreover
  from assms have "C2' = C2{\<lambda>x. Var (''2''@x) }\<^sub>l\<^sub>s" unfolding std_apart_def by auto
  ultimately
  show ?thesis using std_apart_instance_ofls1' std_apart_instance_ofls2' by auto
qed

lemma finite_std_apart: "finite C1 \<Longrightarrow> finite C2 \<Longrightarrow> std_apart C1 C2 = (C1', C2') \<Longrightarrow> finite C1' \<and> finite C2'"
  unfolding std_apart_def by auto

section {* Unifiers *}

definition unifiert :: "substitution \<Rightarrow> fterm set \<Rightarrow> bool" where
  "unifiert \<sigma> ts \<longleftrightarrow> (\<exists>t'. \<forall>t \<in> ts. t{\<sigma>}\<^sub>t = t')"
(* Alternative:
   \<^sub>1. Define unifier for a pair of formulas. Then extend this to a set by looking at all pairs of the set.
   \<^sub>2. The result is singleton  
 *)

definition unifierls :: "substitution \<Rightarrow> fterm literal set \<Rightarrow> bool" where
  "unifierls \<sigma> L \<longleftrightarrow> (\<exists>l'. \<forall>l \<in> L. l{\<sigma>}\<^sub>l = l')"

(* Not used anywhere 
lemma unifierls_same: "unifierls \<sigma> L \<Longrightarrow> l\<^sub>1  \<in> L  \<Longrightarrow> l\<^sub>2  \<in> L  \<Longrightarrow> l\<^sub>1 {\<sigma>}\<^sub>l = l\<^sub>2 {\<sigma>}\<^sub>l" 
  unfolding unifierls_def by auto
*)
lemma unif_sub:
  assumes unif: "unifierls \<sigma> L"
  assumes nonempty: "L \<noteq> {}"
  shows "\<exists>l. subls L \<sigma> = {subl l \<sigma>}"
proof -
  from nonempty obtain l where "l \<in> L" by auto
  from unif this have "L {\<sigma>}\<^sub>l\<^sub>s = {l {\<sigma>}\<^sub>l}" unfolding unifierls_def by auto
  then show ?thesis by auto
qed

lemma unifiert_def2: (* Pretty ugly lemma... (\<lambda>t. sub t \<sigma>) ` ts should have some {\<sigma>}\<^sub>x notation probably *)
  assumes L_elem: "ts \<noteq> {}"
  shows "unifiert \<sigma> ts \<longleftrightarrow> (\<exists>l. (\<lambda>t. sub t \<sigma>) ` ts ={l})"
proof
  assume unif: "unifiert \<sigma> ts"
  from L_elem obtain t where "t \<in> ts" by auto
  then have "(\<lambda>t. sub t \<sigma>) ` ts = {t {\<sigma>}\<^sub>t}" using unif unfolding unifiert_def by auto
  then show "\<exists>l. (\<lambda>t. sub t \<sigma>) ` ts = {l}" by auto
next
  assume "\<exists>l. (\<lambda>t. sub t \<sigma>) ` ts ={l}"
  then obtain l where "(\<lambda>t. sub t \<sigma>) ` ts = {l}" by auto
  then have "\<forall>l' \<in> ts. l'{\<sigma>}\<^sub>t = l" by auto
  then show "unifiert \<sigma> ts" unfolding unifiert_def by auto
qed

lemma unifierls_def2: 
  assumes L_elem: "L \<noteq> {}"
  shows "unifierls \<sigma> L \<longleftrightarrow> (\<exists>l. L {\<sigma>}\<^sub>l\<^sub>s ={l})"
proof
  assume unif: "unifierls \<sigma> L"
  from L_elem obtain l where "l \<in> L" by auto
  then have "L {\<sigma>}\<^sub>l\<^sub>s = {l {\<sigma>}\<^sub>l}" using unif unfolding unifierls_def by auto
  then show "\<exists>l. L{\<sigma>}\<^sub>l\<^sub>s = {l}" by auto
next
  assume "\<exists>l. L {\<sigma>}\<^sub>l\<^sub>s ={l}"
  then obtain l where "L {\<sigma>}\<^sub>l\<^sub>s = {l}" by auto
  then have "\<forall>l' \<in> L. l'{\<sigma>}\<^sub>l = l" by auto
  then show "unifierls \<sigma> L" unfolding unifierls_def by auto
qed
(* I Could use this lemma for great effect in the Combining soundness proof *)

lemma groundls_unif_singleton:
  assumes groundls: "groundls L" 
  assumes unif: "unifierls \<sigma>' L"
  assumes empt: "L \<noteq> {}"
  shows "\<exists>l. L = {l}"
proof -
  from unif empt have "\<exists>l. L {\<sigma>'}\<^sub>l\<^sub>s = {l}" using unif_sub by auto
  then show ?thesis using groundls_subls groundls by auto
qed

definition unifiablet :: "fterm set \<Rightarrow> bool" where
  "unifiablet fs \<longleftrightarrow> (\<exists>\<sigma>. unifiert \<sigma> fs)"

definition unifiablels :: "fterm literal set \<Rightarrow> bool" where
  "unifiablels L \<longleftrightarrow> (\<exists>\<sigma>. unifierls \<sigma> L)"

lemma unifier_comp[simp]: "unifierls \<sigma> (L\<^sup>C) \<longleftrightarrow> unifierls \<sigma> L"
proof
  assume "unifierls \<sigma> (L\<^sup>C)" 
  then obtain l'' where l''_p: "\<forall>l \<in> L\<^sup>C. l{\<sigma>}\<^sub>l = l''" 
    unfolding unifierls_def by auto
  obtain l' where "(l')\<^sup>c = l''" using comp_exi2[of l''] by auto
  from this l''_p have l'_p:"\<forall>l \<in> L\<^sup>C. l{\<sigma>}\<^sub>l = (l')\<^sup>c" by auto
  have "\<forall>l \<in> L. l{\<sigma>}\<^sub>l = l'"
    proof
      fix l
      assume "l\<in>L"
      then have "l\<^sup>c \<in> L\<^sup>C" by auto
      then have "(l\<^sup>c){\<sigma>}\<^sub>l = (l')\<^sup>c" using l'_p by auto
      then have "(l {\<sigma>}\<^sub>l)\<^sup>c = (l')\<^sup>c" by (cases l) auto
      then show "l{\<sigma>}\<^sub>l = l'" using cancel_comp2 by blast
    qed
  then show "unifierls \<sigma> L" unfolding unifierls_def by auto
next
  assume "unifierls \<sigma> L"
  then obtain l' where l'_p: "\<forall>l \<in> L. l{\<sigma>}\<^sub>l = l'" unfolding unifierls_def by auto
  have "\<forall>l \<in> L\<^sup>C. l{\<sigma>}\<^sub>l = (l')\<^sup>c"
    proof
      fix l
      assume "l \<in> L\<^sup>C"
      then have "l\<^sup>c \<in> L" using cancel_comp1 by (metis image_iff)
      then show "l{\<sigma>}\<^sub>l = (l')\<^sup>c" using l'_p comp_sub cancel_comp1 by metis
    qed
  then show "unifierls \<sigma> (L\<^sup>C)" unfolding unifierls_def by auto
qed

lemma unifier_sub1: "unifierls \<sigma> L \<Longrightarrow> L' \<subseteq> L \<Longrightarrow> unifierls \<sigma> L' " 
  unfolding unifierls_def by auto

lemma unifier_sub2: 
  assumes asm: "unifierls \<sigma> (L\<^sub>1 \<union> L\<^sub>2)"
  shows "unifierls \<sigma> L\<^sub>1 \<and> unifierls \<sigma> L\<^sub>2 "
proof -
  have "L\<^sub>1 \<subseteq> (L\<^sub>1 \<union> L\<^sub>2) \<and> L\<^sub>2 \<subseteq> (L\<^sub>1 \<union> L\<^sub>2)" by simp
  from this asm show ?thesis using unifier_sub1 by auto
qed

subsection {* Most General Unifiers *}

definition mgut :: "substitution \<Rightarrow> fterm set \<Rightarrow> bool" where
  "mgut \<sigma> fs \<longleftrightarrow> unifiert \<sigma> fs \<and> (\<forall>u. unifiert u fs \<longrightarrow> (\<exists>i. u = \<sigma> \<cdot> i))"

definition mguls :: "substitution \<Rightarrow> fterm literal set \<Rightarrow> bool" where
  "mguls \<sigma> L \<longleftrightarrow> unifierls \<sigma> L \<and> (\<forall>u. unifierls u L \<longrightarrow> (\<exists>i. u = \<sigma> \<cdot> i))"

section {* Resolution *}

definition applicable :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> bool" where
  "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<longleftrightarrow> 
       C\<^sub>1 \<noteq> {} \<and> C\<^sub>2 \<noteq> {} \<and> L\<^sub>1 \<noteq> {} \<and> L\<^sub>2 \<noteq> {}
     \<and> varsls C\<^sub>1 \<inter> varsls C\<^sub>2 = {} 
     \<and> L\<^sub>1 \<subseteq> C\<^sub>1 \<and> L\<^sub>2 \<subseteq> C\<^sub>2 
     \<and> mguls \<sigma> (L\<^sub>1 \<union> L\<^sub>2\<^sup>C)"

definition mresolution :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> fterm clause" where
  "mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = (C\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s - L\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s) \<union> (C\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s - L\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s)"

definition resolution :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> fterm clause" where
  "resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = ((C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2)) {\<sigma>}\<^sub>l\<^sub>s"

inductive mresolution_step :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  mresolution_rule: 
    "C\<^sub>1 \<in> Cs \<Longrightarrow> C\<^sub>2 \<in> Cs \<Longrightarrow> applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<Longrightarrow> 
       mresolution_step Cs (Cs \<union> {mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>})"
| standardize_apart:
    "C \<in> Cs \<Longrightarrow> var_renaming_of C C' \<Longrightarrow> mresolution_step Cs (Cs \<union> {C'})"

inductive resolution_step :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  resolution_rule: 
    "C\<^sub>1 \<in> Cs \<Longrightarrow> C\<^sub>2 \<in> Cs \<Longrightarrow> applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<Longrightarrow> 
       resolution_step Cs (Cs \<union> {resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>})"
| lstandardize_apart: (* Maybe rename would be a better name? ? ? *)
    "C \<in> Cs \<Longrightarrow> var_renaming_of C C' \<Longrightarrow> resolution_step Cs (Cs \<union> {C'})"

definition mresolution_deriv :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "mresolution_deriv = star mresolution_step"

definition resolution_deriv :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "resolution_deriv = star resolution_step"

(* Very nice lemma, but it is not used. 
  Could be used in a Completeness proof *)
lemma ground_mresolution:
  assumes ground: "groundls C\<^sub>1 \<and> groundls C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = (C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2) \<and> (\<exists>l. L\<^sub>1 = {l} \<and> L\<^sub>2 = {l}\<^sup>C)"
proof -
  from appl ground have groundl: "groundls L\<^sub>1 \<and> groundls L\<^sub>2" unfolding applicable_def by auto
  from this ground appl have resl: "(C\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s - L\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s) \<union> (C\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s - L\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s) = (C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2)" 
    using groundls_subls unfolding applicable_def by auto

  from ground appl have l\<^sub>1'l\<^sub>2'ground: "groundls L\<^sub>1 \<and> groundls L\<^sub>2" 
    unfolding applicable_def by auto
  then have "groundls (L\<^sub>1 \<union> L\<^sub>2\<^sup>C)" using ground_compls by auto
  moreover
  from appl have "unifierls \<sigma> (L\<^sub>1 \<union> L\<^sub>2\<^sup>C)" unfolding mguls_def applicable_def by auto
  ultimately
  obtain l where "L\<^sub>1 \<union> L\<^sub>2\<^sup>C = {l}" 
    using appl groundls_unif_singleton 
    unfolding applicable_def by (metis sup_eq_bot_iff)
  from appl this have "L\<^sub>1 = {l} \<and> L\<^sub>2\<^sup>C = {l}" unfolding applicable_def by (metis image_is_empty singleton_Un_iff) 
  then have l_p: "L\<^sub>1 = {l} \<and> L\<^sub>2 = {l}\<^sup>C" using cancel_compls1[of L\<^sub>2] by auto

  from resl l_p show ?thesis unfolding mresolution_def by auto
qed

(* Very nice lemma, but it is not used. 
  Could be used in a Completeness proof *)
lemma ground_mresolution_ground: 
  assumes asm: "groundls C\<^sub>1 \<and> groundls C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "groundls (mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
proof -
  from asm appl have "mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = (C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2)" using ground_mresolution by auto
  then show ?thesis using asm by auto
qed

section {* Soundness *}
(* Proving instantiation sound *)

fun evalsub :: "'u fun_denot \<Rightarrow> 'u var_denot \<Rightarrow> substitution \<Rightarrow> 'u var_denot" where
  "evalsub F E \<sigma> = (evalt E F) \<circ> \<sigma>"

lemma substitutiont: "evalt E F (t {\<sigma>}\<^sub>t) = evalt (evalsub F E \<sigma>) F t"
apply (induction t)
apply auto
apply (metis (mono_tags, lifting) comp_apply map_cong)
done

lemma substitutionts: "evalts E F (ts {\<sigma>}\<^sub>t\<^sub>s) = evalts (evalsub F E \<sigma>) F ts"
using substitutiont by auto

lemma substitutionl: "evall E F G (l {\<sigma>}\<^sub>l) \<longleftrightarrow> evall (evalsub F E \<sigma>) F G l"
apply (induction l) 
using substitutionts apply (metis evall.simps(1) subl.simps(1)) 
using substitutionts apply (metis evall.simps(2) subl.simps(2))
done

lemma subst_sound:
 assumes asm: "evalc F G C"
 shows "evalc F G (C {\<sigma>}\<^sub>l\<^sub>s)"
proof - 
 have "\<forall>E. \<exists>l \<in> C {\<sigma>}\<^sub>l\<^sub>s. evall E F G l"
  proof
   fix E
   from asm have "\<forall>E. \<exists>l \<in> C. evall E F G l" unfolding evalc_def by auto
   then have "\<exists>l \<in> C. evall (evalsub F E \<sigma>) F G l" by auto
   then show "\<exists>l \<in> C {\<sigma>}\<^sub>l\<^sub>s. evall E F G l" using substitutionl by blast
  qed
 then show "evalc F G (C {\<sigma>}\<^sub>l\<^sub>s)" unfolding evalc_def by auto
qed

lemma simple_resolution_sound:
  assumes C\<^sub>1sat:  "evalc F G C\<^sub>1"
  assumes C\<^sub>2sat:  "evalc F G C\<^sub>2"
  assumes l\<^sub>1inc\<^sub>1: "l\<^sub>1 \<in> C\<^sub>1"
  assumes l\<^sub>2inc\<^sub>2: "l\<^sub>2 \<in> C\<^sub>2"
  assumes comp: "l\<^sub>1\<^sup>c = l\<^sub>2"
  shows "evalc F G ((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))"
proof -
  have "\<forall>E. \<exists>l \<in> (((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))). evall E F G l"
    proof
      fix E
      have "evall E F G l\<^sub>1 \<or> evall E F G l\<^sub>2" using comp by (cases l\<^sub>1) auto
      then show "\<exists>l \<in> (((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))). evall E F G l"
        proof
          assume "evall E F G l\<^sub>1"
          then have "\<not>evall E F G l\<^sub>2" using comp by (cases l\<^sub>1) auto
          then have "\<exists>l\<^sub>2'\<in> C\<^sub>2. l\<^sub>2' \<noteq> l\<^sub>2 \<and> evall E F G l\<^sub>2'" using l\<^sub>2inc\<^sub>2 C\<^sub>2sat unfolding evalc_def by auto
          then show "\<exists>l\<in>(C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}). evall E F G l" by auto
        next
          assume "evall E F G l\<^sub>2" (* Symmetric *)
          then have "\<not>evall E F G l\<^sub>1" using comp by (cases l\<^sub>1) auto
          then have "\<exists>l\<^sub>1'\<in> C\<^sub>1. l\<^sub>1' \<noteq> l\<^sub>1 \<and> evall E F G l\<^sub>1'" using l\<^sub>1inc\<^sub>1 C\<^sub>1sat unfolding evalc_def by auto
          then show "\<exists>l\<in>(C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}). evall E F G l" by auto
        qed
    qed
  then show ?thesis unfolding evalc_def by simp
qed

lemma mresolution_sound:
  assumes sat\<^sub>1: "evalc F G C\<^sub>1"
  assumes sat\<^sub>2: "evalc F G C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "evalc F G (mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
proof -
  from sat\<^sub>1 have sat\<^sub>1\<sigma>: "evalc F G (C\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s)" using subst_sound by blast
  from sat\<^sub>2 have sat\<^sub>2\<sigma>: "evalc F G (C\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s)" using subst_sound by blast

  from appl obtain l\<^sub>1 where l\<^sub>1_p: "l\<^sub>1 \<in> L\<^sub>1" unfolding applicable_def by auto

  from l\<^sub>1_p appl have "l\<^sub>1 \<in> C\<^sub>1" unfolding applicable_def by auto
  then have inc\<^sub>1\<sigma>: "l\<^sub>1 {\<sigma>}\<^sub>l \<in> C\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s" by auto
  
  from l\<^sub>1_p have unified\<^sub>1: "l\<^sub>1 \<in> (L\<^sub>1 \<union> (L\<^sub>2\<^sup>C))" by auto

  from l\<^sub>1_p appl have l\<^sub>1\<sigma>isl\<^sub>1\<sigma>: "{l\<^sub>1{\<sigma>}\<^sub>l} = L\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s"  
    unfolding mguls_def unifierls_def applicable_def by auto

  from appl obtain l\<^sub>2 where l\<^sub>2_p: "l\<^sub>2 \<in> L\<^sub>2" unfolding applicable_def by auto
  
  from l\<^sub>2_p appl have "l\<^sub>2 \<in> C\<^sub>2" unfolding applicable_def by auto
  then have inc\<^sub>2\<sigma>: "l\<^sub>2 {\<sigma>}\<^sub>l \<in> C\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s" by auto

  from l\<^sub>2_p have unified\<^sub>2: "l\<^sub>2\<^sup>c \<in> (L\<^sub>1 \<union> (L\<^sub>2\<^sup>C))" by auto

  from unified\<^sub>1 unified\<^sub>2 appl have "l\<^sub>1 {\<sigma>}\<^sub>l = (l\<^sub>2\<^sup>c){\<sigma>}\<^sub>l" 
    unfolding mguls_def unifierls_def applicable_def by auto
  then have comp: "(l\<^sub>1 {\<sigma>}\<^sub>l)\<^sup>c = l\<^sub>2 {\<sigma>}\<^sub>l" using comp_sub comp_swap by auto (* These steps could be lemmas *)

  from appl have "unifierls \<sigma> (L\<^sub>2\<^sup>C)" 
    using unifier_sub2 unfolding mguls_def applicable_def by blast
  then have "unifierls \<sigma> L\<^sub>2" by auto
  from this l\<^sub>2_p have l\<^sub>2\<sigma>isl\<^sub>2\<sigma>: "{l\<^sub>2{\<sigma>}\<^sub>l} = L\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s" unfolding unifierls_def by auto

  from sat\<^sub>1\<sigma> sat\<^sub>2\<sigma> inc\<^sub>1\<sigma> inc\<^sub>2\<sigma> comp have "evalc F G (C\<^sub>1{\<sigma>}\<^sub>l\<^sub>s - {l\<^sub>1{\<sigma>}\<^sub>l} \<union> (C\<^sub>2{\<sigma>}\<^sub>l\<^sub>s - {l\<^sub>2{\<sigma>}\<^sub>l}))" using simple_resolution_sound[of F G "C\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s" "C\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s" "l\<^sub>1 {\<sigma>}\<^sub>l" " l\<^sub>2 {\<sigma>}\<^sub>l"]
    by auto
  from this l\<^sub>1\<sigma>isl\<^sub>1\<sigma> l\<^sub>2\<sigma>isl\<^sub>2\<sigma> show ?thesis unfolding mresolution_def by auto
qed

lemma resolution_superset: "mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<subseteq> resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
 unfolding mresolution_def resolution_def by auto

lemma superset_sound:
  assumes sup: "C \<subseteq> C'"
  assumes sat: "evalc F G C"
  shows "evalc F G C'"
proof -
  have "\<forall>E. \<exists>l \<in> C'. evall E F G l"
    proof
      fix E
      from sat have "\<forall>E. \<exists>l \<in> C. evall E F G l" unfolding evalc_def by -
      then have "\<exists>l \<in> C . evall E F G l" by auto
      then show "\<exists>l \<in> C'. evall E F G l" using sup by auto
    qed
  then show "evalc F G C'" unfolding evalc_def by auto
qed
 

lemma resolution_sound:
  assumes sat\<^sub>1: "evalc F G C\<^sub>1"
  assumes sat\<^sub>2: "evalc F G C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "evalc F G (resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
proof -
  from sat\<^sub>1 sat\<^sub>2 appl have "evalc F G (mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)" using mresolution_sound by blast
  then show ?thesis using superset_sound resolution_superset by metis
qed

lemma sound_step: "mresolution_step Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'"
proof (induction rule: mresolution_step.induct)
  case (mresolution_rule C\<^sub>1 Cs C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)
  then have "evalc F G C\<^sub>1 \<and> evalc F G C\<^sub>2" unfolding evalcs_def by auto
  then have "evalc F G (mresolution C\<^sub>1 C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)" 
    using mresolution_sound mresolution_rule by auto
  then show ?case using mresolution_rule unfolding evalcs_def by auto
next
  case (standardize_apart C Cs C')
  then have "evalc F G C" unfolding evalcs_def by auto
  then have "evalc F G C'" using subst_sound standardize_apart unfolding var_renaming_of_def instance_ofls_def by metis
  then show ?case using standardize_apart unfolding evalcs_def by auto
qed

lemma lsound_step: "resolution_step Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'"
proof (induction rule: resolution_step.induct)
  case (resolution_rule C\<^sub>1 Cs C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)
  then have "evalc F G C\<^sub>1 \<and> evalc F G C\<^sub>2" unfolding evalcs_def by auto
  then have "evalc F G (resolution C\<^sub>1 C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)" 
    using resolution_sound resolution_rule by auto
  then show ?case using resolution_rule unfolding evalcs_def by auto
next
  case (lstandardize_apart C Cs C')
  then have "evalc F G C" unfolding evalcs_def by auto
  then have "evalc F G C'" using subst_sound lstandardize_apart unfolding var_renaming_of_def instance_ofls_def by metis
  then show ?case using lstandardize_apart unfolding evalcs_def by auto
qed

lemma sound_derivation: 
  "mresolution_deriv Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'" 
unfolding mresolution_deriv_def
proof (induction rule: star.induct)
  case refl then show ?case by auto
next
  case (step Cs\<^sub>1 Cs\<^sub>2 Cs\<^sub>3) then show ?case using sound_step by auto
qed

lemma lsound_derivation: 
  "resolution_deriv Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'" 
unfolding resolution_deriv_def
proof (induction rule: star.induct)
  case refl then show ?case by auto
next
  case (step Cs\<^sub>1 Cs\<^sub>2 Cs\<^sub>3) then show ?case using lsound_step by auto
qed

section {* Enumerations *}

fun hlit_of_flit :: "fterm literal \<Rightarrow> hterm literal" where (*  Already defined in terms and literals*)
  "hlit_of_flit (Pos P ts) = Pos P (hterms_of_fterms ts)"
| "hlit_of_flit (Neg P ts) = Neg P (hterms_of_fterms ts)"

lemma ground_h_undiag: "groundl l \<Longrightarrow> nat_from_hatom (hlit_of_flit l) = nat_from_fatom l"
proof (induction l) (* Not really induction *)
  case (Pos P ts) 
  then show ?case unfolding nat_from_fatom_def by auto
next
  case (Neg P ts) 
  then show ?case using undiag_neg undiag_neg2 unfolding nat_from_fatom_def by auto
qed


section {* Herbrand Interpretations *}

(* HFun is the Herbrand function denotation in which terms are mapped to themselves  *)
term HFun

lemma hterms_ground: "ground (fterm_of_hterm t)" "grounds (fterms_of_hterms ts)"
apply (induction t and ts rule: fterm_of_hterm.induct fterms_of_hterms.induct)
apply auto
done

lemma hatom_ground: "groundl (fatom_of_hatom l)"
apply (induction l)
using hterms_ground apply auto
done

lemma diag_ground: "groundl (fatom_from_nat n)" unfolding fatom_from_nat_def using hatom_ground by auto 

lemma eval_ground: "ground t \<Longrightarrow> (evalt E HFun t) = hterm_of_fterm t" "grounds ts \<Longrightarrow> (evalts E HFun ts) = hterms_of_fterms ts"
apply (induction t and ts rule: hterm_of_fterm.induct hterms_of_fterms.induct)
apply auto
done

lemma evall_grounds:
  assumes asm: "grounds ts"
  shows "evall E HFun G (Pos P ts) \<longleftrightarrow> G P (hterms_of_fterms ts)"
proof -
  have "evall E HFun G (Pos P ts) = G P (evalts E HFun ts)" by auto
  also have "... = G P (hterms_of_fterms ts)" using asm eval_ground by metis
  finally show ?thesis by auto
qed

section {* Partial Interpretations *}

type_synonym partial_pred_denot = "bool list"

(* This definition is quite syntactical. I think that's good though.
   Alternative: Check if an instance is in list. If not return true.
   Otherwise, build an interpretation from the partial interpretation *)

(* Only ground literals can be falsified *)
fun falsifiesl :: "partial_pred_denot \<Rightarrow> fterm literal \<Rightarrow> bool" where
  "falsifiesl G (Pos p ts) = 
     (\<exists>i.  
      i < length G
      \<and> G ! i = False
      \<and> fatom_from_nat i = Pos p ts)" (* I could get rid of the existential quantifier by using nat_from_fatom, but then I should make sure l is ground *)
| "falsifiesl G (Neg p ts) = 
     (\<exists>i.  
      i < length G
      \<and> G ! i = True
      \<and> fatom_from_nat i = Pos p ts)"

abbreviation falsifiesg :: "partial_pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "falsifiesg G C \<equiv> (\<forall>l \<in> C. falsifiesl G l)"

abbreviation falsifiesc :: "partial_pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "falsifiesc G C \<equiv> (\<exists>C'. instance_ofls C' C \<and> falsifiesg G C')"

abbreviation falsifiescs :: "partial_pred_denot \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "falsifiescs G Cs \<equiv> (\<exists>C \<in> Cs. falsifiesc G C)"

lemma falsifies_ground:
  assumes "falsifiesl G l"
  shows "groundl l"
proof (cases l)
  case (Pos p ts) 
  then have "\<exists>i. fatom_from_nat i = Pos p ts" using assms by auto
  then show ?thesis using diag_ground Pos by metis
next
  case (Neg p ts) 
  then have "\<exists>i. fatom_from_nat i = Pos p ts" using assms by auto
  then have "groundl (Pos p ts)" using diag_ground Neg by metis
  then show ?thesis using Neg by auto
qed 

lemma falsifies_ground_sub: (* This lemma seems quite pointless *)
  assumes "falsifiesl G l"
  shows "falsifiesl G (l{\<sigma>}\<^sub>l) \<and> groundl (l{\<sigma>}\<^sub>l)"
proof -
  from assms have "falsifiesl G (l) \<and> groundl (l)" using falsifies_ground by auto
  then show ?thesis using groundl_subs by auto
qed

lemma falsifiesc_ground:
  assumes "falsifiesc G C"
  shows "\<exists>C'. instance_ofls C' C \<and> falsifiesg G C' \<and> groundls C'"
proof -
  from assms obtain C' where C'_p: "instance_ofls C' C \<and> falsifiesg G C'" by auto
  then have "\<forall>l \<in> C'. falsifiesl G l" by auto
  then have "\<forall>l \<in> C'. groundl l" using falsifies_ground by auto
  then have "groundls C'" by auto
  then show ?thesis using C'_p by auto
qed
  
lemma ground_falsifiesc: (* Very pointless lemma *)
  assumes "groundls C" (* this assumption is not even used *)
  assumes "falsifiesg G C"
  shows "\<forall>l\<in>C. falsifiesl G l" using local.assms(2) by -  

lemma ground_falsifies:
  assumes "groundl l"
  assumes "falsifiesl G l"
  shows"
      \<exists>i.  
      i < length G
      \<and> G ! i = (\<not>sign l)
      \<and> fatom_from_nat i = Pos (get_pred l) (get_terms l)"
using assms by (cases l) auto (* Not really induction *)


abbreviation extend :: "(nat \<Rightarrow> partial_pred_denot) \<Rightarrow> hterm pred_denot" where
  "extend f P ts \<equiv> (
     let n = nat_from_hatom (Pos P ts) in
       f (Suc n) ! n
     )"

fun sub_of_denot :: "hterm var_denot \<Rightarrow> substitution" where
  "sub_of_denot E = fterm_of_hterm \<circ> E"

lemma ground_sub_of_denott: "ground ((t :: fterm) {sub_of_denot E}\<^sub>t)" 
apply (induction t)
apply (auto simp add: hterms_ground)
done

lemma ground_sub_of_denotts: "grounds ((ts :: fterm list) {sub_of_denot E}\<^sub>t\<^sub>s)"
apply auto
using ground_sub_of_denott apply simp 
done

lemma ground_sub_of_denotl: "groundl ((l :: fterm literal) {sub_of_denot E}\<^sub>l)"
proof -
  have "grounds (subs (get_terms l :: fterm list) (sub_of_denot E))" 
    using ground_sub_of_denotts by auto
  then show ?thesis by (cases l)  auto
qed

lemma sub_of_denot_equivx: "evalt E HFun (sub_of_denot E x) = E x"
proof -
  have "ground (sub_of_denot E x)" using hterms_ground by auto
  then
  have "evalt E HFun (sub_of_denot E x) = hterm_of_fterm (sub_of_denot E x)"
    using eval_ground(1) by auto
  also have "... = hterm_of_fterm (fterm_of_hterm (E x))" by auto
  also have "... = E x" by auto
  finally show ?thesis by auto
qed

lemma sub_of_denot_equivt:
    "evalt E HFun (t {sub_of_denot E}\<^sub>t) = evalt E HFun t"
apply (induction t)
using sub_of_denot_equivx apply auto
done

lemma sub_of_denot_equivts: "evalts E HFun (ts {sub_of_denot E}\<^sub>t\<^sub>s) = evalts E HFun ts"
using sub_of_denot_equivt apply simp
done

lemma sub_of_denot_equivl: "evall E HFun G (l {sub_of_denot E}\<^sub>l) \<longleftrightarrow> evall E HFun G l"
proof (induction l)
  case (Pos p ts)
  have "evall E HFun G ((Pos p ts) {sub_of_denot E}\<^sub>l) \<longleftrightarrow> G p (evalts E HFun (ts {sub_of_denot E}\<^sub>t\<^sub>s))" by auto
  also have " ... \<longleftrightarrow> G p (evalts E HFun ts)" using sub_of_denot_equivts[of E ts] by metis
  also have " ... \<longleftrightarrow> evall E HFun G (Pos p ts)" by simp
  finally
  show ?case by blast
next
 case (Neg p ts)
  have "evall E HFun G ((Neg p ts) {sub_of_denot E}\<^sub>l) \<longleftrightarrow> \<not>G p (evalts E HFun (ts {sub_of_denot E}\<^sub>t\<^sub>s))" by auto
  also have " ... \<longleftrightarrow> \<not>G p (evalts E HFun ts)" using sub_of_denot_equivts[of E ts] by metis
  also have " ... = evall E HFun G (Neg p ts)" by simp
  finally
  show ?case by blast
qed

(* Under an Herbrand interpretation, an environment is equivalent to a substitution
   Why have this conjunction of two lemmas?
*)
lemma sub_of_denot_equiv_ground': 
  "evall E HFun G l = evall E HFun G (l {sub_of_denot E}\<^sub>l) \<and> groundl (l {sub_of_denot E}\<^sub>l)"
    using sub_of_denot_equivl ground_sub_of_denotl by auto

(* Under an Herbrand interpretation, an environment is "equivalent" to a substitution - also for partial interpretations *)
lemma partial_equiv_subst:
  assumes "falsifiesc G (C {\<tau>}\<^sub>l\<^sub>s)"
  shows "falsifiesc G C"
proof -
  from assms obtain C' where C'_p: "instance_ofls C' (C {\<tau>}\<^sub>l\<^sub>s) \<and> falsifiesg G C'" by auto
  then have "instance_ofls (C {\<tau>}\<^sub>l\<^sub>s) C" unfolding instance_ofls_def by auto
  then have "instance_ofls C' C" using C'_p instance_ofls_trans by auto
  then show ?thesis using C'_p by auto
qed

(* Under an Herbrand interpretation, an environment is equivalent to a substitution*)
lemma sub_of_denot_equiv_ground:
  "((\<exists>l \<in> C. evall E HFun G l) \<longleftrightarrow> (\<exists>l \<in> C {sub_of_denot E}\<^sub>l\<^sub>s. evall E HFun G l))
           \<and> groundls (C {sub_of_denot E}\<^sub>l\<^sub>s)"
  using sub_of_denot_equiv_ground' by auto

lemma std_apart_falsifies1': "falsifiesc G C1 \<longleftrightarrow> falsifiesc G (std1 C1)"
proof 
  assume asm: "falsifiesc G C1"
  then obtain Cg where "instance_ofls Cg C1  \<and> falsifiesg G Cg" by auto
  moreover
  then have "instance_ofls Cg (std1 C1)" using std_apart_instance_ofls1' instance_ofls_trans asm by blast
  ultimately
  show "falsifiesc G (std1 C1)" by auto
next
  assume asm: "falsifiesc G (std1 C1)"
  then have inst: "instance_ofls (std1 C1) C1" unfolding instance_ofls_def by auto

  from asm obtain Cg where "instance_ofls Cg (std1 C1)  \<and> falsifiesg G Cg" by auto
  moreover
  then have "instance_ofls Cg C1" using inst instance_ofls_trans assms by blast
  ultimately
  show "falsifiesc G C1" by auto
qed

lemma std_apart_falsifies1:
  assumes "std_apart C1 C2 = (C1',C2')"
  assumes "falsifiesc G C1"
  shows "falsifiesc G C1'"
proof -
  from assms have "C1' = std1 C1" unfolding std_apart_def by auto
  then show ?thesis using assms std_apart_falsifies1' by auto
qed

lemma std_apart_falsifies1_sym:
  assumes "std_apart C1 C2 = (C1',C2')"
  assumes "falsifiesc G C1'"
  shows "falsifiesc G C1"
proof -
  from assms have "C1' = std1 C1" unfolding std_apart_def by auto
  then show ?thesis using assms std_apart_falsifies1' by auto
qed

lemma std_apart_falsifies2': "falsifiesc G C2 \<longleftrightarrow> falsifiesc G (std2 C2)"
proof 
  assume asm: "falsifiesc G C2"
  then obtain Cg where "instance_ofls Cg C2  \<and> falsifiesg G Cg" by auto
  moreover
  then have "instance_ofls Cg (std2 C2)" using std_apart_instance_ofls2' instance_ofls_trans asm by blast
  ultimately
  show "falsifiesc G (std2 C2)" by auto
next
  assume asm: "falsifiesc G (std2 C2)"
  then have inst: "instance_ofls (std2 C2) C2" unfolding instance_ofls_def by auto

  from asm obtain Cg where "instance_ofls Cg (std2 C2)  \<and> falsifiesg G Cg" by auto
  moreover
  then have "instance_ofls Cg C2" using inst instance_ofls_trans assms by blast
  ultimately
  show "falsifiesc G C2" by auto
qed

lemma std_apart_falsifies2:
  assumes "std_apart C1 C2 = (C1',C2')"
  assumes "falsifiesc G C2"
  shows "falsifiesc G C2'"
proof -
  from assms have "C2' = std2 C2" unfolding std_apart_def by auto
  then show ?thesis using assms std_apart_falsifies2' by auto
qed

lemma std_apart_falsifies2_sym:
  assumes "std_apart C1 C2 = (C1',C2')"
  assumes "falsifiesc G C2'"
  shows "falsifiesc G C2"
proof -
  from assms have "C2' = std2 C2" unfolding std_apart_def by auto
  then show ?thesis using assms std_apart_falsifies2' by auto
qed

lemma std_apart_renames1': "var_renaming_of C1 (std1 C1)"
proof -
  have "instance_ofls C1 (std1 C1)" using std_apart_instance_ofls1' assms by auto
  moreover have "instance_ofls (std1 C1) C1" using assms unfolding instance_ofls_def std_apart_def by auto
  ultimately show "var_renaming_of C1 (std1 C1)" unfolding var_renaming_of_def by auto
qed

lemma std_apart_renames1:
  assumes "std_apart C1 C2 = (C1',C2')"
  shows "var_renaming_of C1 C1'"
proof -
  from assms have "C1' = C1{\<lambda>x. Var (''1''@x) }\<^sub>l\<^sub>s" unfolding std_apart_def by auto
  then show ?thesis using std_apart_renames1' by auto
qed

lemma std_apart_renames2': "var_renaming_of C2 (std2 C2)"
proof -
  have "instance_ofls C2 (std2 C2)" using std_apart_instance_ofls2' assms by auto
  moreover have "instance_ofls (std2 C2) C2" using assms unfolding instance_ofls_def std_apart_def by auto
  ultimately show "var_renaming_of C2 (std2 C2)" unfolding var_renaming_of_def by auto
qed

lemma std_apart_renames2:
  assumes "std_apart C1 C2 = (C1',C2')"
  shows "var_renaming_of C2 C2'"
proof -
  from assms have "C2' = C2{\<lambda>x. Var (''2''@x) }\<^sub>l\<^sub>s" unfolding std_apart_def by auto
  then show ?thesis using std_apart_renames2' by auto
qed


subsection {* Semantic Trees *}

abbreviation closed_branch :: "partial_pred_denot \<Rightarrow> tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "closed_branch G T Cs \<equiv> branch G T \<and> falsifiescs G Cs"

abbreviation(input) open_branch :: "partial_pred_denot \<Rightarrow> tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "open_branch G T Cs \<equiv> branch G T \<and> \<not>falsifiescs G Cs"

fun closed_tree :: "tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "closed_tree T Cs \<longleftrightarrow> anybranch T (\<lambda>b. closed_branch b T Cs) 
                  \<and> anyinternal T (\<lambda>p. \<not>falsifiescs p Cs)" (* Maybe change from fun to abbreviation of definition *)


section {* Herbrand's Theorem *}

lemma maximum:
  assumes asm: "finite C"
  shows "\<exists>n :: nat. \<forall>l \<in> C. f l \<le> n"
proof
  from asm show "\<forall>l\<in>C. f l \<le> (Max (f ` C))" by auto
qed

lemma extend_preserves_model: (* only for ground *)
  assumes f_chain: "list_chain (f :: nat \<Rightarrow> partial_pred_denot)" 
  assumes C_ground: "groundls C"
  assumes C_sat: "~falsifiesc (f (Suc n)) C" (* probably - this should be falsifiesg now *)
  assumes n_max: "\<forall>l\<in>C. nat_from_fatom l \<le> n"
  shows "evalc HFun (extend f) C"
proof -
  let ?F = "HFun" 
  let ?G = "extend f"
  {
    fix E
    from C_sat have "\<forall>C'. (~instance_ofls C' C \<or> ~ falsifiesg (f (Suc n)) C')" by auto
    then have "~falsifiesg (f (Suc n)) C" using instance_ofls_self by auto
    then obtain l where l_p: "l\<in>C \<and> ~falsifiesl (f (Suc n)) l" by auto
    let ?i = "nat_from_fatom l"
     
    from l_p have i_n: "?i \<le> n" using n_max by auto
    then have j_n: "?i < length (f (Suc n))" using f_chain chain_length[of f] by auto
      
    have "evall E HFun (extend f) l"
      proof (cases l)
        case (Pos P ts)
        from Pos l_p C_ground have ts_ground: "grounds ts" by auto
        from Pos l_p C_ground have undiag_l: "nat_from_hatom (hlit_of_flit l) = ?i" using ground_h_undiag by blast

        have "~falsifiesl (f (Suc n)) l" using l_p by auto
        then have "f (Suc n) ! ?i = True" 
          using j_n Pos ts_ground empty_subts[of ts] by auto
        moreover have "f (Suc ?i) ! ?i = f (Suc n) ! ?i" 
          using f_chain i_n j_n chain_length[of f] ith_in_extension[of f] by simp
        ultimately
        have "f (Suc ?i) ! ?i = True" using Pos undiag_l by auto
        then have "?G P (hterms_of_fterms ts)" using Pos undiag_l by auto
        then show ?thesis using evall_grounds[of ts _ ?G P] ts_ground Pos by auto
      next
        case (Neg P ts) (* Symmetric *)
        from Neg l_p C_ground have ts_ground: "grounds ts" by auto
        from Neg l_p C_ground have undiag_l: "nat_from_hatom (hlit_of_flit l) = ?i" using ground_h_undiag by blast

        have "~falsifiesl (f (Suc n)) l" using l_p by auto  
        then have "f (Suc n) ! ?i = False" 
          using j_n Neg ts_ground empty_subts[of ts] undiag_neg by auto
        moreover have "f (Suc ?i) ! ?i = f (Suc n) ! ?i" 
          using f_chain i_n j_n chain_length[of f] ith_in_extension[of f] by simp
        ultimately
        have "f (Suc ?i) ! ?i = False" using Neg undiag_l by auto
        then have "~?G P (hterms_of_fterms ts)" using Neg undiag_l undiag_neg2 by simp 
        then show ?thesis using Neg evall_grounds[of ts _ ?G P] ts_ground by auto
      qed
    then have "\<exists>l \<in> C. evall E HFun (extend f) l" using l_p by auto
  }
  then have "evalc HFun (extend f) C" unfolding evalc_def by auto
  then show ?thesis using instance_ofls_self by auto
qed

lemma extend_preserves_model2: (* only for ground *)
  assumes f_chain: "list_chain (f :: nat \<Rightarrow> partial_pred_denot)" 
  assumes C_ground: "groundls C"
  assumes fin_c: "finite C"
  assumes model_C: "\<forall>n. \<not>falsifiesc (f n) C" (* probably - this should be falsifiesg now *)
  shows C_false: "evalc HFun (extend f) C"
proof -
  (* Since C is finite, C {sub_of_denot E}\<^sub>l\<^sub>s has a largest index of a literal.  *)
  obtain n where largest: "\<forall>l \<in> C. nat_from_fatom l \<le> n" using fin_c maximum by blast
  moreover
  then have "\<not>falsifiesc (f (Suc n)) C" using model_C by auto
  ultimately show ?thesis using model_C f_chain C_ground extend_preserves_model[of f C n ] by blast
qed

lemma list_chain_model': 
  assumes f_chain: "list_chain (f :: nat \<Rightarrow> partial_pred_denot)"
  assumes model_c: "\<forall>n. \<not>falsifiesc (f n) C"
  assumes fin_c: "finite C"
  shows "evalc HFun (extend f) C"
unfolding evalc_def proof 
  fix E
  let ?F = "HFun"
  let ?G = "extend f"
  let ?\<sigma> = "sub_of_denot E"
  
  (* Since C is finite, C {sub_of_denot E}\<^sub>l\<^sub>s has a largest index of a literal. *)
  from fin_c model_c have fin_c\<sigma>: "finite (C {sub_of_denot E}\<^sub>l\<^sub>s)" by auto
  have groundc\<sigma>: "groundls (C {sub_of_denot E}\<^sub>l\<^sub>s)" using sub_of_denot_equiv_ground by auto

  (* Here starts the proof *)
  (* We go from syntactic FO world to syntactic ground world: *)
  from model_c have "\<forall>n. \<not>falsifiesc (f n) (C {?\<sigma>}\<^sub>l\<^sub>s)" using partial_equiv_subst by blast
  (* Then from syntactic ground world to semantic ground world: *)
  then have "evalc HFun ?G (C {?\<sigma>}\<^sub>l\<^sub>s)" using groundc\<sigma> f_chain fin_c\<sigma>  extend_preserves_model2[of f "C {?\<sigma>}\<^sub>l\<^sub>s"] by blast
  (* Then from semantic ground world to semantic FO world: *)
  then have "\<forall>E. \<exists>l \<in> (C {?\<sigma>}\<^sub>l\<^sub>s). evall E ?F ?G l" unfolding evalc_def by auto
  then have "\<exists>l \<in> (C {?\<sigma>}\<^sub>l\<^sub>s). evall E ?F ?G l" by auto
  then show "\<exists>l \<in> C. evall E ?F ?G l" using sub_of_denot_equiv_ground[of C E "extend f"] by blast
qed

(* If we have a list-chain of partial models, then we have a model. *)
lemma list_chain_model:
  assumes f_chain: "list_chain (f :: nat \<Rightarrow> partial_pred_denot)"
  assumes model_cs: "\<forall>n. \<not>falsifiescs (f n) Cs" 
  assumes fin_cs: "finite Cs"
  assumes fin_c: "\<forall>C \<in> Cs. finite C"
  shows "evalcs HFun (extend f) Cs"
proof -
  let ?F = "HFun"
    
  have "\<forall>C \<in> Cs. evalc ?F (extend f) C"  
    proof (rule ballI) (* Maybe this proof should be a lemma *)
      fix C
      assume asm: "C \<in> Cs"
      then have "\<forall>n. \<not> falsifiesc (f n) C" using model_cs by auto
      then show "evalc ?F (extend f) C" using fin_c asm f_chain list_chain_model'[of f C] by auto
    qed                                                                      
  then show "evalcs ?F (extend f) Cs" unfolding evalcs_def by auto
qed

fun deeptree :: "nat \<Rightarrow> tree" where
  "deeptree 0 = Leaf"
| "deeptree (Suc n) = Branching (deeptree n) (deeptree n)"

thm extend_preserves_model
thm list_chain_model

lemma branch_length: "branch b (deeptree n) \<Longrightarrow> length b = n"
proof (induction n arbitrary: b)
  case 0 then show ?case using branch_inv_Leaf by auto
next
  case (Suc n)
  then have "branch b (Branching (deeptree n) (deeptree n))" by auto
  then obtain a b' where p: "b=a#b'\<and> branch b' (deeptree n)" using branch_inv_Branching[of b] by blast
  then have "length b' = n" using Suc by auto
  then show ?case using p by auto
qed

lemma infinity:
  assumes inj: "\<forall>n :: nat. undiago (diago n) = n" 
  assumes all_tree: "\<forall>n :: nat. (diago n) \<in> tree"
  shows "\<not>finite tree"
proof -
  from inj all_tree have "\<forall>n. n = undiago (diago n) \<and> (diago n) \<in> tree" by auto
  then have "\<forall>n. \<exists>ds. n = undiago ds \<and> ds \<in> tree" by auto
  then have "undiago ` tree = (UNIV :: nat set)" by auto
  then have "\<not>finite tree"by (metis finite_imageI infinite_UNIV_nat) 
  then show ?thesis by auto
qed

lemma longer_falsifiesl:
  "falsifiesl ds l \<Longrightarrow> falsifiesl (ds@d) l"
proof (induction l) (* Not really induction *)
  case (Pos P ts)
  then obtain i where i_p: "  
      i < length ds
      \<and> ds ! i = False
      \<and> fatom_from_nat i = Pos P ts" by auto
  moreover
  from i_p have "i < length (ds@d)" by auto
  moreover
  from i_p have "(ds@d) ! i = False" by (simp add: nth_append) 
  ultimately
  have "
      i < length (ds@d)
      \<and> (ds@d) ! i = False
      \<and> fatom_from_nat i = Pos P ts" by auto
  then show ?case by auto
next
  case (Neg P ts) (* very symmetrical *)
  then obtain i where i_p: "  
      i < length ds
      \<and> ds ! i = True
      \<and> fatom_from_nat i = Pos P ts" by auto
  moreover
  from i_p have "i < length (ds@d)" by auto
  moreover
  from i_p have "(ds@d) ! i = True" by (simp add: nth_append) 
  ultimately
  have " 
      i < length (ds@d)
      \<and> (ds@d) ! i = True
      \<and> fatom_from_nat i = Pos P ts" by auto
  then show ?case by auto
qed

lemma longer_falsifiesg:
  assumes "falsifiesg ds C"
  shows "falsifiesg (ds @ d) C"
proof
  fix l
  assume "l\<in>C"
  then show "falsifiesl (ds @ d) l" using assms longer_falsifiesl by auto
qed

lemma longer_falsifiesc:
  assumes "falsifiesc ds C"
  shows "falsifiesc (ds @ d) C"
proof -
  from assms obtain C' where "instance_ofls C' C \<and> falsifiesg ds C'" by auto
  moreover
  then have "falsifiesg (ds @ d) C'" using longer_falsifiesg by auto
  ultimately show ?thesis by auto
qed

(* We use this so that we can apply königs lemma *)
lemma longer_falsifies:  
  assumes "falsifiescs ds Cs"
  shows "falsifiescs (ds @ d) Cs"
proof -
  from assms obtain C where "C \<in> Cs \<and> falsifiesc ds C" by auto
  moreover
  then have "falsifiesc (ds @ d) C" using longer_falsifiesc[of C ds d] by blast
  ultimately
  show ?thesis by auto
qed

(* "If all finite semantic trees have an open branch, then the set of clauses has a model." *)
theorem herbrand':
  assumes openb: "\<forall>T. \<exists>G. open_branch G T Cs"
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  shows "\<exists>G. evalcs HFun G Cs"
proof -
  (* Show T infinite *)
  let ?tree = "{G. \<not>falsifiescs G Cs}"
  let ?undiag = length
  let ?diag = "(\<lambda>l. SOME b. open_branch b (deeptree l) Cs) :: nat \<Rightarrow> partial_pred_denot"

  from openb have diag_open: "\<forall>l. open_branch (?diag l) (deeptree l) Cs"
    using someI_ex[of "%b. open_branch b (deeptree _) Cs"] by auto
  then have "\<forall>n. ?undiag (?diag n) = n" using branch_length by auto
  moreover
  have "\<forall>n. (?diag n) \<in> ?tree" using diag_open by auto
  ultimately
  have "\<not>finite ?tree" using infinity[of _ "\<lambda>n. SOME b. open_branch b (_ n) Cs"] by simp
  (* Get infinite path *)
  moreover 
  have "\<forall>ds d. \<not>falsifiescs (ds @ d) Cs \<longrightarrow> \<not>falsifiescs ds Cs" 
    using longer_falsifies[of Cs] by blast
  then have "(\<forall>ds d. ds @ d \<in> ?tree \<longrightarrow> ds \<in> ?tree)" by auto
  ultimately
  have "\<exists>c. list_chain c \<and> (\<forall>n. c n \<in> ?tree)" using konig[of ?tree] by blast
  then have "\<exists>G. list_chain G \<and> (\<forall>n. \<not> falsifiescs (G n) Cs)" by auto
  (* Apply above Chain lemma *)
  then show "\<exists>G. evalcs HFun G Cs" using list_chain_model finite_cs by auto
qed
(* This lemma is interesting: lemma "\<forall>G. \<not> evalcs F G Cs \<Longrightarrow> \<forall>G. \<not> evalcs HFun G Cs" oops*)

lemma shorter_falsifiesl:
  assumes "falsifiesl (ds@d) l"
  assumes "nat_from_fatom l < length ds"
  shows "falsifiesl ds l"
proof (cases l)
  case (Pos p ts)
  from assms Pos obtain i where i_p: "i < length (ds@d)
      \<and> (ds@d) ! i = False
      \<and> fatom_from_nat i = Pos p ts" by auto
  moreover
  then have "i = nat_from_fatom (Pos p ts)" using undiag_diag_fatom[of i] by auto
  then have "i < length ds" using assms Pos by auto
  moreover
  then have "ds ! i = False" using i_p by (simp add: nth_append) 
  ultimately show ?thesis using Pos by auto
next
  case (Neg p ts)
  from assms Neg obtain i where i_p: "i < length (ds@d)
      \<and> (ds@d) ! i = True
      \<and> fatom_from_nat i = Pos p ts" by auto
  moreover
  then have "i = nat_from_fatom (Pos p ts)" using undiag_diag_fatom[of i] by auto
  then have "i < length ds" using assms Neg undiag_neg by auto
  moreover
  then have "ds ! i = True" using i_p by (simp add: nth_append) 
  ultimately show ?thesis using Neg by auto
qed

theorem herbrand'_contra:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>G. \<not>evalcs HFun G Cs"
  shows "\<exists>T. \<forall>G. branch G T \<longrightarrow> closed_branch G T Cs"
proof -
  from finite_cs unsat have "\<forall>T. \<exists>G. open_branch G T Cs \<Longrightarrow> \<exists>G. evalcs HFun G Cs" using herbrand' by blast
  then show ?thesis using unsat by blast 
qed

theorem herbrand:
  assumes unsat: "\<forall>G. \<not> evalcs HFun G Cs"
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  shows "\<exists>T. closed_tree T Cs"
proof -
  from unsat finite_cs obtain T where "anybranch T (\<lambda>b. closed_branch b T Cs)" using herbrand'_contra[of Cs] by blast
  then have "\<exists>T. anybranch T (\<lambda>p. falsifiescs p Cs) \<and> anyinternal T (\<lambda>p. \<not> falsifiescs p Cs)" 
    using cutoff_branch_internal[of T "(\<lambda>p. falsifiescs p Cs)"] by blast
  then show ?thesis by auto
qed

end

