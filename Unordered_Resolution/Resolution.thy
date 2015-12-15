theory Resolution imports TermsAndLiterals Tree "~~/src/HOL/IMP/Star" begin

hide_const (open) TermsAndLiterals.Leaf TermsAndLiterals.Branch

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

fun varst  :: "fterm \<Rightarrow> var_sym set" 
and varsts :: "fterm list \<Rightarrow> var_sym set" where 
  "varst (Var x) = {x}"
| "varst (Fun f ts) = varsts ts"
| "varsts [] = {}"
| "varsts (t # ts) = (varst t) \<union> (varsts ts)"

definition varsl :: "fterm literal \<Rightarrow> var_sym set" where 
  "varsl l = varsts (get_terms l)"

definition varsls :: "fterm literal set \<Rightarrow> var_sym set" where 
  "varsls L \<equiv> \<Union>l\<in>L. varsl l"

abbreviation groundl :: "fterm literal \<Rightarrow> bool" where
  "groundl l \<equiv> grounds (get_terms l)"

abbreviation groundls :: "fterm clause \<Rightarrow> bool" where
  "groundls L \<equiv> \<forall> l \<in> L. groundl l"

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
(* I Could Curry here and remove ts *)

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
 *)
definition var_renaming :: "substitution \<Rightarrow> bool" where
  "var_renaming \<sigma> \<longleftrightarrow> (\<forall>x. \<exists>y. \<sigma> x = Var y)"

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

definition resolution :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> fterm clause" where
  "resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = (C\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s - L\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s) \<union> (C\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s - L\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s)"

definition lresolution :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> fterm clause" where
  "lresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = ((C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2)) {\<sigma>}\<^sub>l\<^sub>s"

inductive resolution_step :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  resolution_rule: 
    "C\<^sub>1 \<in> Cs \<Longrightarrow> C\<^sub>2 \<in> Cs \<Longrightarrow> applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<Longrightarrow> 
       resolution_step Cs (Cs \<union> {resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>})"
| standardize_apart:
    "C \<in> Cs \<Longrightarrow> var_renaming \<sigma> \<Longrightarrow> resolution_step Cs (Cs \<union> {C {\<sigma>}\<^sub>l\<^sub>s})"

inductive lresolution_step :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  lresolution_rule: 
    "C\<^sub>1 \<in> Cs \<Longrightarrow> C\<^sub>2 \<in> Cs \<Longrightarrow> applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<Longrightarrow> 
       lresolution_step Cs (Cs \<union> {lresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>})"
| lstandardize_apart:
    "C \<in> Cs \<Longrightarrow> var_renaming \<sigma> \<Longrightarrow> lresolution_step Cs (Cs \<union> {C {\<sigma>}\<^sub>l\<^sub>s})"

definition resolution_deriv :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "resolution_deriv = star resolution_step"

definition lresolution_deriv :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "lresolution_deriv = star lresolution_step"

(* Very nice lemma, but it is not used. 
  Could be used in a Completeness proof *)
lemma ground_resolution:
  assumes ground: "groundls C\<^sub>1 \<and> groundls C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = (C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2) \<and> (\<exists>l. L\<^sub>1 = {l} \<and> L\<^sub>2 = {l}\<^sup>C)"
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

  from resl l_p show ?thesis unfolding resolution_def by auto
qed

(* Very nice lemma, but it is not used. 
  Could be used in a Completeness proof *)
lemma ground_resolution_ground: 
  assumes asm: "groundls C\<^sub>1 \<and> groundls C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "groundls (resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
proof -
  from asm appl have "resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = (C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2)" using ground_resolution by auto
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
  assumes Comp: "l\<^sub>1\<^sup>c = l\<^sub>2"
  shows "evalc F G ((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))"
proof -
  have "\<forall>E. \<exists>l \<in> (((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))). evall E F G l"
    proof
      fix E
      have "evall E F G l\<^sub>1 \<or> evall E F G l\<^sub>2" using Comp by (cases l\<^sub>1) auto
      then show "\<exists>l \<in> (((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))). evall E F G l"
        proof
          assume "evall E F G l\<^sub>1"
          then have "\<not>evall E F G l\<^sub>2" using Comp by (cases l\<^sub>1) auto
          then have "\<exists>l\<^sub>2'\<in> C\<^sub>2. l\<^sub>2' \<noteq> l\<^sub>2 \<and> evall E F G l\<^sub>2'" using l\<^sub>2inc\<^sub>2 C\<^sub>2sat unfolding evalc_def by auto
          then show "\<exists>l\<in>(C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}). evall E F G l" by auto
        next
          assume "evall E F G l\<^sub>2" (* Symmetric *)
          then have "\<not>evall E F G l\<^sub>1" using Comp by (cases l\<^sub>1) auto
          then have "\<exists>l\<^sub>1'\<in> C\<^sub>1. l\<^sub>1' \<noteq> l\<^sub>1 \<and> evall E F G l\<^sub>1'" using l\<^sub>1inc\<^sub>1 C\<^sub>1sat unfolding evalc_def by auto
          then show "\<exists>l\<in>(C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}). evall E F G l" by auto
        qed
    qed
  then show ?thesis unfolding evalc_def by simp
qed

lemma resolution_sound:
  assumes sat\<^sub>1: "evalc F G C\<^sub>1"
  assumes sat\<^sub>2: "evalc F G C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "evalc F G (resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
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
  then have comp: "(l\<^sub>1 {\<sigma>}\<^sub>l)\<^sup>c = l\<^sub>2 {\<sigma>}\<^sub>l" using comp_sub comp_swap by auto (* These steps Could be lemmas *)

  from appl have "unifierls \<sigma> (L\<^sub>2\<^sup>C)" 
    using unifier_sub2 unfolding mguls_def applicable_def by blast
  then have "unifierls \<sigma> L\<^sub>2" by auto
  from this l\<^sub>2_p have l\<^sub>2\<sigma>isl\<^sub>2\<sigma>: "{l\<^sub>2{\<sigma>}\<^sub>l} = L\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s" unfolding unifierls_def by auto

  from sat\<^sub>1\<sigma> sat\<^sub>2\<sigma> inc\<^sub>1\<sigma> inc\<^sub>2\<sigma> comp have "evalc F G (C\<^sub>1{\<sigma>}\<^sub>l\<^sub>s - {l\<^sub>1{\<sigma>}\<^sub>l} \<union> (C\<^sub>2{\<sigma>}\<^sub>l\<^sub>s - {l\<^sub>2{\<sigma>}\<^sub>l}))" using simple_resolution_sound[of F G "C\<^sub>1 {\<sigma>}\<^sub>l\<^sub>s" "C\<^sub>2 {\<sigma>}\<^sub>l\<^sub>s" "l\<^sub>1 {\<sigma>}\<^sub>l" " l\<^sub>2 {\<sigma>}\<^sub>l"]
    by auto
  from this l\<^sub>1\<sigma>isl\<^sub>1\<sigma> l\<^sub>2\<sigma>isl\<^sub>2\<sigma> show ?thesis unfolding resolution_def by auto
qed

lemma lresolution_superset: "resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<subseteq> lresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
 unfolding resolution_def lresolution_def by auto

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
 

lemma lresolution_sound:
  assumes sat\<^sub>1: "evalc F G C\<^sub>1"
  assumes sat\<^sub>2: "evalc F G C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "evalc F G (lresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
proof -
  from sat\<^sub>1 sat\<^sub>2 appl have "evalc F G (resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)" using resolution_sound by blast
  then show ?thesis using superset_sound lresolution_superset by metis
qed

lemma sound_step: "resolution_step Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'"
proof (induction rule: resolution_step.induct)
  case (resolution_rule C\<^sub>1 Cs C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)
  then have "evalc F G C\<^sub>1 \<and> evalc F G C\<^sub>2" unfolding evalcs_def by auto
  then have "evalc F G (resolution C\<^sub>1 C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)" 
    using resolution_sound resolution_rule by auto
  then show ?case using resolution_rule unfolding evalcs_def by auto
next
  case (standardize_apart C Cs \<sigma>)
  then have "evalc F G C" unfolding evalcs_def by auto
  then have "evalc F G (C{\<sigma>}\<^sub>l\<^sub>s)" using subst_sound by auto
  then show ?case using standardize_apart unfolding evalcs_def by auto
qed

lemma lsound_step: "lresolution_step Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'"
proof (induction rule: lresolution_step.induct)
  case (lresolution_rule C\<^sub>1 Cs C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)
  then have "evalc F G C\<^sub>1 \<and> evalc F G C\<^sub>2" unfolding evalcs_def by auto
  then have "evalc F G (lresolution C\<^sub>1 C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)" 
    using lresolution_sound lresolution_rule by auto
  then show ?case using lresolution_rule unfolding evalcs_def by auto
next
  case (lstandardize_apart C Cs \<sigma>)
  then have "evalc F G C" unfolding evalcs_def by auto
  then have "evalc F G (C{\<sigma>}\<^sub>l\<^sub>s)" using subst_sound by auto
  then show ?case using lstandardize_apart unfolding evalcs_def by auto
qed

lemma sound_derivation: 
  "resolution_deriv Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'" 
unfolding resolution_deriv_def
proof (induction rule: star.induct)
  case refl then show ?case by auto
next
  case (step Cs\<^sub>1 Cs\<^sub>2 Cs\<^sub>3) then show ?case using sound_step by auto
qed

lemma lsound_derivation: 
  "lresolution_deriv Cs Cs' \<Longrightarrow> evalcs F G Cs \<Longrightarrow> evalcs F G Cs'" 
unfolding lresolution_deriv_def
proof (induction rule: star.induct)
  case refl then show ?case by auto
next
  case (step Cs\<^sub>1 Cs\<^sub>2 Cs\<^sub>3) then show ?case using lsound_step by auto
qed

section {* Enumerations *}

fun hlit_of_flit :: "fterm literal \<Rightarrow> hterm literal" where
  "hlit_of_flit (Pos P ts) = Pos P (hterms_of_fterms ts)"
| "hlit_of_flit (Neg P ts) = Neg P (hterms_of_fterms ts)"

lemma undiag_neg: "undiag_fatom (Neg P ts) = undiag_fatom (Pos P ts)"
  unfolding undiag_fatom_def undiag_hatom_def by auto

lemma undiag_neg2: "undiag_hatom (Neg P ts) = undiag_hatom (Pos P ts)"
  unfolding undiag_fatom_def undiag_hatom_def by auto

lemma ground_h_undiag: "groundl l \<Longrightarrow> undiag_hatom (hlit_of_flit l) = undiag_fatom l"
proof (induction l) (* Not really induction *)
  case (Pos P ts) 
  then show ?case unfolding undiag_fatom_def by auto
next
  case (Neg P ts) 
  then show ?case using undiag_neg undiag_neg2 unfolding undiag_fatom_def by auto
qed


section {* Herbrand Interpretations *}

(* HFun is the Herbrand function denotation in which terms are mapped to themselves  *)
value HFun

lemma hterms_ground: "ground (fterm_of_hterm t)" "grounds (fterms_of_hterms ts)"
apply (induction t and ts rule: fterm_of_hterm.induct fterms_of_hterms.induct)
apply auto
done

lemma hatom_ground: "groundl (fatom_of_hatom l)"
apply (induction l)
using hterms_ground apply auto
done

lemma diag_ground: "groundl (diag_fatom n)" unfolding diag_fatom_def using hatom_ground by auto 

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

(* WARNING: My definition of falsification is WRONG! For a clause I allow each literal
   to be individually projected down to the ground world, BUT they should all be projected
   down with the same substitution to be falsified.
*)

(* This definition is quite syntactical. I think that's good though.
   Alternative: Check if an instance is in list. If not return true.
   Otherwise, build an interpretation from the partial interpretation *)

(* Only ground literals can be falsified *)
fun falsifiesl :: "partial_pred_denot \<Rightarrow> fterm literal \<Rightarrow> bool" where
  "falsifiesl G (Pos p ts) = 
     (\<exists>i.  
      i < length G
      \<and> G ! i = False
      \<and> diag_fatom i = Pos p ts)"
| "falsifiesl G (Neg p ts) = 
     (\<exists>i.  
      i < length G
      \<and> G ! i = True
      \<and> diag_fatom i = Pos p ts)"

abbreviation falsifiesg :: "partial_pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "falsifiesg G C \<equiv> (\<forall>l \<in> C. falsifiesl G l)"

abbreviation falsifiesc :: "partial_pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "falsifiesc G C \<equiv> (\<exists>C'. instance_ofls C' C \<and> falsifiesg G C')"
(*A perhaps better definition:
First  we define it for groundliterals. We dont need the substitution since they are ground.
Second we define it for groundclauses - all ground literals must be falsified.
Third for fol-clauses - has ground instance that is falsified
*)

abbreviation falsifiescs :: "partial_pred_denot \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "falsifiescs G Cs \<equiv> (\<exists>C \<in> Cs. falsifiesc G C)"

lemma falsifies_ground:
  assumes "falsifiesl G l"
  shows "groundl l"
proof (cases l)
  case (Pos p ts) 
  then have "\<exists>i. diag_fatom i = Pos p ts" using assms by auto
  then show ?thesis using diag_ground Pos by metis
next
  case (Neg p ts) 
  then have "\<exists>i. diag_fatom i = Pos p ts" using assms by auto
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
      \<and> diag_fatom i = Pos (get_pred l) (get_terms l)"
using assms by (cases l) auto (* Not really induction *)

abbreviation extend :: "(nat \<Rightarrow> partial_pred_denot) \<Rightarrow> hterm pred_denot" where
  "extend f P ts \<equiv> (
     let n = undiag_hatom (Pos P ts) in
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

lemma sub_of_denot_equivl: "evall E HFun G (l {sub_of_denot E}\<^sub>l) = evall E HFun G l"
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

(* This theorem is not true any more... *)
lemma partial_equiv_subst': "falsifiesl G ((l ::fterm literal) {\<tau>}\<^sub>l) \<Longrightarrow> falsifiesl G l"
proof (induction l) (* Not really induction - just cases *)

oops


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

subsection {* Semantic Trees *}

abbreviation closed_branch :: "partial_pred_denot \<Rightarrow> tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "closed_branch G T Cs \<equiv> branch G T \<and> falsifiescs G Cs"

abbreviation open_branch :: "partial_pred_denot \<Rightarrow> tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "open_branch G T Cs \<equiv> branch G T \<and> \<not>falsifiescs G Cs"

fun closed_tree :: "tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "closed_tree T Cs \<longleftrightarrow> anybranch T (\<lambda>b. closed_branch b T Cs) 
                  \<and> anyinternal T (\<lambda>p. \<not>falsifiescs p Cs)"


section {* Herbrand's Theorem *}

lemma maximum:
  assumes asm: "finite C"
  shows "\<exists>n :: nat. \<forall>l \<in> C. f l \<le> n"
proof
  from asm show "\<forall>l\<in>C. f l \<le> (Max (f ` C))" by auto
qed

(* Det her navn er altså mærkeligt baglæns... *)
lemma extend_preserves_model:
  assumes f_chain: "list_chain (f :: nat \<Rightarrow> partial_pred_denot)" 
  assumes n_max: "\<forall>l\<in>C. undiag_fatom l \<le> n"
  assumes C_ground: "groundls C"
  assumes C_false: "\<not>evalc HFun (extend f) C"
  shows "falsifiesc (f (Suc n)) C" (* probably - this should be falsifiesg now *)
proof -
  let ?F = "HFun" 
  let ?G = "extend f"
  {
  fix l
  assume asm: "l\<in>C"
  let ?i = "undiag_fatom l"
  from asm have i_n: "?i \<le> n" using n_max by auto
  then have j_n: "?i \<le> length (f n)" using f_chain chain_length[of f n] by auto

  from C_false have "\<not>(\<forall>E. \<exists>l \<in> C. evall E ?F ?G l)" unfolding evalc_def by auto
  then have "\<exists>E. \<forall>l \<in> C. \<not> evall E ?F ?G l" by auto
  then have "\<forall>E. \<forall>l \<in> C. \<not> evall E ?F ?G l" using C_ground ground_var_denot by blast
  then have last: "\<forall>E. \<not> evall E ?F ?G l" using asm by blast

  then have "falsifiesl (f (Suc n)) l"
    proof (cases l)
      case (Pos P ts)
      from Pos asm C_ground have ts_ground: "grounds ts" by auto
      from Pos asm C_ground have undiag_l: "undiag_hatom (hlit_of_flit l) = ?i" using ground_h_undiag by blast

      from last have "\<not>?G P (hterms_of_fterms ts)" using evall_grounds[of ts _ ?G P] ts_ground Pos by auto
      then have "f (Suc ?i) ! ?i = False" using Pos undiag_l by auto
      moreover
      have "f (Suc ?i) ! ?i = f (Suc n) ! ?i" 
        using f_chain i_n j_n chain_length[of f] ith_in_extension[of f] by simp
      ultimately have "f (Suc n) ! ?i = False" by auto
      then have "  
      ?i < length (f (Suc n)) (* j_n *)
      \<and> f (Suc n) ! ?i = False (*last thing *)
      \<and> diag_fatom ?i = Pos P ts (* by definition of ?i *)
      \<and> ts = ts {\<epsilon>}\<^sub>t\<^sub>s" 
        using 
          j_n ts_ground diag_undiag_fatom instance_ofts_self f_chain chain_length[of f] Pos empty_subts
        by auto
      then show ?thesis using Pos by auto
    next
      case (Neg P ts) (* symmetric *)
      from Neg asm C_ground have ts_ground: "grounds ts" by auto
      from Neg asm C_ground have undiag_l: "undiag_hatom (hlit_of_flit l) = ?i" using ground_h_undiag by blast

      from last have "?G P (hterms_of_fterms ts)" using evall_grounds[of ts _ ?G P] C_ground asm Neg by auto
      then have "f (Suc ?i) ! ?i = True" using Neg undiag_neg undiag_l
         by (metis hatom_of_fatom.simps(1) undiag_fatom_def) 
      moreover
      have "f (Suc ?i) ! ?i = f (Suc n) ! ?i" 
        using f_chain i_n j_n chain_length[of f] ith_in_extension[of f] by simp
      ultimately have "f (Suc n) ! ?i = True" by auto
      then have "  
      ?i < length (f (Suc n)) (* j_n *)
      \<and> f (Suc n) ! ?i = True (*last thing *)
      \<and> diag_fatom ?i = Pos P ts (* by definition of ?i *)
      \<and> ts = ts {\<epsilon>}\<^sub>t\<^sub>s" 
        using j_n diag_undiag_fatom instance_ofts_self[of ts] f_chain chain_length[of f] Neg undiag_neg ts_ground empty_subts
        by auto
      then show ?thesis using Neg by auto
    qed
  }
  then have "falsifiesg (f (Suc n)) C" by auto
  then show ?thesis using instance_ofls_self by auto
qed

(* If we have a list-chain of partial models, then we have a model *)
lemma list_chain_model:
  assumes f_chain: "list_chain (f :: nat \<Rightarrow> partial_pred_denot)"
  assumes model_cs: "\<forall>n. \<not>falsifiescs (f n) Cs" 
  assumes fin_cs: "finite Cs"
  assumes fin_c: "\<forall>C \<in> Cs. finite C"
  shows "\<exists>G. evalcs HFun G Cs"
proof
  let ?F = "HFun"
  let ?G = "extend f"

  have "\<forall>C E. (C \<in> Cs \<longrightarrow> (\<exists>l \<in> C. evall E ?F ?G l))"
    proof (rule allI; rule allI; rule impI)
      fix C
      fix E
      assume asm: "C \<in> Cs"
      let ?\<sigma> = "sub_of_denot E"
      have groundc\<sigma>: "groundls (C {?\<sigma>}\<^sub>l\<^sub>s)" using sub_of_denot_equiv_ground by auto
      from fin_c asm have "finite (C {?\<sigma>}\<^sub>l\<^sub>s)" by auto
      then obtain n where largest: "\<forall>l \<in> (C {?\<sigma>}\<^sub>l\<^sub>s). undiag_fatom l \<le> n" using maximum by blast
      from model_cs asm have "\<not>falsifiesc (f (Suc n)) C" by auto
      then have model_c: "\<not>falsifiesc (f (Suc n)) (C {?\<sigma>}\<^sub>l\<^sub>s)" using partial_equiv_subst by blast 

      have "evalc HFun ?G (C {?\<sigma>}\<^sub>l\<^sub>s)" 
        using groundc\<sigma> f_chain largest model_c 
              extend_preserves_model[of f "C {?\<sigma>}\<^sub>l\<^sub>s" n] by blast
      then have "\<forall>E. \<exists>l \<in> (C {?\<sigma>}\<^sub>l\<^sub>s). evall E ?F ?G l" unfolding evalc_def by auto
      then have "\<exists>l \<in> (C {?\<sigma>}\<^sub>l\<^sub>s). evall E ?F ?G l" by auto
      then show "\<exists>l\<in>C. evall E ?F ?G l" using sub_of_denot_equiv_ground by simp
      (* Først skal vi have lavet det ground. Det gør vi med at lave environmentet om til en substitution. Det kan vi kun hvis vores univers er herbrand *)(* Se på en partial model for det største literal *)  (* Den gør clausen sand. Derfor gør modellen fra Chainen også clausen sand *)
    qed
  then have "\<forall>C \<in> Cs. \<forall>E. \<exists>l \<in> C. evall E ?F ?G l" by auto
  then have "\<forall>C \<in> Cs. evalc ?F ?G C" unfolding evalc_def by auto
  then show "evalcs ?F ?G Cs" unfolding evalcs_def by auto
qed

fun deeptree :: "nat \<Rightarrow> tree" where
  "deeptree 0 = Leaf"
| "deeptree (Suc n) = Branch (deeptree n) (deeptree n)"

thm extend_preserves_model
thm list_chain_model

lemma branch_length: "branch b (deeptree n) \<Longrightarrow> length b = n"
proof (induction n arbitrary: b)
  case 0 then show ?case using branch_inv_Leaf by auto
next
  case (Suc n)
  then have "branch b (Branch (deeptree n) (deeptree n))" by auto
  then obtain a b' where p: "b=a#b'\<and> branch b' (deeptree n)" using branch_inv_Branch[of b] by blast
  then have "length b' = n" using Suc by auto
  then show ?case using p by auto
qed

lemma infinity:
  assumes bij: "\<forall>n :: nat. undiago (diago n) = n"
  assumes all_tree: "\<forall>n :: nat. (diago n) \<in> tree"
  shows "\<not>finite tree"
proof -
  from bij all_tree have "\<forall>n. n = undiago (diago n) \<and> (diago n) \<in> tree" by auto
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
      \<and> diag_fatom i = Pos P ts" by auto
  moreover
  from i_p have "i < length (ds@d)" by auto
  moreover
  from i_p have "(ds@d) ! i = False" by (simp add: nth_append) 
  ultimately
  have "
      i < length (ds@d)
      \<and> (ds@d) ! i = False
      \<and> diag_fatom i = Pos P ts" by auto
  then show ?case by auto
next
  case (Neg P ts) (* very symmetrical *)
  then obtain i where i_p: "  
      i < length ds
      \<and> ds ! i = True
      \<and> diag_fatom i = Pos P ts" by auto
  moreover
  from i_p have "i < length (ds@d)" by auto
  moreover
  from i_p have "(ds@d) ! i = True" by (simp add: nth_append) 
  ultimately
  have " 
      i < length (ds@d)
      \<and> (ds@d) ! i = True
      \<and> diag_fatom i = Pos P ts" by auto
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
  assumes "undiag_fatom l < length ds"
  shows "falsifiesl ds l"
proof (cases l)
  case (Pos p ts)
  from assms Pos obtain i where i_p: "i < length (ds@d)
      \<and> (ds@d) ! i = False
      \<and> diag_fatom i = Pos p ts" by auto
  moreover
  then have "i = undiag_fatom (Pos p ts)" using undiag_diag_fatom[of i] by auto
  then have "i < length ds" using assms Pos by auto
  moreover
  then have "ds ! i = False" using i_p by (simp add: nth_append) 
  ultimately show ?thesis using Pos by auto
next
  case (Neg p ts)
  from assms Neg obtain i where i_p: "i < length (ds@d)
      \<and> (ds@d) ! i = True
      \<and> diag_fatom i = Pos p ts" by auto
  moreover
  then have "i = undiag_fatom (Pos p ts)" using undiag_diag_fatom[of i] by auto
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


section {* Lifting Lemma *}

lemma unification: "unifierls \<sigma> L \<Longrightarrow> \<exists>\<theta>. mgu \<theta> L" sorry

lemma lifting:
  assumes appart: "varsls C \<inter> varsls D = {}"
  assumes inst\<^sub>1: "instance_ofls C' C"
  assumes inst\<^sub>2: "instance_ofls D' D"
  assumes appl: "applicable C' D' L' M' \<sigma>"
  shows "\<exists>L M \<tau>. applicable C D L M \<tau> \<and>
                   instance_ofls (lresolution C' D' L' M' \<sigma>) (lresolution C D L M \<tau>)"
proof -
  let ?C'\<^sub>1 = "C' - L'"
  let ?D'\<^sub>1 = "D' - M'"

  from inst\<^sub>1 obtain lmbd where lmbd_p: "C {lmbd}\<^sub>l\<^sub>s = C'" unfolding instance_ofls_def by auto
  from inst\<^sub>2 obtain \<mu> where \<mu>_p: "D {\<mu>}\<^sub>l\<^sub>s = D'" unfolding instance_ofls_def by auto
  
  from \<mu>_p lmbd_p appart obtain \<eta> where \<eta>_p: "C {\<eta>}\<^sub>l\<^sub>s = C' \<and> D {\<eta>}\<^sub>l\<^sub>s = D'" using merge_sub by force

  from \<eta>_p have "\<exists>L \<subseteq> C. L {\<eta>}\<^sub>l\<^sub>s = L' \<and> (C - L){\<eta>}\<^sub>l\<^sub>s = ?C'\<^sub>1" using appl project_sub[of \<eta> C C' L'] unfolding applicable_def by auto
  then obtain L where L_p: "L \<subseteq> C \<and> L {\<eta>}\<^sub>l\<^sub>s = L' \<and> (C - L){\<eta>}\<^sub>l\<^sub>s = ?C'\<^sub>1" by auto
  let ?C\<^sub>1 = "C - L"

  from \<eta>_p have "\<exists>M \<subseteq> D. M {\<eta>}\<^sub>l\<^sub>s = M' \<and> (D - M){\<eta>}\<^sub>l\<^sub>s = ?D'\<^sub>1" using appl project_sub[of \<eta> D D' M'] unfolding applicable_def by auto
  then obtain M where M_p: "M \<subseteq> D \<and> M {\<eta>}\<^sub>l\<^sub>s = M' \<and> (D - M){\<eta>}\<^sub>l\<^sub>s = ?D'\<^sub>1" by auto
  let ?D\<^sub>1 = "D - M"

  from appl have "mguls \<sigma> (L' \<union> M'\<^sup>C)" unfolding applicable_def by auto
  then have "mguls \<sigma> (L {\<eta>}\<^sub>l\<^sub>s \<union> M {\<eta>}\<^sub>l\<^sub>s\<^sup>C)" using L_p M_p by auto
  then have "mguls \<sigma> ((L  \<union> M\<^sup>C) {\<eta>}\<^sub>l\<^sub>s)" using compls_subls subls_union by auto
  then have "unifierls \<sigma> ((L  \<union> M\<^sup>C) {\<eta>}\<^sub>l\<^sub>s)" unfolding mguls_def by auto
  then have \<eta>\<sigma>uni: "unifierls (\<eta> \<cdot> \<sigma>) (L  \<union> M\<^sup>C)" 
    unfolding unifierls_def using composition_conseq2l by auto
  then obtain \<tau> where \<tau>_p: "mguls \<tau> (L  \<union> M\<^sup>C)" using unification by force
  then obtain \<phi> where \<phi>_p: "\<tau> \<cdot> \<phi> = \<eta> \<cdot> \<sigma>" using \<eta>\<sigma>uni unfolding mguls_def by auto
  
  (* Showing that we have the desired resolvent *)
  let ?E = "((C - L)  \<union> (D - M)) {\<tau>}\<^sub>l\<^sub>s"
  have "?E {\<phi>}\<^sub>l\<^sub>s  = (?C\<^sub>1 \<union> ?D\<^sub>1 ) {\<tau> \<cdot> \<phi>}\<^sub>l\<^sub>s" using subls_union composition_conseq2ls by auto
  also have "... = (?C\<^sub>1 \<union> ?D\<^sub>1 ) {\<eta> \<cdot> \<sigma>}\<^sub>l\<^sub>s" using \<phi>_p by auto
  also have "... = (?C\<^sub>1 {\<eta>}\<^sub>l\<^sub>s \<union> ?D\<^sub>1 {\<eta>}\<^sub>l\<^sub>s) {\<sigma>}\<^sub>l\<^sub>s" using subls_union composition_conseq2ls by auto
  also have "... = (?C'\<^sub>1 \<union> ?D'\<^sub>1) {\<sigma>}\<^sub>l\<^sub>s" using \<eta>_p L_p M_p by auto
  finally have "?E {\<phi>}\<^sub>l\<^sub>s = ((C' - L') \<union> (D' - M')){\<sigma>}\<^sub>l\<^sub>s" by auto
  then have inst: "instance_ofls (lresolution C' D' L' M' \<sigma>) (lresolution C D L M \<tau>) "
    unfolding lresolution_def instance_ofls_def by blast

  (* Showing that the resolution is applicable: *)
  {
    have "C' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "C \<noteq> {}" using \<eta>_p by auto
  } moreover {
    have "D' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "D \<noteq> {}" using \<eta>_p by auto
  } moreover {
    have "L' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "L \<noteq> {}" using L_p by auto
  } moreover {
    have "M' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "M \<noteq> {}" using M_p by auto
  }
  ultimately have appll: "applicable C D L M \<tau>" 
    using appart L_p M_p \<tau>_p unfolding applicable_def by auto

  from inst appll show ?thesis by auto
qed


section {* Completeness *}
(* assumes openb: "\<forall>T. \<exists>G. open_branch G T Cs" assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C" shows "\<exists>G. evalcs HFun G Cs" *)

lemma falsifiesg_empty:
  assumes "falsifiesg [] C"
  shows "C = {}"
proof -
  have "\<forall>l \<in> C. False"
    proof
      fix l
      assume "l\<in>C"
      then have "falsifiesl [] l" using assms by auto
      then show False by (cases l) auto
    qed
  then show ?thesis by auto
qed


lemma falsifiescs_empty:
  assumes "falsifiesc [] C"
  shows "C = {}"
proof -
  from assms obtain C' where C'_p: "instance_ofls C' C \<and> falsifiesg [] C'" by auto
  then have "C'= {}" using falsifiesg_empty by auto
  then show "C = {}" using C'_p unfolding instance_ofls_def by auto
qed

(* lemma completeness': \\  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C" \\ assumes notLeaf: "T \<noteq> Leaf" \\  assumes closed: "closed_tree T Cs" \\   shows "\<exists>T'. \<exists>c\<^sub>1 \<in> Cs. \<exists>c\<^sub>2 \<in> Cs. \<exists>r. \\            lresolvent r C\<^sub>1 C\<^sub>2\\         \<and> (\<forall>G. branch G T' \<longrightarrow> \<not>open_branch G T' (Cs \<union> {r})) \\         \<and> size T' < size T"\\proof -\\(*  from notLeaf obtain b where "branch (b@[Right]) T \<and> branch (b@[Left]) T" using has_Branch_of_Leafs by blast\\  then have "falsifiescs (b@[True]) Cs \<and> falsifiescs (b@[False]) Cs" using Closed by auto\\  then obtain C\<^sub>1 C\<^sub>2 where "C\<^sub>1 \<in> Cs \<and> C\<^sub>2 \<in> Cs \<and> falsifiesc (b@[True]) C\<^sub>1 \<and> falsifiesc (b@[False]) C\<^sub>2" by auto\\ *) oops *)

lemma number_lemma:
  assumes "\<not>(\<exists>i. i < length (B :: bool list) \<and> P(i))"
  assumes "\<exists>i. i < length (B@[True]) \<and> P(i)"
  shows "P(length B)"
using assms less_Suc_eq by auto


theorem completeness':
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  shows "closed_tree T Cs \<Longrightarrow> \<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
proof (induction T arbitrary: Cs rule: Nat.measure_induct_rule[of treesize])
  fix T::tree
  fix Cs :: "fterm clause set"
  assume "(\<And>T' Cs. treesize T' < treesize T \<Longrightarrow>
                    closed_tree T' Cs \<Longrightarrow> \<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs')"
  assume clo: "closed_tree T Cs"
  
  {
    assume "treesize T = 0"
    then have "T=Leaf" using treesize_Leaf by auto
    then have "anybranch Leaf (\<lambda>b. closed_branch b Leaf Cs)" using clo by auto
    then have "closed_branch [] Leaf Cs" using branch_inv_Leaf by auto
    then have "falsifiescs [] Cs" by auto
    then have "\<exists>C \<in> Cs. falsifiesc [] C" by auto
    then have "\<exists>C \<in> Cs. C={}" using falsifiescs_empty by auto
    then have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" unfolding resolution_deriv_def by auto
  }
  moreover
  {
    assume "treesize T > 0"
    then have "\<exists>l r. T=Branch l r" by (cases T) auto
    then have "\<exists>B. branch (B@[True]) T \<and> branch (B@[False]) T" using Branch_Leaf_Leaf_Tree by auto
    then have "\<exists>B. internal B T \<and> branch (B@[True]) T \<and> branch (B@[False]) T" 
      using internal_branch[of _ "[]" _ T] by auto
    then obtain B where b_p: "internal B T \<and> branch (B@[True]) T \<and> branch (B@[False]) T" by auto
    let ?B1 = "B@[True]"
    let ?B2 = "B@[False]"                                       

    have "\<exists>C1 \<in> Cs. falsifiesc ?B1 C1" using b_p clo by auto 
    then obtain C1  where C1_p:  "C1 \<in> Cs \<and>falsifiesc ?B1 C1" by auto
    then have "\<exists>C1'. groundls C1' \<and> instance_ofls C1' C1 \<and> falsifiesg ?B1 C1'" 
      using falsifiesc_ground[of C1 ?B1] by metis
    then obtain C1' where C1'_p: "groundls C1' \<and> instance_ofls C1' C1 \<and> falsifiesg ?B1 C1'" by auto
    (* We went down to the ground world *)
    then have "\<forall>l \<in> C1'. falsifiesl (B@[True]) l" by auto
    moreover 
    have "\<not>falsifiesc B C1" using C1_p b_p clo by auto
    then have "\<not> falsifiesg B C1'" using C1'_p by auto
    then have "\<not>(\<forall>l \<in> C1'. falsifiesl B l)" by auto
    ultimately have "\<exists>l \<in> C1'. falsifiesl (B@[True]) l \<and> \<not>(falsifiesl B l)" by auto
    then obtain l1 where l1_p: "l1 \<in> C1' \<and> falsifiesl (B@[True]) l1 \<and> \<not>(falsifiesl B l1)" by auto
    then have "\<not>(\<exists>i.  
      i < length B
      \<and> B ! i = (\<not>sign l1)
      \<and> diag_fatom i = Pos (get_pred l1) (get_terms l1))" using instance_ofts_self by (induction l1) auto
    then have "\<not>(\<exists>i.  
      i < length B
      \<and> (B@[True]) ! i = (\<not>sign l1)
      \<and> diag_fatom i = Pos (get_pred l1) (get_terms l1))" by (metis nth_append) 
    moreover 
    have "groundl l1" using C1'_p l1_p by auto
    then have "\<exists>i.  
      i < length (B@[True])
      \<and> (B@[True]) ! i = (\<not>sign l1)
      \<and> diag_fatom i = Pos (get_pred l1) (get_terms l1)" using ground_falsifies l1_p by blast
    ultimately
    have ggg: "(B@[True]) ! (length B) = (\<not>sign l1) \<and> diag_fatom (length B) = Pos (get_pred l1) (get_terms l1)"
      using number_lemma[of B "\<lambda>i. (B @ [True]) ! i = (\<not> sign l1) \<and> diag_fatom i = Pos (get_pred l1) (get_terms l1)"] by auto
    then have l1_sign: "sign l1 = False" by auto
    from ggg have "undiag_fatom (Pos (get_pred l1) (get_terms l1)) = length B" using undiag_diag_fatom by metis
    then have l1_no: "undiag_fatom l1 = length B" using undiag_neg[of "get_pred l1" "get_terms l1"] l1_sign by auto
    (* Prove: Additionally, all the other literals in C'1 must be falsified by B, since they are falsified by B1, but not l'1. *)
    have B_C1'l1: "falsifiesg B (C1' - {l1})"
      proof
        fix lo
        assume other: "lo \<in> C1' - {l1}"
        from C1'_p have "falsifiesg ?B1 (C1' - {l1})" by auto
        then have loB1: "falsifiesl ?B1 lo" using other by auto
        moreover
        {
          have "l1\<noteq>lo" using other by auto
          then have "undiag_fatom l1 \<noteq> undiag_fatom lo" sorry
          then have "undiag_fatom lo \<noteq> length B" using l1_no by auto
          moreover
          {
            obtain i where "diag_fatom i = Pos (get_pred lo) (get_terms lo) \<and> i < length (B @ [True])" using loB1 by (cases lo) auto
            then have "undiag_fatom (diag_fatom i) = undiag_fatom (Pos (get_pred lo) (get_terms lo)) \<and> i < length (B @ [True])" by auto
            then have "undiag_fatom (Pos (get_pred lo) (get_terms lo)) < length (B @ [True])" using undiag_diag_fatom by auto
            then have "undiag_fatom lo < length (B @ [True])" using undiag_neg by (cases lo) auto
            then have "undiag_fatom lo < length B + 1" by auto
          }
          ultimately have "undiag_fatom lo < length B" using loB1 by auto
        }
        ultimately show "falsifiesl B lo" using shorter_falsifiesl by blast
      qed

    have "\<exists>C2 \<in> Cs. falsifiesc ?B2 C2" using b_p clo by auto (* "Re-formulation" of below line *)
    then obtain C2 where C2_p: "C2 \<in> Cs \<and> falsifiesc ?B2 C2" by auto
    then have "\<exists>C2'. groundls C2' \<and> instance_ofls C2' C2 \<and> falsifiesg ?B2 C2'" 
      using falsifiesc_ground[of C2 ?B2] by metis
    then obtain C2' where C2'_p: "groundls C2' \<and> instance_ofls C2' C2 \<and> falsifiesg ?B2 C2'" by auto
    (* We went down to the ground world *)
    then have "\<forall>l \<in> C2'. falsifiesl (B@[False]) l" by auto
    moreover 
    have "\<not>falsifiesc B C2" using C2_p b_p clo by auto
    then have "\<not> falsifiesg B C2'" using C2'_p by auto
    then have "\<not>(\<forall>l \<in> C2'. falsifiesl B l)" by auto
    ultimately have "\<exists>l \<in> C2'. falsifiesl (B@[False]) l \<and> \<not>(falsifiesl B l)" by auto
    then obtain l2 where l2_p: "l2 \<in> C2' \<and> falsifiesl (B@[False]) l2 \<and> \<not>(falsifiesl B l2)" by auto
    
    have l2_no: "undiag_fatom l2 = length B" sorry
    have l2_sign: "sign l2 = True" sorry
    have B_C2'l2:"falsifiesg B (C2' - {l2})" sorry

    have "falsifiesg B ((C1' - {l1}) \<union> (C2' - {l2}))" using B_C1'l1 B_C2'l2 by cases auto
    then have "falsifiesg B (lresolution C1' C2' {l1} {l2} \<epsilon>)" unfolding lresolution_def empty_subls by auto

    have "applicable C1' C2' {l1} {l2} \<epsilon>" using sorry
...x.

    (* Challange: standardize C1 and C2 apart, you need to do this very early *)
    have "\<exists>L1 L2 \<tau>. applicable C1 C2 L1 L2 \<tau>  \<and> instance_ofls (lresolution C1' C2' {l1} {l2} \<epsilon>) (lresolution C1 C2 L1 L2 \<tau>)" 
      using lifting[of C1 C2 C1' C2' "{l1}" "{l2}" \<epsilon>] sorry



    (*
    from C1_p have "\<forall>l \<in> C1. falsifiesl (B@[True]) l" by auto
    moreover have "\<not>(\<forall>l \<in> C1. falsifiesl B l)" using C1_p b_p clo by auto
    ultimately have "\<exists>l \<in> C1. falsifiesl (B@[True]) l \<and> \<not>(falsifiesl B l)" by auto
    then obtain l where l_p: "l \<in> C1 \<and> falsifiesl (B@[True]) l \<and> \<not>(falsifiesl B l)" by auto
    then have "\<exists>l'. instance_ofl l' l \<and> falsifiesl (B@[True]) l' \<and> groundl l'" using falsifies_ground_sub by blast
    then obtain l' where l'_p: "instance_ofl l' l \<and> falsifiesl (B@[True]) l' \<and> groundl l'" by auto
    then have "\<not>(falsifiesl B l')" using l_p partial_equiv_subst' unfolding instance_ofl_def by blast
    then have "\<not>(\<exists>i.  
      i < length B
      \<and> B ! i = (\<not>sign l')
      \<and> diag_fatom i = Pos (get_pred l') (get_terms l'))" using instance_ofts_self by (induction l') auto
    then have "\<not>(\<exists>i.  
      i < length B
      \<and> (B@[True]) ! i = (\<not>sign l')
      \<and> diag_fatom i = Pos (get_pred l') (get_terms l'))" by (metis nth_append) 
    moreover 
    have "\<exists>i.  
      i < length (B@[True])
      \<and> (B@[True]) ! i = (\<not>sign l')
      \<and> diag_fatom i = Pos (get_pred l') (get_terms l')" using ground_falsifies l'_p by blast
    ultimately
    have ggg: "(B@[True]) ! (length B) = (\<not>sign l') \<and> diag_fatom (length B) = Pos (get_pred l') (get_terms l')"
      using number_lemma[of B "\<lambda>i. (B @ [True]) ! i = (\<not> sign l') \<and> diag_fatom i = Pos (get_pred l') (get_terms l')"] by auto
    then have sss: "sign l' = False" by auto
    from ggg have "undiag_fatom (Pos (get_pred l') (get_terms l')) = length B" using undiag_diag_fatom by metis
    then have "undiag_fatom l' = length B" using undiag_neg[of "get_pred l'" "get_terms l'"] sss by auto
    (* Prove: Additionally, all the other literals in C'1 must be falsified by B, since they are falsified by B1, but not l'1. *)
    *)


    have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" sorry
  }
  ultimately show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" by auto
oops

theorem completeness:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>F G. \<not>evalcs F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
oops

end