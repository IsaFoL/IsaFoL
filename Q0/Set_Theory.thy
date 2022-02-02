theory Set_Theory imports Main begin

(*
  This is the set theory from 
  https://github.com/CakeML/cakeml/blob/master/candle/set-theory/setSpecScript.sml
  ported to Isabelle/HOL.
*)

locale set_theory =
  fixes mem :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix "\<in>:" 67)
  fixes sub :: "'s \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's" (infix "suchthat" 67)
  fixes pow :: "'s \<Rightarrow> 's"
  fixes uni :: "'s \<Rightarrow> 's" ("\<Union>:_" [900] 900)
  fixes upair :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infix "+:" 67)
  assumes extensional: "\<And>x y. x = y \<longleftrightarrow> (\<forall>a. a \<in>: x \<longleftrightarrow> a \<in>: y)"
  assumes mem_sub[simp]: "\<And>x P a. a \<in>: (x suchthat P) \<longleftrightarrow> a \<in>: x \<and> P a"
  assumes mem_pow[simp]: "\<And>x a. a \<in>: (pow x) \<longleftrightarrow> (\<forall>b. b \<in>: a \<longrightarrow> b \<in>: x)"
  assumes mem_uni[simp]: "\<And>x a. a \<in>: \<Union>:x \<longleftrightarrow> (\<exists>b. a \<in>: b \<and> b \<in>: x)"
  assumes mem_upair[simp]: "\<And>x y a. a \<in>: (x +: y) \<longleftrightarrow> a = x \<or> a = y" 
begin

lemma seperation_unique:
  assumes "\<forall>x P a. a \<in>: (sub2 x P) \<longleftrightarrow> a \<in>: x \<and> P a"
  shows "sub2 = sub"
  apply rule
  using assms extensional by auto

lemma pow_unique:
  assumes "\<forall>x a. a \<in>: (pow2 x) \<longleftrightarrow> (\<forall>b. b \<in>: a \<longrightarrow> b \<in>: x)"
  shows "pow2 = pow"
  using assms extensional by auto

lemma uni_unique:
  assumes "\<forall>x a. a \<in>: uni2 x \<longleftrightarrow> (\<exists>b. a \<in>: b \<and> b \<in>: x)"
  shows "uni2 = uni"
  using assms extensional by auto

lemma upair_unique:
  assumes "\<forall>x y a. a \<in>: upair2 x y \<longleftrightarrow> a = x \<or> a = y"
  shows "upair2 = upair"
  apply rule
  using assms extensional by auto

definition empt :: 's ("Ø") where
 "Ø = undefined suchthat (\<lambda>x. False)" 

lemma mem_empty[simp]: "\<not>x \<in>: Ø"
  unfolding empt_def using mem_sub by auto

definition unit :: "'s \<Rightarrow> 's" where
  "unit x = x +: x"

lemma mem_unit[simp]: "x \<in>: (unit y) \<longleftrightarrow> x = y"
  unfolding unit_def using mem_upair by auto

lemma unit_inj: "unit x = unit y \<longleftrightarrow> x = y"
  using extensional unfolding unit_def by auto 

definition one :: 's where
  "one = unit Ø"

lemma mem_one[simp]: "x \<in>: one \<longleftrightarrow> x = Ø"
  unfolding one_def by auto

definition two :: 's where
  "two = Ø +: one"

lemma mem_two[simp]: "\<forall>x. x \<in>: two \<longleftrightarrow> x = Ø \<or> x = one"
  unfolding two_def by auto 

definition pair :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infix ",:" 50) where
  "(x,:y) = (unit x) +: (x +: y)"

lemma upair_inj:
  "a +: b = c +: d \<longleftrightarrow> a = c \<and> b = d \<or> a = d \<and> b = c"
  using extensional by auto

lemma unit_eq_upair:
  "unit x = y +: z \<longleftrightarrow> x = y \<and> y = z"
  using extensional mem_unit mem_upair by metis

lemma pair_inj:
  "(a,:b) = (c,:d) \<longleftrightarrow> a = c \<and> b = d"
  using pair_def upair_inj unit_inj unit_eq_upair by metis

definition binary_uni (infix "\<union>:" 67) where
  "x \<union>: y = \<Union>: (x +: y)"

lemma mem_binary_uni[simp]:
  "a \<in>: (x \<union>: y) \<longleftrightarrow> a \<in>: x \<or> a \<in>: y"
  unfolding binary_uni_def by auto

definition product :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infix "\<times>:" 67) where
  "x \<times>: y = (pow (pow (x \<union>: y)) suchthat (\<lambda>a. \<exists>b c. b \<in>: x \<and> c \<in>: y \<and> a = (b,:c)))"

lemma mem_product[simp]:
  "a \<in>: (x \<times>: y) \<longleftrightarrow> (\<exists>b c. a = (b,:c) \<and> b \<in>: x \<and> c \<in>: y)"
  using product_def pair_def by auto

definition relspace where
  "relspace x y = pow (x \<times>: y)"

definition funspace where
  "funspace x y =
    (relspace x y suchthat
     (\<lambda>f. \<forall>a. a \<in>: x \<longrightarrow> (\<exists>!b. (a,:b) \<in>: f)))"

definition "apply" :: "'s \<Rightarrow> 's \<Rightarrow> 's" ("_\<langle>_\<rangle>" [68,68] 68) where
  "(x\<langle>y\<rangle>) = (SOME a. (y,:a) \<in>: x)"

definition boolset where
  "boolset \<equiv> two"

definition true where
  "true = Ø"

definition false where
  "false = one"

lemma true_neq_false:
  "true \<noteq> false"
  using true_def false_def extensional one_def by auto

lemma mem_boolset[simp]:
  "x \<in>: boolset \<longleftrightarrow> ((x = true) \<or> (x = false))"
  using true_def false_def boolset_def by auto

definition boolean :: "bool \<Rightarrow> 's" where
  "boolean b = (if b then true else false)"

lemma boolean_in_boolset:
  "boolean b \<in>: boolset"
  using boolean_def one_def true_def false_def by auto

lemma boolean_eq_true:
  "boolean b = true \<longleftrightarrow> b"
  using boolean_def true_neq_false by auto

definition "holds s x \<longleftrightarrow> s\<langle>x\<rangle> = true"

definition abstract where
  "abstract doma rang f = ((doma \<times>: rang) suchthat (\<lambda>x. \<exists>a. x = (a,:f a)))"

lemma apply_abstract[simp]:
  "x \<in>: s \<Longrightarrow> f x \<in>: t \<Longrightarrow> (abstract s t f)\<langle>x\<rangle> = f x"
  using apply_def abstract_def pair_inj by auto

lemma apply_abstract_matchable:
  "x \<in>: s \<Longrightarrow> f x \<in>: t \<Longrightarrow> f x = u \<Longrightarrow> (abstract s t f)\<langle>x\<rangle> = u"
  using apply_abstract by auto

lemma apply_in_rng:
  assumes "x \<in>: s"
  assumes "f \<in>: funspace s t"
  shows "f\<langle>x\<rangle> \<in>: t"
proof -
  from assms have "f \<in>: (relspace s t suchthat (\<lambda>f. \<forall>a. a \<in>: s \<longrightarrow> (\<exists>!b. (a ,: b) \<in>: f)))"
    unfolding funspace_def by auto
  then have f_p: "f \<in>: relspace s t \<and> (\<forall>a. a \<in>: s \<longrightarrow> (\<exists>!b. (a ,: b) \<in>: f))"
    by auto
  then have fxf: "(x ,: f\<langle>x\<rangle>) \<in>: f"
    using someI assms apply_def by metis
  from f_p have "f \<in>: pow (s \<times>: t)"
    unfolding relspace_def by auto
  then have "(x ,: f\<langle>x\<rangle>) \<in>: (s \<times>: t)"
    using fxf by auto
  then show ?thesis
    using pair_inj by auto
qed

lemma abstract_in_funspace[simp]:
  "(\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t) \<Longrightarrow> abstract s t f \<in>: funspace s t"
  using funspace_def relspace_def abstract_def pair_inj by auto
 
lemma abstract_in_funspace_matchable:
  "(\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t) \<Longrightarrow> fs = funspace s t \<Longrightarrow> abstract s t f \<in>: fs"
  using abstract_in_funspace by auto

lemma abstract_eq:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t1 \<and> g x \<in>: t2 \<and> f x = g x"
  shows "abstract s t1 f = abstract s t2 g"
proof (rule iffD2[OF extensional], rule)
  fix a
  from assms show "a \<in>: abstract s t1 f = a \<in>: abstract s t2 g"
    unfolding abstract_def using pair_inj by auto
qed

lemma abstract_eq_7891244237890417890:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> f x = g x"
  shows "abstract s t f = abstract s t g"
proof (rule iffD2[OF extensional], rule)
  fix a
  from assms show "a \<in>: abstract s t f = a \<in>: abstract s t g"
    unfolding abstract_def using pair_inj by auto
qed

lemma abstract_eq_789124423789041789012367813:
  assumes "\<And>x. x \<in>: s \<Longrightarrow> f x \<in>: t"
  assumes "\<And>x. x \<in>: s \<Longrightarrow> f x = g x"
  shows "abstract s t f = abstract s t g"
proof (rule iffD2[OF extensional], rule)
  fix a
  from assms show "a \<in>: abstract s t f = a \<in>: abstract s t g"
    unfolding abstract_def using pair_inj by auto
qed

lemma abstract_eq_789124423789041394239843487329487890:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> g x \<in>: t"
  assumes "abstract s t f = abstract s t g"
  assumes "x \<in>: s"
  shows "f x = g x"
  using assms
  by (metis apply_abstract_matchable)

lemma abstract_eq_78912442378904178901289321783617:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> g x \<in>: t"
  shows "(abstract s t f = abstract s t g) \<longleftrightarrow> (\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> f x = g x)"
  using assms abstract_eq_789124423789041394239843487329487890
    abstract_eq_7891244237890417890 by meson

lemma in_funspace_abstract[simp]:
  assumes "z \<in>: funspace s t"
  shows "\<exists>f. z = abstract s t f \<and> (\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t)"
proof -
  define f where "f = (\<lambda>x. SOME y. (x,:y) \<in>: z)"
  then have "\<forall>x. x \<in>: z \<longleftrightarrow> x \<in>: (abstract s t f)"
    using assms apply clarify
    unfolding funspace_def
    apply auto unfolding relspace_def
    unfolding mem_pow
     apply auto
    unfolding abstract_def apply auto
     apply (metis pair_inj someI_ex)+
    done
  then have "z = abstract s t f"
    using extensional by auto
  moreover
  from f_def have "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t"
    using assms apply auto
    unfolding funspace_def
    apply auto
    unfolding relspace_def
    unfolding mem_pow
    apply auto
    apply (metis pair_inj someI_ex)+
    done
  ultimately
  show ?thesis
    by auto   
qed

theorem axiom_of_choice:
  assumes "\<forall>a. a \<in>: x \<longrightarrow> (\<exists>b. b \<in>: a)"
  shows "\<exists>f. \<forall>a. a \<in>: x \<longrightarrow> (f\<langle>a\<rangle>) \<in>: a"
proof -
  define f where "f = (\<lambda>a. SOME b. mem b a)"
  define fa where "fa = abstract x (uni x) f"

  have "\<forall>a. a \<in>: x \<longrightarrow> (fa\<langle>a\<rangle>) \<in>: a"
  proof (rule, rule)
    fix a
    assume "a \<in>: x"
    moreover
    have "f a \<in>: \<Union>:x"
      by (metis (full_types) assms calculation f_def mem_uni someI_ex)
    moreover
    have "f a \<in>: a"
      using assms calculation(1) f_def someI_ex by force
    ultimately
    show "(fa\<langle>a\<rangle>) \<in>: a"
      unfolding fa_def using apply_abstract by auto
  qed
  then show ?thesis
    by auto
qed

definition is_infinite where
  "is_infinite s = infinite {a. a \<in>: s}"

lemma funspace_inhabited:
  "(\<exists>x. x \<in>: s) \<Longrightarrow> (\<exists>x. x \<in>: t) \<Longrightarrow> (\<exists>f. f \<in>: funspace s t)"
  apply (rule_tac x="abstract s t (\<lambda>x. SOME x. x \<in>: t)" in exI)
  using abstract_in_funspace
  using someI by metis 

fun tuple where
  "tuple [] = Ø" |
  "tuple (a#as) = (a,: tuple as)"

lemma pair_not_empty:
  "(x,:y) \<noteq> Ø"
  apply rule
  unfolding extensional using mem_empty pair_def mem_upair by metis

lemma tuple_empty:
  "tuple ls = Ø \<longleftrightarrow> ls = []"
  using pair_not_empty by (cases ls) auto

lemma tuple_inj:
  "tuple l1 = tuple l2 \<longleftrightarrow> l1 = l2"
  apply (induction l1 arbitrary: l2)
  using tuple_empty pair_not_empty pair_inj
   apply metis
  using tuple_empty pair_not_empty pair_inj
  by (metis tuple.elims tuple.simps(2))

fun bigcross where
  "bigcross [] = one" |
  "bigcross (a#as) = a \<times>: (bigcross as)"

lemma mem_bigcross[simp]:
  "x \<in>: (bigcross ls) \<longleftrightarrow> (\<exists>xs. x = tuple xs \<and> list_all2 mem xs ls)"
proof (induction ls arbitrary: x)
  case Nil
  then show ?case 
    using mem_one mem_product by simp
next
  case (Cons l ls)
  show ?case 
  proof
    assume "x \<in>: bigcross (l # ls)"
    then obtain b c where bc_p: "x = (b ,: c) \<and> b \<in>: l \<and> c \<in>: bigcross ls " 
      by auto
    then obtain xs' where "c = tuple xs' \<and> list_all2 (\<in>:) xs' ls" 
      using Cons[of c] by auto
    then have "x = tuple (b#xs') \<and> list_all2 (\<in>:) (b#xs') (l # ls)"
      using bc_p by auto
    then show "\<exists>xs. x = tuple xs \<and> list_all2 (\<in>:) xs (l # ls)"
      by metis
  next 
    assume "\<exists>xs. x = tuple xs \<and> list_all2 (\<in>:) xs (l # ls)"
    then obtain xs where "x = tuple xs \<and> list_all2 (\<in>:) xs (l # ls)"
      by auto
    then obtain xs where "x = tuple xs \<and> list_all2 (\<in>:) xs (l # ls)"
      by auto
    then show "x \<in>: bigcross (l # ls)"
      using Cons
      by (smt list_all2_Cons2 set_theory.bigcross.simps(2) set_theory.mem_product set_theory_axioms tuple.simps(2))
  qed
qed

definition subs :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix "\<subseteq>:" 67) where
  "x \<subseteq>: y \<longleftrightarrow> x \<in>: pow y"

end

(* weak model = with infinite, but without ch (which is in "model") *)
locale weak_model = set_theory _ _ pow
  for pow :: "'u \<Rightarrow> 'u" +
  fixes ch :: "'u \<Rightarrow> 'u"
  fixes indset :: "'u"
  assumes infinite: "is_infinite indset"
begin

lemma indset_inhabited:
  "\<exists>i. i \<in>: indset"
  using infinite unfolding is_infinite_def using infinite_imp_nonempty by auto

(* defines the identity function on its argument (definition from CakeML paper)*)
definition iden :: "'u \<Rightarrow> 'u" where
  "iden = (\<lambda>D. abstract D (funspace D boolset) (\<lambda>x. abstract D boolset (\<lambda>y. boolean (x = y))))"

lemma apply_id[simp]:
  assumes A_in_D: "A \<in>: D"
  assumes B_in_D: "B \<in>: D"
  shows "(iden D)\<langle>A\<rangle>\<langle>B\<rangle> = boolean (A = B)"
proof -
  have abstract_D: "abstract D boolset (\<lambda>y. boolean (A = y)) \<in>: funspace D boolset"
    using boolean_in_boolset by auto
  have bool_in_two: "boolean (A = B) \<in>: boolset"
    using boolean_in_boolset by blast
  have "(boolean (A = B)) = (abstract D boolset (\<lambda>y. boolean (A = y))\<langle>B\<rangle>)"
    using apply_abstract[of B D "\<lambda>y. boolean (A = y)" two] B_in_D bool_in_two by auto
  also
  have "... = (abstract D (funspace D boolset) (\<lambda>x. abstract D boolset (\<lambda>y. boolean (x = y))))\<langle>A\<rangle>\<langle>B\<rangle>" 
    using A_in_D abstract_D apply_abstract[of A D "(\<lambda>x. abstract D boolset (\<lambda>y. boolean (x = y)))" "(funspace D boolset)"] by auto 
  also
  have "... = (iden D)\<langle>A\<rangle>\<langle>B\<rangle> "
    unfolding iden_def ..
  finally
  show ?thesis
    by auto
qed

lemma apply_id_true[simp]:
  assumes A_in_D: "A \<in>: D"
  assumes B_in_D: "B \<in>: D"
  shows "(iden D)\<langle>A\<rangle>\<langle>B\<rangle> = true \<longleftrightarrow> A = B"
  using assms using boolean_def using true_neq_false by auto

definition one_elem_fun :: "'u \<Rightarrow> 'u \<Rightarrow> 'u" where
  "one_elem_fun x d = abstract d boolset (\<lambda>y. boolean (x=y))"

lemma new_lemma12345667:
  assumes "x \<in>: s"
  assumes "f x \<in>: t"
  assumes "abstract s t f = abstract s t g"
  assumes "g x \<in>: t"
  shows "f x = g x"
proof -
  from assms(2) have fx_in_t: "f x \<in>: t"
    by auto (* add to shows? Or seperate lemma. *)

  from assms have gx_in_t: "g x \<in>: t"
    by auto (* add to shows? Or seperate lemma. *)

  have "f x = (abstract s t f)\<langle>x\<rangle>"
    using apply_abstract[of x s f t]
    using fx_in_t assms by auto
  also have "... = abstract s t g\<langle>x\<rangle>"
    using assms by auto
  also have "... = g x"
    using apply_abstract[of x s g t]
    using gx_in_t assms by auto
  finally show ?thesis 
    by auto
qed

lemma pair_in_apply_jfljalkfdjlkfja:
  assumes "(a1,: a2) \<in>: f"
  assumes "f \<in>: funspace s t"
  shows "f\<langle>a1\<rangle> = a2"
  using assms
  by (smt abstract_def apply_abstract mem_product pair_inj set_theory.in_funspace_abstract set_theory.mem_sub set_theory_axioms) 

lemma two_pairs_same_jakldajfdlkf:
  assumes "f \<in>: funspace s t"
  assumes "(a1,: a2) \<in>: f"
  assumes "(a1,: a3) \<in>: f"
  shows "a3 = a2"
  using assms pair_in_apply_jfljalkfdjlkfja by blast

lemma new_lemma_57623741902839035487410245298:
  assumes "f \<in>: funspace s t"
  assumes "g \<in>: funspace s t"
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f\<langle>x\<rangle> = g\<langle>x\<rangle>"
  shows "f = g"
proof -
  have "\<And>a. a \<in>: f \<Longrightarrow> a \<in>: g"
  proof -
    fix a
    assume a: "a \<in>: f"
    from a have b: "\<exists>a1 a2. a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      using assms unfolding funspace_def apply_def using relspace_def by force
    then obtain a1 a2 where as:
      "a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      by blast
    then have "\<exists>a3. a2 \<in>: t \<and> (a1 ,: a3) \<in>: g"
      using assms(2) funspace_def by auto
    then obtain a3 where as2: "a2 \<in>: t \<and> (a1 ,: a3) \<in>: g"
      by auto
    then have "a3 = a2"
      using as a assms(1) assms(2) assms(3) pair_in_apply_jfljalkfdjlkfja by auto
    then show "a \<in>: g"
      using as as2 by blast
  qed
  moreover
  have "\<And>a. a \<in>: g \<Longrightarrow> a \<in>: f"
  proof -
    fix a
    assume a: "a \<in>: g"
    from a have b: "\<exists>a1 a2. a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      using assms unfolding funspace_def apply_def using relspace_def by force
    then obtain a1 a2 where as:
      "a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      by blast
    then have "\<exists>a3. a2 \<in>: t \<and> (a1 ,: a3) \<in>: f"
      using assms(1) funspace_def by auto
    then obtain a3 where as2: "a2 \<in>: t \<and> (a1 ,: a3) \<in>: f"
      by auto
    then have "a3 = a2"
      using as a assms(1) assms(2) assms(3) pair_in_apply_jfljalkfdjlkfja by auto
    then show "a \<in>: f"
      using as as2 by blast
  qed
  ultimately
  show ?thesis 
    using iffD2[OF extensional] by metis
qed

end

locale model = weak_model +
  assumes is_choice: "\<forall>x. (\<exists>a. a \<in>: x) \<longrightarrow> ch x \<in>: x"
begin

end

end