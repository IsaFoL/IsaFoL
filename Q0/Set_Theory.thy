theory Set_Theory imports Main begin
(*

CakeML Copyright Notice, License, and Disclaimer.

Copyright 2013-2023 by Anthony Fox, Google LLC, Ramana Kumar, Magnus Myreen,
Michael Norrish, Scott Owens, Yong Kiam Tan, and other contributors listed
at https://cakeml.org

All rights reserved.

CakeML is free software. Redistribution and use in source and binary forms,
with or without modification, are permitted provided that the following
conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.

    * The names of the copyright holders and contributors may not be
      used to endorse or promote products derived from this software without
      specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS IS''
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

(*
  This formal document is the set theory from 
  https://github.com/CakeML/cakeml/blob/master/candle/set-theory/setSpecScript.sml
  ported to Isabelle/HOL and extended.
*)

(* Corresponds to CakeML's constant is_set_theory_def *)
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

(* Corresponds to CakeML's theorem separation_unique *)
lemma seperation_unique:
  assumes "\<forall>x P a. a \<in>: (sub2 x P) \<longleftrightarrow> a \<in>: x \<and> P a"
  shows "sub2 = sub"
proof
  fix x
  show "sub2 x = (suchthat) x"
    using assms extensional by auto
qed

(* Corresponds to CakeML's theorem power_unique *)
lemma pow_unique:
  assumes "\<forall>x a. a \<in>: (pow2 x) \<longleftrightarrow> (\<forall>b. b \<in>: a \<longrightarrow> b \<in>: x)"
  shows "pow2 = pow"
  using assms extensional by auto

(* Corresponds to CakeML's theorem union_unique *)
lemma uni_unique:
  assumes "\<forall>x a. a \<in>: uni2 x \<longleftrightarrow> (\<exists>b. a \<in>: b \<and> b \<in>: x)"
  shows "uni2 = uni"
  using assms extensional by auto

(* Corresponds to CakeML's theorem upair_unique *)
lemma upair_unique:
  assumes "\<forall>x y a. a \<in>: upair2 x y \<longleftrightarrow> a = x \<or> a = y"
  shows "upair2 = upair"
proof 
  fix x 
  show "upair2 x = (+:) x"
    using assms extensional by auto
qed

(* Corresponds to CakeML's Ø *)
definition empt :: 's ("Ø") where
 "Ø = undefined suchthat (\<lambda>x. False)" 

(* Corresponds to CakeML's theorem mem_empty *)
lemma mem_empty[simp]: "\<not>x \<in>: Ø"
  unfolding empt_def using mem_sub by auto

(* Corresponds to CakeML's constant unit *)
definition unit :: "'s \<Rightarrow> 's" where
  "unit x = x +: x"

(* Corresponds to CakeML's theorem mem_unit *)
lemma mem_unit[simp]: "x \<in>: (unit y) \<longleftrightarrow> x = y"
  unfolding unit_def using mem_upair by auto

(* Corresponds to CakeML's theorem unit_inj *)
lemma unit_inj: "unit x = unit y \<longleftrightarrow> x = y"
  using extensional unfolding unit_def by auto 

(* Corresponds to CakeML's constant one *)
definition one :: 's where
  "one = unit Ø"

(* Corresponds to CakeML's theorem mem_one *)
lemma mem_one[simp]: "x \<in>: one \<longleftrightarrow> x = Ø"
  unfolding one_def by auto

(* Corresponds to CakeML's constant two *)
definition two :: 's where
  "two = Ø +: one"

(* Corresponds to CakeML's theorem mem_two *)
lemma mem_two[simp]: "\<forall>x. x \<in>: two \<longleftrightarrow> x = Ø \<or> x = one"
  unfolding two_def by auto 

(* Corresponds to CakeML's constant pair *)
definition pair :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infix ",:" 50) where
  "(x,:y) = (unit x) +: (x +: y)"

(* Corresponds to CakeML's theorem upair_inj *)
lemma upair_inj:
  "a +: b = c +: d \<longleftrightarrow> a = c \<and> b = d \<or> a = d \<and> b = c"
  using extensional by auto

(* Corresponds to CakeML's theorem unit_eq_upair *)
lemma unit_eq_upair:
  "unit x = y +: z \<longleftrightarrow> x = y \<and> y = z"
  using extensional mem_unit mem_upair by metis

(* Corresponds to CakeML's theorem pair_inj *)
lemma pair_inj:
  "(a,:b) = (c,:d) \<longleftrightarrow> a = c \<and> b = d"
  using pair_def upair_inj unit_inj unit_eq_upair by metis

(* Corresponds to CakeML's constant binary_uni *)
definition binary_uni (infix "\<union>:" 67) where
  "x \<union>: y = \<Union>: (x +: y)"

(* Corresponds to CakeML's theorem mem_binary_uni *)
lemma mem_binary_uni[simp]:
  "a \<in>: (x \<union>: y) \<longleftrightarrow> a \<in>: x \<or> a \<in>: y"
  unfolding binary_uni_def by auto

(* Corresponds to CakeML's constant product *)
definition product :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infix "\<times>:" 67) where
  "x \<times>: y = (pow (pow (x \<union>: y)) suchthat (\<lambda>a. \<exists>b c. b \<in>: x \<and> c \<in>: y \<and> a = (b,:c)))"

(* Corresponds to CakeML's theorem mem_product *)
lemma mem_product[simp]:
  "a \<in>: (x \<times>: y) \<longleftrightarrow> (\<exists>b c. a = (b,:c) \<and> b \<in>: x \<and> c \<in>: y)"
  using product_def pair_def by auto

(* Corresponds to CakeML's constant product *)
definition relspace where
  "relspace x y = pow (x \<times>: y)"

(* Corresponds to CakeML's constant funspace *)
definition funspace where
  "funspace x y =
    (relspace x y suchthat
     (\<lambda>f. \<forall>a. a \<in>: x \<longrightarrow> (\<exists>!b. (a,:b) \<in>: f)))"

(* Corresponds to CakeML's constant apply *)
definition "apply" :: "'s \<Rightarrow> 's \<Rightarrow> 's" ("_\<langle>_\<rangle>" [68,68] 68) where
  "(x\<langle>y\<rangle>) = (SOME a. (y,:a) \<in>: x)"

(* Corresponds to CakeML's overloading of boolset *)
definition boolset where
  "boolset \<equiv> two"

(* Corresponds to CakeML's constant true *)
definition true where
  "true = Ø"

(* Corresponds to CakeML's constant false *)
definition false where
  "false = one"

(* Corresponds to CakeML's theorem true_neq_false *)
lemma true_neq_false:
  "true \<noteq> false"
  using true_def false_def extensional one_def by auto

(* Corresponds to CakeML's theorem mem_boolset *)
lemma mem_boolset[simp]:
  "x \<in>: boolset \<longleftrightarrow> ((x = true) \<or> (x = false))"
  using true_def false_def boolset_def by auto

(* Corresponds to CakeML's constant boolean *)
definition boolean :: "bool \<Rightarrow> 's" where
  "boolean b = (if b then true else false)"

(* Corresponds to CakeML's theorem boolean_in_boolset *)
lemma boolean_in_boolset:
  "boolean b \<in>: boolset"
  using boolean_def one_def true_def false_def by auto

(* Corresponds to CakeML's theorem boolean_eq_true *)
lemma boolean_eq_true:
  "boolean b = true \<longleftrightarrow> b"
  using boolean_def true_neq_false by auto

(* Corresponds to CakeML's constant holds *)
definition "holds s x \<longleftrightarrow> s\<langle>x\<rangle> = true"

(* Corresponds to CakeML's constant abstract *)
definition abstract where
  "abstract doma rang f = ((doma \<times>: rang) suchthat (\<lambda>x. \<exists>a. x = (a,:f a)))"

(* Corresponds to CakeML's theorem apply_abstract *)
lemma apply_abstract[simp]:
  "x \<in>: s \<Longrightarrow> f x \<in>: t \<Longrightarrow> (abstract s t f)\<langle>x\<rangle> = f x"
  using apply_def abstract_def pair_inj by auto

(* Corresponds to CakeML's theorem apply_abstract_matchable *)
lemma apply_abstract_matchable:
  "x \<in>: s \<Longrightarrow> f x \<in>: t \<Longrightarrow> f x = u \<Longrightarrow> (abstract s t f)\<langle>x\<rangle> = u"
  using apply_abstract by auto

(* Corresponds to CakeML's theorem apply_in_rng *)
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

(* Corresponds to CakeML's theorem abstract_in_funspace  *)
lemma abstract_in_funspace[simp]:
  "(\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t) \<Longrightarrow> abstract s t f \<in>: funspace s t"
  using funspace_def relspace_def abstract_def pair_inj by auto

(* Corresponds to CakeML's theorem abstract_in_funspace_matchable *)
lemma abstract_in_funspace_matchable:
  "(\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t) \<Longrightarrow> fs = funspace s t \<Longrightarrow> abstract s t f \<in>: fs"
  using abstract_in_funspace by auto

(* Corresponds to CakeML's theorem abstract_eq *)
lemma abstract_eq:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t1 \<and> g x \<in>: t2 \<and> f x = g x"
  shows "abstract s t1 f = abstract s t2 g"
proof (rule iffD2[OF extensional], rule)
  fix a
  from assms show "a \<in>: abstract s t1 f = a \<in>: abstract s t2 g"
    unfolding abstract_def using pair_inj by auto
qed

lemma abstract_extensional:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> f x = g x"
  shows "abstract s t f = abstract s t g"
proof (rule iffD2[OF extensional], rule)
  fix a
  from assms show "a \<in>: abstract s t f = a \<in>: abstract s t g"
    unfolding abstract_def using pair_inj by auto
qed

lemma abstract_extensional':
  assumes "\<And>x. x \<in>: s \<Longrightarrow> f x \<in>: t"
  assumes "\<And>x. x \<in>: s \<Longrightarrow> f x = g x"
  shows "abstract s t f = abstract s t g"
proof (rule iffD2[OF extensional], rule)
  fix a
  from assms show "a \<in>: abstract s t f = a \<in>: abstract s t g"
    unfolding abstract_def using pair_inj by auto
qed

lemma abstract_cong:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> g x \<in>: t"
  assumes "abstract s t f = abstract s t g"
  assumes "x \<in>: s"
  shows "f x = g x"
  using assms
  by (metis apply_abstract_matchable)

lemma abstract_cong_specific:
  assumes "x \<in>: s"
  assumes "f x \<in>: t"
  assumes "abstract s t f = abstract s t g"
  assumes "g x \<in>: t"
  shows "f x = g x"
proof -
  have "f x = (abstract s t f)\<langle>x\<rangle>"
    using apply_abstract[of x s f t]
    using assms by auto
  also have "... = abstract s t g\<langle>x\<rangle>"
    using assms by auto
  also have "... = g x"
    using apply_abstract[of x s g t]
    using assms by auto
  finally show ?thesis 
    by auto
qed

lemma abstract_cong_extensional:
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> g x \<in>: t"
  shows "(abstract s t f = abstract s t g) \<longleftrightarrow> (\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t \<and> f x = g x)"
  using assms abstract_cong
    abstract_extensional by meson

(* Corresponds to CakeML's theorem in_funspace_abstract *)
lemma in_funspace_abstract[simp]:
  assumes "z \<in>: funspace s t"
  shows "\<exists>f. z = abstract s t f \<and> (\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t)"
proof -
  define f where "f = (\<lambda>x. SOME y. (x,:y) \<in>: z)"
  have "\<forall>x. x \<in>: z \<longleftrightarrow> x \<in>: (abstract s t f)"
  proof (rule, rule)
    fix x
    assume xz: "x \<in>: z"
    moreover
    have "\<forall>b. b \<in>: z \<longrightarrow> (\<exists>ba c. b = (ba ,: c) \<and> ba \<in>: s \<and> c \<in>: t)"
      using xz assms
      unfolding funspace_def relspace_def by (auto)
    moreover
    have "\<forall>a. a \<in>: s \<longrightarrow> (\<exists>!b. (a ,: b) \<in>: z)"
      using xz using assms
      unfolding funspace_def relspace_def by auto
    ultimately
    have "\<exists>a. x = (a ,: f a)"
      using assms f_def someI_ex unfolding funspace_def relspace_def by (metis (no_types, lifting))
    then show "x \<in>: abstract s t f"
      using xz assms unfolding funspace_def relspace_def abstract_def by auto
  next
    fix x 
    assume xf: "x \<in>: abstract s t f"
    then have "(\<exists>b c. x = (b ,: c) \<and> b \<in>: s \<and> c \<in>: t)"
      unfolding abstract_def by simp
    moreover
    have "(\<exists>a. x = (a ,: (SOME y. (a ,: y) \<in>: z)))"
      using xf f_def unfolding abstract_def by simp
    moreover
    have "(\<forall>a. a \<in>: s \<longrightarrow> (\<exists>!b. (a ,: b) \<in>: z))"
      using assms unfolding funspace_def by simp
    ultimately
    show "x \<in>: z"
      using f_def by (metis pair_inj someI_ex)
  qed
  then have "z = abstract s t f"
    using extensional by auto
  moreover
  from f_def have "\<forall>x. x \<in>: s \<longrightarrow> f x \<in>: t"
    using apply_in_rng assms local.apply_def by force
  ultimately
  show ?thesis
    by auto   
qed

(* Corresponds to CakeML's theorem axiom_of_choice *)
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

(* Corresponds to CakeML's constant is_infinite *)
definition is_infinite where
  "is_infinite s = infinite {a. a \<in>: s}"

(* Corresponds to CakeML's theorem funspace_inhabited *)
lemma funspace_inhabited:
  "(\<exists>x. x \<in>: s) \<Longrightarrow> (\<exists>x. x \<in>: t) \<Longrightarrow> (\<exists>f. f \<in>: funspace s t)"
  apply (rule_tac x="abstract s t (\<lambda>x. SOME x. x \<in>: t)" in exI)
  using abstract_in_funspace
  using someI by metis 

(* Corresponds to CakeML's constant tuple *)
fun tuple where
  "tuple [] = Ø" |
  "tuple (a#as) = (a,: tuple as)"

(* Corresponds to CakeML's theorem pair_not_empty *)
lemma pair_not_empty:
  "(x,:y) \<noteq> Ø"
  apply rule
  unfolding extensional using mem_empty pair_def mem_upair by metis

(* Corresponds to CakeML's theorem tuple_empty *)
lemma tuple_empty:
  "tuple ls = Ø \<longleftrightarrow> ls = []"
  using pair_not_empty by (cases ls) auto

(* Corresponds to CakeML's theorem tuple_inj *)
lemma tuple_inj:
  "tuple l1 = tuple l2 \<longleftrightarrow> l1 = l2"
proof (induction l1 arbitrary: l2)
  case Nil
  then show ?case 
    using tuple_empty by metis
next
  case (Cons a l1)
  then show ?case
    using pair_not_empty pair_inj by (metis tuple.elims tuple.simps(2))
qed

(* Corresponds to CakeML's constant bigcross *)
fun bigcross where
  "bigcross [] = one" |
  "bigcross (a#as) = a \<times>: (bigcross as)"

(* Corresponds to CakeML's theorem mem_bigcross *)
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
      using Cons list.distinct(1) list.rel_cases mem_product by fastforce
  qed
qed

definition subs :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix "\<subseteq>:" 67) where
  "x \<subseteq>: y \<longleftrightarrow> x \<in>: pow y"

(* defines the identity function on its argument (definition from CakeML) *)
definition iden :: "'s \<Rightarrow> 's" where
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
    using A_in_D abstract_D 
      apply_abstract[of A D "(\<lambda>x. abstract D boolset (\<lambda>y. boolean (x = y)))" "(funspace D boolset)"]
    by auto 
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

definition one_elem_fun :: "'s \<Rightarrow> 's \<Rightarrow> 's" where
  "one_elem_fun x d = abstract d boolset (\<lambda>y. boolean (x=y))"

lemma apply_if_pair_in:
  assumes "(a1,: a2) \<in>: f"
  assumes "f \<in>: funspace s t"
  shows "f\<langle>a1\<rangle> = a2"
  using assms
  by (smt abstract_def apply_abstract mem_product pair_inj set_theory.in_funspace_abstract 
      set_theory.mem_sub set_theory_axioms)

lemma funspace_app_unique:
  assumes "f \<in>: funspace s t"
  assumes "(a1,: a2) \<in>: f"
  assumes "(a1,: a3) \<in>: f"
  shows "a3 = a2"
  using assms apply_if_pair_in by blast

lemma funspace_extensional:
  assumes "f \<in>: funspace s t"
  assumes "g \<in>: funspace s t"
  assumes "\<forall>x. x \<in>: s \<longrightarrow> f\<langle>x\<rangle> = g\<langle>x\<rangle>"
  shows "f = g"
proof -
  have "\<And>a. a \<in>: f \<Longrightarrow> a \<in>: g"
  proof -
    fix a
    assume af: "a \<in>: f"
    from af have "\<exists>a1 a2. a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      using assms unfolding funspace_def apply_def using relspace_def by force
    then obtain a1 a2 where a12:
      "a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      by blast
    then have "\<exists>a3. a2 \<in>: t \<and> (a1 ,: a3) \<in>: g"
      using assms(2) funspace_def by auto
    then obtain a3 where a3: "a2 \<in>: t \<and> (a1 ,: a3) \<in>: g"
      by auto
    then have "a3 = a2"
      using a12 af assms(1,2,3) apply_if_pair_in by auto
    then show "a \<in>: g"
      using a12 a3 by blast
  qed
  moreover
  have "\<And>a. a \<in>: g \<Longrightarrow> a \<in>: f"
  proof -
    fix a
    assume ag: "a \<in>: g"
    then have "\<exists>a1 a2. a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      using assms unfolding funspace_def apply_def using relspace_def by force
    then obtain a1 a2 where a12:
      "a1 \<in>:s \<and> a2 \<in>: t \<and> (a1 ,: a2) = a"
      by blast
    then have "\<exists>a3. a2 \<in>: t \<and> (a1 ,: a3) \<in>: f"
      using assms(1) funspace_def by auto
    then obtain a3 where a3: "a2 \<in>: t \<and> (a1 ,: a3) \<in>: f"
      by auto
    then have "a3 = a2"
      using a12 ag assms(1,2,3) apply_if_pair_in by auto
    then show "a \<in>: f"
      using a3 a12 by blast
  qed
  ultimately
  show ?thesis 
    using iffD2[OF extensional] by metis
qed

end

(* Corresponds to CakeML's constant is_model *)
locale model = set_theory _ _ pow
  for pow :: "'u \<Rightarrow> 'u" +
  fixes ch :: "'u \<Rightarrow> 'u"
  fixes indset :: "'u"
  assumes infinite: "is_infinite indset"
  assumes is_choice: "\<forall>x. (\<exists>a. a \<in>: x) \<longrightarrow> ch x \<in>: x"
begin

(* Corresponds to CakeML's theorem indset_inhabited *)
lemma indset_inhabited:
  "\<exists>i. i \<in>: indset"
  using infinite unfolding is_infinite_def using infinite_imp_nonempty by auto

end

end