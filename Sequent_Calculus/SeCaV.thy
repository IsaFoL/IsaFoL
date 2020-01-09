(*
    Author: Jørgen Villadsen, DTU Compute, 2019
    Contributors: Asta Halkjær From, Alexander Birch Jensen & Anders Schlichtkrull
*)

text \<open>Lastest version at IsaFoL \<^url>\<open>https://bitbucket.org/isafol/\<close> in Sequent_Calculus directory\<close>

section \<open>Sequent Calculus Verifier (SeCaV)\<close>

theory SeCaV imports Main begin

section \<open>Syntax: Terms\<close>

datatype 'a "term" =
  Var nat |
  Fun 'a \<open>'a term list\<close>

section \<open>Increment Function\<close>

primrec
  liftt :: \<open>'a term \<Rightarrow> 'a term\<close> and
  liftts :: \<open>'a term list \<Rightarrow> 'a term list\<close> where
  \<open>liftt (Var i) = Var (Suc i)\<close>
| \<open>liftt (Fun a ts) = Fun a (liftts ts)\<close>
| \<open>liftts [] = []\<close>
| \<open>liftts (t # ts) = liftt t # liftts ts\<close>

section \<open>Parameters: Terms\<close>

primrec
  paramst :: \<open>'a term \<Rightarrow> 'a set\<close> and
  paramsts :: \<open>'a term list \<Rightarrow> 'a set\<close> where
  \<open>paramst (Var n) = {}\<close>
| \<open>paramst (Fun a ts) = {a} \<union> paramsts ts\<close>
| \<open>paramsts [] = {}\<close>
| \<open>paramsts (t # ts) = (paramst t \<union> paramsts ts)\<close>

lemma p0 [simp]: \<open>paramsts ts = \<Union>(set (map paramst ts))\<close>
  by (induct ts) auto

primrec paramst' :: \<open>'a term \<Rightarrow> 'a set\<close> where
  \<open>paramst' (Var n) = {}\<close>
| \<open>paramst' (Fun a ts) = {a} \<union> \<Union>(set (map paramst' ts))\<close>

lemma p1 [simp]: \<open>paramst' t = paramst t\<close>
  by (induct t) auto

section \<open>Syntax: Formulas\<close>

datatype ('a, 'b) form =
  Pre 'b \<open>'a term list\<close> |
  Con \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close> |
  Dis \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close> |
  Imp \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close> |
  Neg \<open>('a, 'b) form\<close> |
  Uni \<open>('a, 'b) form\<close> |
  Exi \<open>('a, 'b) form\<close>

section \<open>Parameters: Formulas\<close>

primrec params :: \<open>('a, 'b) form \<Rightarrow> 'a set\<close> where
  \<open>params (Pre b ts) = paramsts ts\<close>
| \<open>params (Con p q) = params p \<union> params q\<close>
| \<open>params (Dis p q) = params p \<union> params q\<close>
| \<open>params (Imp p q) = params p \<union> params q\<close>
| \<open>params (Neg p) = params p\<close>
| \<open>params (Uni p) = params p\<close>
| \<open>params (Exi p) = params p\<close>

primrec params' :: \<open>('a, 'b) form \<Rightarrow> 'a set\<close> where
  \<open>params' (Pre b ts) = \<Union>(set (map paramst' ts))\<close>
| \<open>params' (Con p q) = params' p \<union> params' q\<close>
| \<open>params' (Dis p q) = params' p \<union> params' q\<close>
| \<open>params' (Imp p q) = params' p \<union> params' q\<close>
| \<open>params' (Neg p) = params' p\<close>
| \<open>params' (Uni p) = params' p\<close>
| \<open>params' (Exi p) = params' p\<close>

lemma p2 [simp]: \<open>params' p = params p\<close>
  by (induct p) auto

fun paramst'' :: \<open>'a term \<Rightarrow> 'a set\<close> where
  \<open>paramst'' (Var n) = {}\<close>
| \<open>paramst'' (Fun a ts) = {a} \<union> (\<Union>t \<in> set ts. paramst'' t)\<close>

lemma p1' [simp]: \<open>paramst'' t = paramst t\<close>
  by (induct t) auto

fun params'' :: \<open>('a, 'b) form \<Rightarrow> 'a set\<close> where
  \<open>params'' (Pre b ts) = (\<Union>t \<in> set ts. paramst'' t)\<close>
| \<open>params'' (Con p q) = params'' p \<union> params'' q\<close>
| \<open>params'' (Dis p q) = params'' p \<union> params'' q\<close>
| \<open>params'' (Imp p q) = params'' p \<union> params'' q\<close>
| \<open>params'' (Neg p) = params'' p\<close>
| \<open>params'' (Uni p) = params'' p\<close>
| \<open>params'' (Exi p) = params'' p\<close>

lemma p2' [simp]: \<open>params'' p = params p\<close>
  by (induct p) auto

section \<open>Semantics: Terms\<close>

primrec semantics_term and semantics_list where
  \<open>semantics_term e f (Var n) = e n\<close> |
  \<open>semantics_term e f (Fun i l) = f i (semantics_list e f l)\<close> |
  \<open>semantics_list e f [] = []\<close> |
  \<open>semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l\<close>

section \<open>Semantics: Formulas\<close>

definition shift where
  \<open>shift e v z \<equiv> \<lambda>n. if n < v then e n else if n = v then z else e (n - 1)\<close>

primrec semantics where
  \<open>semantics e f g (Pre i l) = g i (semantics_list e f l)\<close> |
  \<open>semantics e f g (Con p q) = (semantics e f g p \<and> semantics e f g q)\<close> |
  \<open>semantics e f g (Dis p q) = (semantics e f g p \<or> semantics e f g q)\<close> |
  \<open>semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)\<close> |
  \<open>semantics e f g (Neg p) = (\<not> semantics e f g p)\<close> |
  \<open>semantics e f g (Uni p) = (\<forall>z. semantics (shift e 0 z) f g p)\<close> |
  \<open>semantics e f g (Exi p) = (\<exists>z. semantics (shift e 0 z) f g p)\<close>

section \<open>Update Lemmas\<close>

lemma upd_lemma' [simp]:
  \<open>n \<notin> paramst t \<Longrightarrow> semantics_term e (f(n := x)) t = semantics_term e f t\<close>
  \<open>n \<notin> paramsts ts \<Longrightarrow> semantics_list e (f(n := x)) ts = semantics_list e f ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) auto

lemma upd_lemma [simp]: \<open>n \<notin> params p \<Longrightarrow> semantics e (f(n := x)) g p = semantics e f g p\<close>
  by (induct p arbitrary: e) auto

section \<open>Substitution\<close>

primrec
  substt :: \<open>'a term \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term\<close> and
  substts :: \<open>'a term list \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term list\<close> where
  \<open>substt (Var i) s k = (if k < i then Var (i - 1) else if i = k then s else Var i)\<close>
| \<open>substt (Fun a ts) s k = Fun a (substts ts s k)\<close>
| \<open>substts [] s k = []\<close>
| \<open>substts (t # ts) s k = substt t s k # substts ts s k\<close>

primrec subst :: \<open>('a, 'b) form \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> ('a, 'b) form\<close> where
  \<open>subst (Pre b ts) s k = Pre b (substts ts s k)\<close>
| \<open>subst (Con p q) s k = Con (subst p s k) (subst q s k)\<close>
| \<open>subst (Dis p q) s k = Dis (subst p s k) (subst q s k)\<close>
| \<open>subst (Imp p q) s k = Imp (subst p s k) (subst q s k)\<close>
| \<open>subst (Neg p) s k = Neg (subst p s k)\<close>
| \<open>subst (Uni p) s k = Uni (subst p (liftt s) (Suc k))\<close>
| \<open>subst (Exi p) s k = Exi (subst p (liftt s) (Suc k))\<close>

lemma shift_eq [simp]: \<open>i = j \<Longrightarrow> (shift e i T) j = T\<close> for i :: nat
  unfolding shift_def by force

lemma shift_gt [simp]: \<open>j < i \<Longrightarrow> (shift e i T) j = e j\<close> for i :: nat
  unfolding shift_def by force

lemma shift_lt [simp]: \<open>i < j \<Longrightarrow> (shift e i T) j = e (j - 1)\<close> for i :: nat
  unfolding shift_def by force

lemma shift_commute [simp]: \<open>shift (shift e i U) 0 T = shift (shift e 0 T) (Suc i) U\<close>
  unfolding shift_def by force

lemma subst_lemma' [simp]:
  \<open>semantics_term e f (substt t u i) = semantics_term (shift e i (semantics_term e f u)) f t\<close>
  \<open>semantics_list e f (substts ts u i) = semantics_list (shift e i (semantics_term e f u)) f ts\<close>
  by (induct t and ts rule: substt.induct substts.induct) auto

lemma lift_lemma [simp]:
  \<open>semantics_term (shift e 0 z) f (liftt t) = semantics_term e f t\<close>
  \<open>semantics_list (shift e 0 z) f (liftts ts) = semantics_list e f ts\<close>
  by (induct t and ts rule: liftt.induct liftts.induct) auto

lemma subst_lemma [simp]:
  \<open>semantics e f g (subst a t i) = semantics (shift e i (semantics_term e f t)) f g a\<close>
  by (induct a arbitrary: e i t) auto

section \<open>Auxiliary Functions\<close>

primrec new_term and new_list where
  \<open>new_term c (Var n) = True\<close> |
  \<open>new_term c (Fun i l) = (if i = c then False else new_list c l)\<close> |
  \<open>new_list c [] = True\<close> |
  \<open>new_list c (t # l) = (if new_term c t then new_list c l else False)\<close>

primrec new where
  \<open>new c (Pre i l) = new_list c l\<close> |
  \<open>new c (Con p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Dis p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Imp p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Neg p) = new c p\<close> |
  \<open>new c (Uni p) = new c p\<close> |
  \<open>new c (Exi p) = new c p\<close>

primrec news where
  \<open>news c [] = True\<close> |
  \<open>news c (p # x) = (if new c p then news c x else False)\<close>

primrec inc_term and inc_list where
  \<open>inc_term (Var n) = Var (n + 1)\<close> |
  \<open>inc_term (Fun i l) = Fun i (inc_list l)\<close> |
  \<open>inc_list [] = []\<close> |
  \<open>inc_list (t # l) = inc_term t # inc_list l\<close>

primrec sub_term and sub_list where
  \<open>sub_term v s (Var n) = (if n < v then Var n else if n = v then s else Var (n - 1))\<close> |
  \<open>sub_term v s (Fun i l) = Fun i (sub_list v s l)\<close> |
  \<open>sub_list v s [] = []\<close> |
  \<open>sub_list v s (t # l) = sub_term v s t # sub_list v s l\<close>

primrec sub where
  \<open>sub v s (Pre i l) = Pre i (sub_list v s l)\<close> |
  \<open>sub v s (Con p q) = Con (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Dis p q) = Dis (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Imp p q) = Imp (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Neg p) = Neg (sub v s p)\<close> |
  \<open>sub v s (Uni p) = Uni (sub (v + 1) (inc_term s) p)\<close> |
  \<open>sub v s (Exi p) = Exi (sub (v + 1) (inc_term s) p)\<close>

primrec member where
  \<open>member p [] = False\<close> |
  \<open>member p (q # x) = (if p = q then True else member p x)\<close>

primrec ext where
  \<open>ext y [] = True\<close> |
  \<open>ext y (p # x) = (if member p y then ext y x else False)\<close>

section \<open>Sequent Calculus\<close>

inductive sequent_calculus (\<open>\<tturnstile> _\<close> 0) where
  \<open>\<tturnstile> Pre i l # Neg (Pre i l) # x\<close> |
  \<open>\<tturnstile> p # x \<Longrightarrow> \<tturnstile> Neg (Neg p) # x\<close> |
  \<open>\<tturnstile> p # q # x \<Longrightarrow> \<tturnstile> Dis p q # x\<close> |
  \<open>\<tturnstile> Neg p # q # x \<Longrightarrow> \<tturnstile> Imp p q # x\<close> |
  \<open>\<tturnstile> Neg p # Neg q # x \<Longrightarrow> \<tturnstile> Neg (Con p q) # x\<close> |
  \<open>\<tturnstile> p # x \<Longrightarrow> \<tturnstile> q # x \<Longrightarrow> \<tturnstile> Con p q # x\<close> |
  \<open>\<tturnstile> p # x \<Longrightarrow> \<tturnstile> Neg q # x \<Longrightarrow> \<tturnstile> Neg (Imp p q) # x\<close> |
  \<open>\<tturnstile> Neg p # x \<Longrightarrow> \<tturnstile> Neg q # x \<Longrightarrow> \<tturnstile> Neg (Dis p q) # x\<close> |
  \<open>\<tturnstile> sub 0 t p # x \<Longrightarrow> \<tturnstile> Exi p # x\<close> |
  \<open>\<tturnstile> Neg (sub 0 t p) # x \<Longrightarrow> \<tturnstile> Neg (Uni p) # x\<close> |
  \<open>\<tturnstile> sub 0 (Fun i []) p # x \<Longrightarrow> news i (p # x) \<Longrightarrow> \<tturnstile> Uni p # x\<close> |
  \<open>\<tturnstile> Neg (sub 0 (Fun i []) p) # x \<Longrightarrow> news i (p # x) \<Longrightarrow> \<tturnstile> Neg (Exi p) # x\<close> |
  \<open>\<tturnstile> x \<Longrightarrow> ext y x \<Longrightarrow> \<tturnstile> y\<close>

section \<open>Auxiliary Lemmas\<close>

lemma s1 [simp]: \<open>new_term c t = (c \<notin> paramst t)\<close> \<open>new_list c l = (c \<notin> paramsts l)\<close>
  by (induct t and l rule: new_term.induct new_list.induct) auto

lemma s2 [simp]: \<open>new c p = (c \<notin> params p)\<close>
  by (induct p) auto

lemma s3 [simp]: \<open>news c x = list_all (\<lambda>p. c \<notin> params p) x\<close>
  by (induct x) auto

lemma s5 [simp]: \<open>sub_term v s t = substt t s v\<close> \<open>sub_list v s l = substts l s v\<close>
  by (induct t and l rule: inc_term.induct inc_list.induct) auto

lemma s4 [simp]: \<open>inc_term t = liftt (t :: 'a term)\<close> \<open>inc_list l = liftts (l :: 'a term list)\<close>
  by (induct t and l rule: inc_term.induct inc_list.induct) auto

lemma s6 [simp]: \<open>sub v s p = subst p s v\<close>
  by (induct p arbitrary: v s) auto

lemma s7 [simp]: \<open>member p x = (p \<in> set x)\<close>
  by (induct x) auto

lemma s8 [simp]: \<open>ext y x = (set x \<subseteq> set y)\<close>
  by (induct x) auto

section \<open>Soundness\<close>

theorem sound: \<open>\<tturnstile> x \<Longrightarrow> \<exists>p \<in> set x. semantics e f g p\<close>
proof (induct arbitrary: f rule: sequent_calculus.induct)
  case (11 i p x)
  then show ?case
  proof (cases \<open>\<forall>z. semantics e (f(i := \<lambda>_. z)) g (sub 0 (Fun i []) p)\<close>)
    case False
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) x\<close>
      using 11 by auto
    ultimately show ?thesis
      using 11 Ball_set insert_iff list.set(2) upd_lemma by metis
  qed auto
next
  case (12 i p x)
  then show ?case
  proof (cases \<open>\<forall>z. semantics e (f(i := \<lambda>_. z)) g (Neg (sub 0 (Fun i []) p))\<close>)
    case False
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) x\<close>
      using 12 by auto
    ultimately show ?thesis
      using 12 Ball_set insert_iff list.set(2) upd_lemma by metis
  qed auto
qed auto

corollary \<open>\<tturnstile> x \<Longrightarrow> \<exists>p. member p x \<and> semantics e f g p\<close>
  using sound by force

corollary \<open>\<tturnstile> [p] \<Longrightarrow> semantics e f g p\<close>
  using sound by force

corollary \<open>\<not> (\<tturnstile> [])\<close>
  using sound by force

section \<open>Completeness\<close>

text \<open>Full proofs at IsaFoL \<^url>\<open>https://bitbucket.org/isafol/\<close> in FOL_Berghofer directory\<close>

section \<open>Micro Example\<close>

proposition \<open>p a \<longrightarrow> p a\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Pre ''p'' [Fun ''a'' []]) (Pre ''p'' [Fun ''a'' []])
  ]
    :: (string, string) form list\<close>
proof -
  have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' [Fun ''a'' []]),
      Pre ''p'' [Fun ''a'' []]
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(4) that .
  then have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [Fun ''a'' []],
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(13) that by force
  then show ?thesis
    using sequent_calculus.intros(1) .
qed

section \<open>Small Example\<close>

proposition \<open>p a \<longrightarrow> (\<exists>x. p x)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Pre ''p'' [Fun ''a'' []]) (Exi (Pre ''p'' [Var 0]))
  ]
    :: (string, string) form list\<close>
proof -
  have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' [Fun ''a'' []]),
      Exi (Pre ''p'' [Var 0])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(4) that .
  then have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre ''p'' [Var 0]),
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(13) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [Fun ''a'' []],
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(9) that by force
  then show ?thesis
    using sequent_calculus.intros(1) .
qed

section \<open>Large Example\<close>

proposition \<open>(\<forall>x. p x \<longrightarrow> q x) \<longrightarrow> (\<exists>x. p x) \<longrightarrow> (\<exists>x. q x)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp
      (Uni (Imp (Pre ''p'' [Var 0]) (Pre ''q'' [Var 0])))
      (Imp (Exi (Pre ''p'' [Var 0])) (Exi (Pre ''q'' [Var 0])))
  ]
    :: (string, string) form list\<close>
proof -
  have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Pre ''p'' [Var 0]) (Pre ''q'' [Var 0]))),
      Imp (Exi (Pre ''p'' [Var 0])) (Exi (Pre ''q'' [Var 0]))
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(4) that .
  then have ?thesis if \<open>\<tturnstile>
    [
      Imp (Exi (Pre ''p'' [Var 0])) (Exi (Pre ''q'' [Var 0])),
      Neg (Uni (Imp (Pre ''p'' [Var 0]) (Pre ''q'' [Var 0])))
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(13) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Neg (Exi (Pre ''p'' [Var 0])),
      Exi (Pre ''q'' [Var 0]),
      Neg (Uni (Imp (Pre ''p'' [Var 0]) (Pre ''q'' [Var 0])))
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(4) that .
  then have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre ''p'' [Fun ''a'' []]),
      Exi (Pre ''q'' [Var 0]),
      Neg (Uni (Imp (Pre ''p'' [Var 0]) (Pre ''q'' [Var 0])))
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(12) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Pre ''p'' [Var 0]) (Pre ''q'' [Var 0]))),
      Neg (Pre ''p'' [Fun ''a'' []]),
      Exi (Pre ''q'' [Var 0])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(13) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre ''p'' [Fun ''a'' []]) (Pre ''q'' [Fun ''a'' []])),
      Neg (Pre ''p'' [Fun ''a'' []]),
      Exi (Pre ''q'' [Var 0])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(10) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre ''q'' [Var 0]),
      Neg ((Imp (Pre ''p'' [Fun ''a'' []]) (Pre ''q'' [Fun ''a'' []]))),
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(13) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Pre ''q'' [Fun ''a'' []],
      Neg ((Imp (Pre ''p'' [Fun ''a'' []]) (Pre ''q'' [Fun ''a'' []]))),
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(9) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Neg ((Imp (Pre ''p'' [Fun ''a'' []]) (Pre ''q'' [Fun ''a'' []]))),
      Pre ''q'' [Fun ''a'' []],
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(13) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [Fun ''a'' []],
      Pre ''q'' [Fun ''a'' []],
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close> and \<open>\<tturnstile>
    [
      Neg (Pre ''q'' [Fun ''a'' []]),
      Pre ''q'' [Fun ''a'' []],
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(7) that .
  then have ?thesis if \<open>\<tturnstile>
    [
      Pre ''p'' [Fun ''a'' []],
      Neg (Pre ''p'' [Fun ''a'' []]),
      Pre ''q'' [Fun ''a'' []]
    ]
      :: (string, string) form list\<close> and \<open>\<tturnstile>
    [
      Pre ''q'' [Fun ''a'' []],
      Neg (Pre ''q'' [Fun ''a'' []]),
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(13) that by force
  then have ?thesis if \<open>\<tturnstile>
    [
      Pre ''q'' [Fun ''a'' []],
      Neg (Pre ''q'' [Fun ''a'' []]),
      Neg (Pre ''p'' [Fun ''a'' []])
    ]
      :: (string, string) form list\<close>
    using sequent_calculus.intros(1) that .
  then show ?thesis
    using sequent_calculus.intros(1) .
qed

section \<open>Acknowledgements\<close>

text \<open>Mordechai Ben-Ari (Springer 2012): Mathematical Logic for Computer Science (Third Edition)\<close>

end
