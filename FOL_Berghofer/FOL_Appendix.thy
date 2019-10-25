(*
    Author: Jørgen Villadsen, DTU Compute, 2019
    Contributors: Andreas Halkjær From, Alexander Birch Jensen & Anders Schlichtkrull
*)

section \<open>Formalizing a Sequent Calculus in Isabelle/HOL\<close>

theory FOL_Appendix imports FOL_Sequent begin

fun new_term and new_list where
  \<open>new_term c (Var n) = True\<close> |
  \<open>new_term c (Fun i l) = (if i = c then False else new_list c l)\<close> |
  \<open>new_list c [] = True\<close> |
  \<open>new_list c (t # l) = (if new_term c t then new_list c l else False)\<close>

fun new where
  \<open>new c \<bottom> = True\<close> |
  \<open>new c \<top> = True\<close> |
  \<open>new c (Pre i l) = new_list c l\<close> |
  \<open>new c (Con p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Dis p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Imp p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Neg p) = new c p\<close> |
  \<open>new c (Uni p) = new c p\<close> |
  \<open>new c (Exi p) = new c p\<close>

fun news where
  \<open>news c [] = True\<close> |
  \<open>news c (p # x) = (if new c p then news c x else False)\<close>

fun inc_term and inc_list where
  \<open>inc_term (Var n) = Var (n + 1)\<close> |
  \<open>inc_term (Fun i l) = Fun i (inc_list l)\<close> |
  \<open>inc_list [] = []\<close> |
  \<open>inc_list (t # l) = inc_term t # inc_list l\<close>

fun sub_term and sub_list where
  \<open>sub_term v s (Var n) = (if n < v then Var n else if n = v then s else Var (n - 1))\<close> |
  \<open>sub_term v s (Fun i l) = Fun i (sub_list v s l)\<close> |
  \<open>sub_list v s [] = []\<close> |
  \<open>sub_list v s (t # l) = sub_term v s t # sub_list v s l\<close>

fun sub where
  \<open>sub v s \<bottom> = \<bottom>\<close> |
  \<open>sub v s \<top> = \<top>\<close> |
  \<open>sub v s (Pre i l) = Pre i (sub_list v s l)\<close> |
  \<open>sub v s (Con p q) = Con (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Dis p q) = Dis (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Imp p q) = Imp (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Neg p) = Neg (sub v s p)\<close> |
  \<open>sub v s (Uni p) = Uni (sub (v + 1) (inc_term s) p)\<close> |
  \<open>sub v s (Exi p) = Exi (sub (v + 1) (inc_term s) p)\<close>

fun member where
  \<open>member p [] = False\<close> |
  \<open>member p (q # x) = (if p = q then True else member p x)\<close>

fun ext where
  \<open>ext y [] = True\<close> |
  \<open>ext y (p # x) = (if member p y then ext y x else False)\<close>

inductive sequent_calculus ("\<tturnstile> _" 0) where
  \<open>\<tturnstile> Pre i l # Neg (Pre i l) # x\<close> |
  \<open>\<tturnstile> Neg \<bottom> # x\<close> |
  \<open>\<tturnstile> \<top> # x\<close> |
  \<open>\<tturnstile> p # x \<Longrightarrow> \<tturnstile> Neg (Neg p) # x\<close> |
  \<open>\<tturnstile> Neg p # Neg q # x \<Longrightarrow> \<tturnstile> Neg (Con p q) # x\<close> |
  \<open>\<tturnstile> p # q # x \<Longrightarrow> \<tturnstile> Dis p q # x\<close> |
  \<open>\<tturnstile> Neg p # q # x \<Longrightarrow> \<tturnstile> Imp p q # x\<close> |
  \<open>\<tturnstile> p # x \<Longrightarrow> \<tturnstile> q # x \<Longrightarrow> \<tturnstile> Con p q # x\<close> |
  \<open>\<tturnstile> Neg p # x \<Longrightarrow> \<tturnstile> Neg q # x \<Longrightarrow> \<tturnstile> Neg (Dis p q) # x\<close> |
  \<open>\<tturnstile> p # x \<Longrightarrow> \<tturnstile> Neg q # x \<Longrightarrow> \<tturnstile> Neg (Imp p q) # x\<close> |
  \<open>\<tturnstile> sub 0 t p # x \<Longrightarrow> \<tturnstile> Exi p # x\<close> |
  \<open>\<tturnstile> Neg (sub 0 t p) # x \<Longrightarrow> \<tturnstile> Neg (Uni p) # x\<close> |
  \<open>\<tturnstile> sub 0 (Fun i []) p # x \<Longrightarrow> news i (p # x) \<Longrightarrow> \<tturnstile> Uni p # x\<close> |
  \<open>\<tturnstile> Neg (sub 0 (Fun i []) p) # x \<Longrightarrow> news i (p # x) \<Longrightarrow> \<tturnstile> Neg (Exi p) # x\<close> |
  \<open>\<tturnstile> x \<Longrightarrow> ext y x \<Longrightarrow> \<tturnstile> y\<close>

lemma s1 [simp]: \<open>new_term c t = FOL_Berghofer.new_term c t\<close> \<open>new_list c l = FOL_Berghofer.new_list c l\<close>
  by (induct t and l rule: new_term_new_list.induct) simp_all

lemma s2 [simp]: \<open>new c p = FOL_Berghofer.new c p\<close>
  by (induct p) simp_all

lemma s3 [simp]: \<open>news c x = FOL_Berghofer.news c x\<close>
  by (induct x) simp_all

lemma s4 [simp]: \<open>inc_term t = liftt (t :: 'a term)\<close> \<open>inc_list l = liftts (l :: 'a term list)\<close>
  by (induct t and l rule: inc_term_inc_list.induct) simp_all

lemma s5 [simp]: \<open>sub_term v s t = substt t s v\<close> \<open>sub_list v s l = substts l s v\<close>
  by (induct t and l rule: inc_term_inc_list.induct) simp_all

lemma s6 [simp]: \<open>sub v s p = subst p s v\<close>
  by (induct p arbitrary: v s) simp_all

lemma member_set [simp]: \<open>p \<in> set x = member p x\<close>
  by (induct x) simp_all

lemma ext_set [simp]: \<open>set x \<subseteq> set y = ext y x\<close>
  by (induct x) simp_all

lemma x1: \<open>\<tturnstile> x \<Longrightarrow> \<turnstile> x\<close>
  by (induct x rule: sequent_calculus.induct) (simp_all add: SC.intros)

lemma x2: \<open>\<turnstile> x \<Longrightarrow> \<tturnstile> x\<close>
  by (induct x rule: SC.induct) (simp_all add: sequent_calculus.intros)

lemma x0: \<open>(\<tturnstile> x) = (\<turnstile> x)\<close>
  using x1 x2 by fast

abbreviation herbrand_valid ("\<then> _" 0) where
  \<open>(\<then> p :: (nat, nat) form) \<equiv> \<forall>(e :: _ \<Rightarrow> nat hterm) f g. semantics e f g p\<close>

theorem complete_sound: \<open>\<then> p \<Longrightarrow> \<tturnstile> [p]\<close> \<open>\<tturnstile> [q] \<Longrightarrow> semantics e f g q\<close>
  by (use SC_completeness x0 list.map(1) in metis) (use SC_soundness x0 in fastforce)

corollary \<open>(\<then> p) \<longleftrightarrow> (\<tturnstile> [p])\<close>
  using complete_sound by fast

subsection \<open>Acknowledgements\<close>

text \<open>

\<^item> Mordechai (Moti) Ben-Ari:
Mathematical Logic for Computer Science.
\<^url>\<open>https://www.springer.com/gp/book/9781447141280\<close>

\<close>

end
