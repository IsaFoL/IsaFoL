theory WoLLIC_Sorry imports Main begin

datatype 'a "term" =
  Var nat |
  Fun 'a \<open>'a term list\<close>

datatype ('a, 'b) form =
  FF ("\<bottom>") |
  TT ("\<top>") |
  Pre 'b \<open>'a term list\<close> |
  Con \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close> |
  Dis \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close> |
  Imp \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close> |
  Neg \<open>('a, 'b) form\<close> |
  Uni \<open>('a, 'b) form\<close> |
  Exi \<open>('a, 'b) form\<close>

datatype 'a hterm = HFun 'a \<open>'a hterm list\<close>

definition shift where
  \<open>shift e v z \<equiv> \<lambda>n. if n < v then e n else if n = v then z else e (n - 1)\<close>

fun semantics_term and semantics_list where
  \<open>semantics_term e f (Var n) = e n\<close> |
  \<open>semantics_term e f (Fun i l) = f i (semantics_list e f l)\<close> |
  \<open>semantics_list e f [] = []\<close> |
  \<open>semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l\<close>

fun semantics where
  \<open>semantics e f g \<bottom> = False\<close> |
  \<open>semantics e f g \<top> = True\<close> |
  \<open>semantics e f g (Pre i l) = g i (semantics_list e f l)\<close> |
  \<open>semantics e f g (Con p q) = (semantics e f g p \<and> semantics e f g q)\<close> |
  \<open>semantics e f g (Dis p q) = (semantics e f g p \<or> semantics e f g q)\<close> |
  \<open>semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)\<close> |
  \<open>semantics e f g (Neg p) = (\<not> semantics e f g p)\<close> |
  \<open>semantics e f g (Uni p) = (\<forall>z. semantics (shift e 0 z) f g p)\<close> |
  \<open>semantics e f g (Exi p) = (\<exists>z. semantics (shift e 0 z) f g p)\<close>

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

abbreviation herbrand_valid ("\<then> _" 0) where
  \<open>(\<then> p :: (nat, nat) form) \<equiv> \<forall>(e :: _ \<Rightarrow> nat hterm) f g. semantics e f g p\<close>

theorem complete_sound: \<open>\<then> p \<Longrightarrow> \<tturnstile> [p]\<close> \<open>\<tturnstile> [q] \<Longrightarrow> semantics e f g q\<close>
  sorry

corollary \<open>(\<then> p) \<longleftrightarrow> (\<tturnstile> [p])\<close>
  using complete_sound by fast

end
