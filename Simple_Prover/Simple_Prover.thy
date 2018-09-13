(* Authors: Jørgen Villadsen, Anders Schlichtkrull, Andreas Halkjær From *)

section \<open>A Certified Simple Prover for First-Order Logic\<close>

theory Simple_Prover imports Main begin

section \<open>Preliminaries\<close>

primrec dec :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>dec 0 = 0\<close> |
  \<open>dec (Suc n) = n\<close>

primrec sub :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sub x 0 = x\<close> |
  \<open>sub x (Suc n) = dec (sub x n)\<close>

primrec add :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>add x 0 = x\<close> |
  \<open>add x (Suc n) = Suc (add x n)\<close>

lemma append_simps: \<open>[] @ l = l\<close> \<open>(h # t) @ l = h # t @ l\<close>
  by (rule append.simps(1),rule append.simps(2))

lemma if_simps: \<open>(if True then x else y) = x\<close> \<open>(if False then x else y) = y\<close>
  by (rule if_True,rule if_False)

lemma not_simps: \<open>(\<not> True) = False\<close> \<open>(\<not> False) = True\<close>
  by (rule not_True_eq_False,rule not_False_eq_True)

lemma prod_simps: \<open>fst (x,y) = x\<close> \<open>snd (x,y) = y\<close>
  unfolding fst_def snd_def
  by (rule prod.case,rule prod.case)

lemma nat_simps: \<open>(0 = 0) = True\<close>
  by (rule simp_thms)

lemma list_simps: \<open>([] = []) = True\<close>
  by (rule simp_thms)

lemma bool_simps: \<open>(True = True) = True\<close> \<open>(False = False) = True\<close>
  by (rule simp_thms,rule simp_thms)

lemma inject_simps: \<open>(True \<and> b) = b\<close> \<open>(False \<and> b) = False\<close>
  by (rule simp_thms,rule simp_thms)

section \<open>Syntax and Semantics\<close>

type_synonym id = nat

datatype nnf = Pre bool id \<open>nat list\<close> | Con nnf nnf | Dis nnf nnf | Uni nnf | Exi nnf

abbreviation (input) \<open>TEST P Q \<equiv> (\<exists>x. P x \<or> Q x) \<longrightarrow> (\<exists>x. Q x) \<or> (\<exists>x. P x)\<close>

proposition \<open>TEST P Q\<close>
  by iprover

proposition \<open>TEST P Q = (\<forall>x. \<not> P x \<and> \<not> Q x) \<or> (\<exists>x. Q x) \<or> (\<exists>x. P x)\<close>
  by fast

abbreviation (input) \<open>P_id \<equiv> 0\<close>

abbreviation (input) \<open>Q_id \<equiv> Suc 0\<close>

definition \<comment> \<open>TEST P Q\<close>
  \<open>test \<equiv> Dis
    (Uni (Con (Pre False P_id [0]) (Pre False Q_id [0])))
    (Dis (Exi (Pre True Q_id [0])) (Exi (Pre True P_id [0])))\<close>

type_synonym proxy = \<open>unit list\<close>

type_synonym model = \<open>proxy set \<times> (id \<Rightarrow> proxy list \<Rightarrow> bool)\<close>

type_synonym environment = \<open>nat \<Rightarrow> proxy\<close>

definition is_model_environment :: \<open>model \<Rightarrow> environment \<Rightarrow> bool\<close> where
  \<open>is_model_environment m e \<equiv> \<forall>n. e n \<in> fst m\<close>

primrec semantics :: \<open>model \<Rightarrow> environment \<Rightarrow> nnf \<Rightarrow> bool\<close> where
  \<open>semantics m e (Pre b i v) = (b = snd m i (map e v))\<close> |
  \<open>semantics m e (Con p q) = (semantics m e p \<and> semantics m e q)\<close> |
  \<open>semantics m e (Dis p q) = (semantics m e p \<or> semantics m e q)\<close> |
  \<open>semantics m e (Uni p) = (\<forall>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)\<close> |
  \<open>semantics m e (Exi p) = (\<exists>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)\<close>

section \<open>Sequent Calculus\<close>

primrec dash :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>dash l 0 = l\<close> |
  \<open>dash l (Suc n) = n # l\<close>

primrec dump :: \<open>nat list \<Rightarrow> nat list\<close> where
  \<open>dump [] = []\<close> |
  \<open>dump (h # t) = dash (dump t) h\<close>

primrec free :: \<open>nnf \<Rightarrow> nat list\<close> where
  \<open>free (Pre _ _ v) = v\<close> |
  \<open>free (Con p q) = free p @ free q\<close> |
  \<open>free (Dis p q) = free p @ free q\<close> |
  \<open>free (Uni p) = dump (free p)\<close> |
  \<open>free (Exi p) = dump (free p)\<close>

primrec frees :: \<open>nnf list \<Rightarrow> nat list\<close> where
  \<open>frees [] = []\<close> |
  \<open>frees (h # t) = free h @ frees t\<close>

primrec fresh :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>fresh [] = 0\<close> |
  \<open>fresh (h # t) = Suc (add (sub (dec (fresh t)) h) h)\<close>

primrec over :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>over s _ 0 = s\<close> |
  \<open>over _ h (Suc _) = h\<close>

primrec more :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>more x s h 0 = over s h (sub x h)\<close> |
  \<open>more _ _ h (Suc _) = dec h\<close>

primrec mend :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>mend _ _ [] = []\<close> |
  \<open>mend x s (h # t) = more x s h (sub h x) # mend x s t\<close>

primrec subst :: \<open>nat \<Rightarrow> nat \<Rightarrow> nnf \<Rightarrow> nnf\<close> where
  \<open>subst x s (Pre b i v) = Pre b i (mend x s v)\<close> |
  \<open>subst x s (Con p q) = Con (subst x s p) (subst x s q)\<close> |
  \<open>subst x s (Dis p q) = Dis (subst x s p) (subst x s q)\<close> |
  \<open>subst x s (Uni p) = Uni (subst (Suc x) (Suc s) p)\<close> |
  \<open>subst x s (Exi p) = Exi (subst (Suc x) (Suc s) p)\<close>

type_synonym sequent = \<open>(nat \<times> nnf) list\<close>

primrec base :: \<open>sequent \<Rightarrow> nnf list\<close> where
  \<open>base [] = []\<close> |
  \<open>base (h # t) = snd h # base t\<close>

primrec stop :: \<open>sequent list \<Rightarrow> nnf \<Rightarrow> nnf list \<Rightarrow> sequent list\<close> where
  \<open>stop c _ [] = c\<close> |
  \<open>stop c p (h # t) = (if p = h then [] else stop c p t)\<close>

primrec track :: \<open>sequent \<Rightarrow> nat \<Rightarrow> nnf \<Rightarrow> sequent list\<close> where
  \<open>track s _ (Pre b i v) = stop [s @ [(0,Pre b i v)]] (Pre (\<not> b) i v) (base s)\<close> |
  \<open>track s _ (Con p q) = [s @ [(0,p)],s @ [(0,q)]]\<close> |
  \<open>track s _ (Dis p q) = [s @ [(0,p),(0,q)]]\<close> |
  \<open>track s _ (Uni p) = [s @ [(0,subst 0 (fresh (frees (Uni p # base s))) p)]]\<close> |
  \<open>track s n (Exi p) = [s @ [(0,subst 0 n p),(Suc n,Exi p)]]\<close>

primrec solve :: \<open>sequent \<Rightarrow> sequent list\<close> where
  \<open>solve [] = [[]]\<close> |
  \<open>solve (h # t) = track t (fst h) (snd h)\<close>

primrec solves :: \<open>sequent list \<Rightarrow> sequent list\<close> where
  \<open>solves [] = []\<close> |
  \<open>solves (h # t) = solve h @ solves t\<close>

type_synonym 'a algorithm = \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool\<close>

primrec null :: \<open>'a list \<Rightarrow> bool\<close> where
  \<open>null [] = True\<close> |
  \<open>null (_ # _) = False\<close>

definition main :: \<open>sequent list algorithm \<Rightarrow> nnf \<Rightarrow> bool\<close> where
  \<open>main a p \<equiv> a null solves [[(0,p)]]\<close>

primrec repeat :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  \<open>repeat _ c 0 = c\<close> |
  \<open>repeat f c (Suc n) = repeat f (f c) n\<close>

definition iterator :: \<open>'a algorithm\<close> where
  \<open>iterator g f c \<equiv> \<exists>n. g (repeat f c n)\<close>

definition check :: \<open>nnf \<Rightarrow> bool\<close> where
  \<open>check \<equiv> main iterator\<close>

section \<open>Prover\<close>

abbreviation (input) \<open>CHECK \<equiv> check = (\<lambda>p. \<forall>m e. is_model_environment m e \<longrightarrow> semantics m e p)\<close>

abbreviation \<open>prover \<equiv> iterator null solves\<close>

lemma check_prover: \<open>check p \<equiv> prover [[(0,p)]]\<close>
  unfolding check_def main_def .

lemma iterator[code]: \<open>iterator g f c = (if g c then True else iterator g f (f c))\<close>
  unfolding iterator_def
  using repeat.simps not0_implies_Suc
  by metis

lemma prover: \<open>prover c = (if null c then True else prover (solves c))\<close>
  using iterator .

lemma prover_next: \<open>prover (h # t) = prover (solves (h # t))\<close>
  using prover
  by simp

lemma prover_done: \<open>prover [] = True\<close>
  using prover
  by simp

lemmas simps = check_prover prover_next prover_done solves.simps solve.simps track.simps stop.simps
  base.simps subst.simps mend.simps more.simps over.simps fresh.simps frees.simps free.simps
  dump.simps dash.simps nnf.distinct nnf.inject add.simps sub.simps dec.simps append_simps if_simps
  not_simps prod_simps nat_simps list_simps bool_simps inject_simps nat.distinct list.distinct
  bool.distinct prod.inject nat.inject list.inject

theorem program:
  \<open>\<And>p. check p \<equiv> prover [[(0,p)]]\<close>
  \<open>\<And>h t. prover (h # t) \<equiv> prover (solves (h # t))\<close>
  \<open>prover [] \<equiv> True\<close>
  \<open>solves [] \<equiv> []\<close>
  \<open>\<And>h t. solves (h # t) \<equiv> solve h @ solves t\<close>
  \<open>solve [] \<equiv> [[]]\<close>
  \<open>\<And>h t. solve (h # t) \<equiv> track t (fst h) (snd h)\<close>
  \<open>\<And>s n b i v. track s n (Pre b i v) \<equiv> stop [s @ [(0,Pre b i v)]] (Pre (\<not> b) i v) (base s)\<close>
  \<open>\<And>s n p q. track s n (Con p q) \<equiv> [s @ [(0,p)],s @ [(0,q)]]\<close>
  \<open>\<And>s n p q. track s n (Dis p q) \<equiv> [s @ [(0,p),(0,q)]]\<close>
  \<open>\<And>s n p. track s n (Uni p) \<equiv> [s @ [(0,subst 0 (fresh (frees (Uni p # base s))) p)]]\<close>
  \<open>\<And>s n p. track s n (Exi p) \<equiv> [s @ [(0,subst 0 n p),(Suc n,Exi p)]]\<close>
  \<open>\<And>c p. stop c p [] \<equiv> c\<close>
  \<open>\<And>c p h t. stop c p (h # t) \<equiv> (if p = h then [] else stop c p t)\<close>
  \<open>base [] \<equiv> []\<close>
  \<open>\<And>h t. base (h # t) \<equiv> snd h # base t\<close>
  \<open>\<And>x s b i v. subst x s (Pre b i v) \<equiv> Pre b i (mend x s v)\<close>
  \<open>\<And>x s p q. subst x s (Con p q) \<equiv> Con (subst x s p) (subst x s q)\<close>
  \<open>\<And>x s p q. subst x s (Dis p q) \<equiv> Dis (subst x s p) (subst x s q)\<close>
  \<open>\<And>x s p. subst x s (Uni p) \<equiv> Uni (subst (Suc x) (Suc s) p)\<close>
  \<open>\<And>x s p. subst x s (Exi p) \<equiv> Exi (subst (Suc x) (Suc s) p)\<close>
  \<open>\<And>x s. mend x s [] \<equiv> []\<close>
  \<open>\<And>x s h t. mend x s (h # t) \<equiv> more x s h (sub h x) # mend x s t\<close>
  \<open>\<And>x s h. more x s h 0 \<equiv> over s h (sub x h)\<close>
  \<open>\<And>x s h n. more x s h (Suc n) \<equiv> dec h\<close>
  \<open>\<And>s h. over s h 0 \<equiv> s\<close>
  \<open>\<And>s h n. over s h (Suc n) \<equiv> h\<close>
  \<open>fresh [] \<equiv> 0\<close>
  \<open>\<And>h t. fresh (h # t) \<equiv> Suc (add (sub (dec (fresh t)) h) h)\<close>
  \<open>frees [] \<equiv> []\<close>
  \<open>\<And>h t. frees (h # t) \<equiv> free h @ frees t\<close>
  \<open>\<And>b i v. free (Pre b i v) \<equiv> v\<close>
  \<open>\<And>p q. free (Con p q) \<equiv> free p @ free q\<close>
  \<open>\<And>p q. free (Dis p q) \<equiv> free p @ free q\<close>
  \<open>\<And>p. free (Uni p) \<equiv> dump (free p)\<close>
  \<open>\<And>p. free (Exi p) \<equiv> dump (free p)\<close>
  \<open>dump [] \<equiv> []\<close>
  \<open>\<And>h t. dump (h # t) \<equiv> dash (dump t) h\<close>
  \<open>\<And>l. dash l 0 \<equiv> l\<close>
  \<open>\<And>l n. dash l (Suc n) \<equiv> n # l\<close>
  by ((simp only: simps(1)),
      (simp only: simps(2)),
      (simp only: simps(3)),
      (simp only: simps(4)),
      (simp only: simps(5)),
      (simp only: simps(6)),
      (simp only: simps(7)),
      (simp only: simps(8)),
      (simp only: simps(9)),
      (simp only: simps(10)),
      (simp only: simps(11)),
      (simp only: simps(12)),
      (simp only: simps(13)),
      (simp only: simps(14)),
      (simp only: simps(15)),
      (simp only: simps(16)),
      (simp only: simps(17)),
      (simp only: simps(18)),
      (simp only: simps(19)),
      (simp only: simps(20)),
      (simp only: simps(21)),
      (simp only: simps(22)),
      (simp only: simps(23)),
      (simp only: simps(24)),
      (simp only: simps(25)),
      (simp only: simps(26)),
      (simp only: simps(27)),
      (simp only: simps(28)),
      (simp only: simps(29)),
      (simp only: simps(30)),
      (simp only: simps(31)),
      (simp only: simps(32)),
      (simp only: simps(33)),
      (simp only: simps(34)),
      (simp only: simps(35)),
      (simp only: simps(36)),
      (simp only: simps(37)),
      (simp only: simps(38)),
      (simp only: simps(39)),
      (simp only: simps(40)))

theorem data:
  \<open>\<And>b i v p q. Pre b i v = Con p q \<equiv> False\<close>
  \<open>\<And>b i v p q. Con p q = Pre b i v \<equiv> False\<close>
  \<open>\<And>b i v p q. Pre b i v = Dis p q \<equiv> False\<close>
  \<open>\<And>b i v p q. Dis p q = Pre b i v \<equiv> False\<close>
  \<open>\<And>b i v p. Pre b i v = Uni p \<equiv> False\<close>
  \<open>\<And>b i v p. Uni p = Pre b i v \<equiv> False\<close>
  \<open>\<And>b i v p. Pre b i v = Exi p \<equiv> False\<close>
  \<open>\<And>b i v p. Exi p = Pre b i v \<equiv> False\<close>
  \<open>\<And>p q p' q'. Con p q = Dis p' q' \<equiv> False\<close>
  \<open>\<And>p q p' q'. Dis p' q' = Con p q \<equiv> False\<close>
  \<open>\<And>p q p'. Con p q = Uni p' \<equiv> False\<close>
  \<open>\<And>p q p'. Uni p' = Con p q \<equiv> False\<close>
  \<open>\<And>p q p'. Con p q = Exi p' \<equiv> False\<close>
  \<open>\<And>p q p'. Exi p' = Con p q \<equiv> False\<close>
  \<open>\<And>p q p'. Dis p q = Uni p' \<equiv> False\<close>
  \<open>\<And>p q p'. Uni p' = Dis p q \<equiv> False\<close>
  \<open>\<And>p q p'. Dis p q = Exi p' \<equiv> False\<close>
  \<open>\<And>p q p'. Exi p' = Dis p q \<equiv> False\<close>
  \<open>\<And>p p'. Uni p = Exi p' \<equiv> False\<close>
  \<open>\<And>p p'. Exi p' = Uni p \<equiv> False\<close>
  \<open>\<And>b i v b' i' v'. Pre b i v = Pre b' i' v' \<equiv> b = b' \<and> i = i' \<and> v = v'\<close>
  \<open>\<And>p q p' q'. Con p q = Con p' q' \<equiv> p = p' \<and> q = q'\<close>
  \<open>\<And>p q p' q'. Dis p q = Dis p' q' \<equiv> p = p' \<and> q = q'\<close>
  \<open>\<And>p p'. Uni p = Uni p' \<equiv> p = p'\<close>
  \<open>\<And>p p'. Exi p = Exi p' \<equiv> p = p'\<close>
  by ((simp only: simps(41)),
      (simp only: simps(42)),
      (simp only: simps(43)),
      (simp only: simps(44)),
      (simp only: simps(45)),
      (simp only: simps(46)),
      (simp only: simps(47)),
      (simp only: simps(48)),
      (simp only: simps(49)),
      (simp only: simps(50)),
      (simp only: simps(51)),
      (simp only: simps(52)),
      (simp only: simps(53)),
      (simp only: simps(54)),
      (simp only: simps(55)),
      (simp only: simps(56)),
      (simp only: simps(57)),
      (simp only: simps(58)),
      (simp only: simps(59)),
      (simp only: simps(60)),
      (simp only: simps(61)),
      (simp only: simps(62)),
      (simp only: simps(63)),
      (simp only: simps(64)),
      (simp only: simps(65)))

theorem library:
  \<open>\<And>x. add x 0 \<equiv> x\<close>
  \<open>\<And>x n. add x (Suc n) \<equiv> Suc (add x n)\<close>
  \<open>\<And>x. sub x 0 \<equiv> x\<close>
  \<open>\<And>x n. sub x (Suc n) \<equiv> dec (sub x n)\<close>
  \<open>dec 0 \<equiv> 0\<close>
  \<open>\<And>n. dec (Suc n) \<equiv> n\<close>
  \<open>\<And>l. [] @ l \<equiv> l\<close>
  \<open>\<And>h t l. (h # t) @ l \<equiv> h # t @ l\<close>
  \<open>\<And>x y. if True then x else y \<equiv> x\<close>
  \<open>\<And>x y. if False then x else y \<equiv> y\<close>
  \<open>\<not> True \<equiv> False\<close>
  \<open>\<not> False \<equiv> True\<close>
  \<open>\<And>x y. fst (x,y) \<equiv> x\<close>
  \<open>\<And>x y. snd (x,y) \<equiv> y\<close>
  \<open>0 = 0 \<equiv> True\<close>
  \<open>[] = [] \<equiv> True\<close>
  \<open>True = True \<equiv> True\<close>
  \<open>False = False \<equiv> True\<close>
  \<open>\<And>b. True \<and> b \<equiv> b\<close>
  \<open>\<And>b. False \<and> b \<equiv> False\<close>
  \<open>\<And>n. 0 = Suc n \<equiv> False\<close>
  \<open>\<And>n. Suc n = 0 \<equiv> False\<close>
  \<open>\<And>h t. [] = h # t \<equiv> False\<close>
  \<open>\<And>h t. h # t = [] \<equiv> False\<close>
  \<open>True = False \<equiv> False\<close>
  \<open>False = True \<equiv> False\<close>
  \<open>\<And>x y x' y'. (x,y) = (x',y') \<equiv> x = x' \<and> y = y'\<close>
  \<open>\<And>n n'. Suc n = Suc n' \<equiv> n = n'\<close>
  \<open>\<And>h t h' t'. h # t = h' # t' \<equiv> h = h' \<and> t = t'\<close>
  by ((simp only: simps(66)),
      (simp only: simps(67)),
      (simp only: simps(68)),
      (simp only: simps(69)),
      (simp only: simps(70)),
      (simp only: simps(71)),
      (simp only: simps(72)),
      (simp only: simps(73)),
      (simp only: simps(74)),
      (simp only: simps(75)),
      (simp only: simps(76)),
      (simp only: simps(77)),
      (simp only: simps(78)),
      (simp only: simps(79)),
      (simp only: simps(80)),
      (simp only: simps(81)),
      (simp only: simps(82)),
      (simp only: simps(83)),
      (simp only: simps(84)),
      (simp only: simps(85)),
      (simp only: simps(86)),
      (simp only: simps(87)),
      (simp only: simps(88)),
      (simp only: simps(89)),
      (simp only: simps(90)),
      (simp only: simps(91)),
      (simp only: simps(92)),
      (simp only: simps(93)),
      (simp only: simps(94)))

proposition \<open>check test\<close>
  unfolding test_def
  unfolding program(1)
  unfolding program(2)
  unfolding program(3-) data library
  unfolding program(2)
  unfolding program(3-) data library
  unfolding program(2)
  unfolding program(3-) data library
  unfolding program(2)
  unfolding program(3-) data library
  unfolding program(2)
  unfolding program(3-) data library
  unfolding program(2)
  unfolding program(3-) data library
  unfolding program(2)
  unfolding program(3-) data library
  by (rule TrueI)

proposition \<open>check test\<close>
  unfolding check_def
  unfolding main_def
  unfolding test_def
  by (simp add: iterator)

proposition \<open>check test\<close>
  by code_simp

proposition \<open>map length (map (repeat (solves) [[(0,test)]]) [1,2,3,4,5,6,7]) = [1,1,1,2,2,2,0]\<close>
  by code_simp

proposition \<open>repeat (solves) [[(0,test)]] (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = []\<close>
  unfolding repeat.simps
  unfolding test_def
  unfolding program data library
  by (rule TrueI)

proposition \<open>\<forall>m e. is_model_environment m e \<longrightarrow> fst m \<noteq> {}\<close>
  unfolding is_model_environment_def
  by fast

inductive_set calculation :: \<open>sequent \<Rightarrow> (nat \<times> sequent) set\<close> for s where
  \<open>(0,s) \<in> calculation s\<close> |
  \<open>(n,k) \<in> calculation s \<Longrightarrow> l \<in> set (solve k) \<Longrightarrow> (Suc n,l) \<in> calculation s\<close>

primrec semantics_alternative :: \<open>model \<Rightarrow> environment \<Rightarrow> nnf list \<Rightarrow> bool\<close> where
  \<open>semantics_alternative _ _ [] = False\<close> |
  \<open>semantics_alternative m e (h # t) = (semantics m e h \<or> semantics_alternative m e t)\<close>

definition valid :: \<open>nnf list \<Rightarrow> bool\<close> where
  \<open>valid l \<equiv> \<forall>m e. is_model_environment m e \<longrightarrow> semantics_alternative m e l\<close>

abbreviation (input) \<open>VALID \<equiv> valid = finite \<circ> calculation \<circ> map (Pair 0)\<close>

section \<open>Soundness and Completeness\<close>

subsection \<open>Basics\<close>

primrec increase :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>increase _ 0 = 0\<close> |
  \<open>increase f (Suc n) = Suc (f n)\<close>

primrec sv :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> nnf \<Rightarrow> nnf\<close> where
  \<open>sv f (Pre b i v) = Pre b i (map f v)\<close> |
  \<open>sv f (Con p q) = Con (sv f p) (sv f q)\<close> |
  \<open>sv f (Dis p q) = Dis (sv f p) (sv f q)\<close> |
  \<open>sv f (Uni p) = Uni (sv (increase f) p)\<close> |
  \<open>sv f (Exi p) = Exi (sv (increase f) p)\<close>

primrec bind :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bind x 0 = x\<close> |
  \<open>bind _ (Suc n) = n\<close>

definition inst :: \<open>nnf \<Rightarrow> nat \<Rightarrow> nnf\<close> where
  \<open>inst p x \<equiv> sv (bind x) p\<close>

lemma j1: \<open>(if h < x then h else if h = x then s else h - 1) =
 (if h - x = 0 then (if x - h = 0 then s else h) else dec h)\<close> for h :: nat
proof -
  obtain bb :: bool where
    f1: \<open>bb = (h - x = 0 \<longrightarrow> (x - h = 0 \<longrightarrow> (h < x \<longrightarrow> h = s) \<and> (\<not> h < x \<longrightarrow> h \<noteq> x \<longrightarrow> h - 1 = s))
        \<and> (x - h \<noteq> 0 \<longrightarrow> \<not> h < x \<longrightarrow> (h = x \<longrightarrow> s = h) \<and> (h \<noteq> x \<longrightarrow> h - 1 = h)))\<close>
    by metis
  then have \<open>bb \<and> (h - x = 0 \<or> (\<not> h < x \<or> h = dec h) \<and> (h < x \<or> (h \<noteq> x \<or> s = dec h)
            \<and> (h = x \<or> h - 1 = dec h)))\<close>
    by (metis dec.simps(2) diff_Suc_1 diffs0_imp_equal less_SucI not_less_eq old.nat.exhaust
        zero_less_Suc zero_less_diff)
  then show ?thesis
    using f1 by presburger
qed

lemma j2: \<open>(sub h x) = (h - x)\<close> for h :: nat
  by (induct x) (simp_all,simp add: nat_diff_split)

lemma j3: \<open>(if h < x then h else if h = x then s else h - 1) = (if sub h x = 0 then
          (if sub x h = 0 then s else h) else dec h)\<close> for h :: nat
  by (simp add: j1 j2)

lemma j4: \<open>more x s h (sub h x) = (if sub h x = 0 then (if sub x h = 0 then s else h) else dec h)\<close>
  for h :: nat
  by (metis over.simps(1) over.simps(2) more.simps(1) more.simps(2) old.nat.exhaust)

lemma j5: \<open>mend x s v = map (\<lambda>n. (if n < x then n else if n = x then s else n - 1)) v\<close>
  by (induct v) (simp_all add: j4,simp add: j2 nat_diff_split)

definition instt :: \<open>nnf \<Rightarrow> nat \<Rightarrow> nnf\<close> where
  \<open>instt p x \<equiv> subst 0 x p\<close>

primrec increases :: \<open>nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)\<close> where
  \<open>increases 0 x = x\<close> |
  \<open>increases (Suc n) x = increase (increases n x)\<close>

lemma increases_bind:
  \<open>(\<lambda>n. (if n < m then n else if n = m then x + m else n - 1)) n = increases m (bind x) n\<close>
proof (induct m arbitrary: n)
  case 0
  then show ?case
    by (induct n) simp_all
next
  case (Suc k)
  then have \<open>increases (Suc k) (bind x) n =
      increase (\<lambda>n. if n < k then n else if n = k then x + k else n - 1) n\<close>
    by simp
  then show ?case
    by (induct n) simp_all
qed

lemma subb_sv: \<open>subst m (x + m) p = sv (increases m (bind x)) p\<close>
proof (induct p arbitrary: m)
  case (Pre b i v)
  then show ?case
    using increases_bind j5 by simp
next
  case (Con p q)
  then show ?case
    by simp
next
  case (Dis p q)
  then show ?case
    by simp
next
  case (Uni p)
  have \<open>subst m (x + m) (Uni p) = Uni (subst (Suc m) (x + Suc m) p)\<close>
    by simp
  also have \<open>\<dots> = Uni (sv (increases (Suc m) (bind x)) p)\<close>
    using Uni by blast
  also have \<open>\<dots> = sv (increases m (bind x)) (Uni p)\<close>
    by simp
  finally show ?case .
next
  case (Exi p)
  have \<open>subst m (x + m) (Exi p) = Exi (subst (Suc m) (x + Suc m) p)\<close>
    by simp
  also have \<open>\<dots> = Exi (sv (increases (Suc m) (bind x)) p)\<close>
    using Exi by blast
  also have \<open>\<dots> = sv (increases m (bind x)) (Exi p)\<close>
    by simp
  finally show ?case .
qed

lemma instt: \<open>instt p x = inst p x\<close>
  unfolding inst_def instt_def
  using subb_sv by (metis add_cancel_left_right increases.simps(1))

lemma base: \<open>base s = map snd s\<close>
  by (induct s) simp_all

definition maps :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list\<close> where
  \<open>maps f l \<equiv> concat (map f l)\<close>

lemma frees: \<open>frees l = maps free l\<close>
  unfolding maps_def by (induct l) simp_all

lemma solves: \<open>solves l = maps solve l\<close>
  unfolding maps_def by (induct l) simp_all

lemma ms: \<open>maps solve = solves\<close>
  using ext solves by fastforce

primrec maxl :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>maxl [] = 0\<close> |
  \<open>maxl (h # t) = add (sub (maxl t) h) h\<close>

definition fresh' :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>fresh' l \<equiv> if null l then 0 else Suc (maxl l)\<close>

lemma fresh': \<open>fresh l = fresh' l\<close>
  unfolding fresh'_def by (induct l) (auto, metis null.simps(2) list.exhaust maxl.simps)

primrec repeat' :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  \<open>repeat' _ c 0 = c\<close> |
  \<open>repeat' f c (Suc n) = f (repeat' f c n)\<close>

lemma r: \<open>f (repeat f c n) = repeat f (f c) n\<close>
  by (induct n arbitrary: c) simp_all

lemma rr: \<open>repeat' f c n = repeat f c n\<close>
  by (induct n) (simp_all add: r)

primrec sub' :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sub' x 0 = x\<close> |
  \<open>sub' x (Suc n) = sub' (dec x) n\<close>

lemma d0: \<open>dec x = x-(1::nat)\<close>
  by (simp add: nat_diff_split)

lemma d1: \<open>sub' x y = x-(y::nat)\<close>
  using d0 diff_Suc_eq_diff_pred sub'.simps by (induct y arbitrary: x) presburger+

lemma dx: \<open>sub x y = sub' x y\<close>
  by (simp add: d1 j2)

lemma mmm: \<open>(add (sub n n') n') = (max n n')\<close>
proof (induct n' arbitrary: n)
  case 0 then show ?case by simp
next
  case Suc then show ?case
  proof -
    fix n'a :: nat and na :: nat
    assume a1: \<open>\<And>n. add (sub n n'a) n'a = max n n'a\<close>
    have f2: \<open>\<And>n na. n = 0 \<or> Suc (max na (n - 1)) = max (Suc na) n\<close>
      by (metis (lifting) Nitpick.case_nat_unfold max_Suc1)
    { assume \<open>na \<noteq> 0\<close>
      then have \<open>Suc (max n'a (dec na)) = max na (Suc n'a)\<close>
        using f2 by (metis (lifting) dec.simps(2) Suc_pred' max.commute not_gr0) }
    then have \<open>Suc (max n'a (dec na)) = max na (Suc n'a)\<close>
      by (metis max.commute max_0L dec.simps(1))
    then show \<open>add (sub na (Suc n'a)) (Suc n'a) = max na (Suc n'a)\<close>
      using a1 dx by simp
  qed
qed

lemma maps: \<open>maps f = (concat \<circ> map f)\<close>
  using maps_def comp_apply
  by fastforce

definition make_sequent :: \<open>nnf list \<Rightarrow> sequent\<close> where
  \<open>make_sequent l = map (\<lambda>p. (0,p)) l\<close>

definition list_sequent :: \<open>sequent \<Rightarrow> nnf list\<close> where
  \<open>list_sequent s = map snd s\<close>

definition fv_list :: \<open>nnf list \<Rightarrow> nat list\<close> where
  \<open>fv_list \<equiv> maps free\<close>

primrec is_axiom :: \<open>nnf list \<Rightarrow> bool\<close> where
  \<open>is_axiom [] = False\<close> |
  \<open>is_axiom (p # t) = ((\<exists>b i v. p = Pre b i v \<and> Pre (\<not> b) i v \<in> set t))\<close>

primrec member :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>member _ [] = False\<close> |
  \<open>member a (h # t) = (if a = h then True else member a t)\<close>

lemma member_set: \<open>member a l = (a \<in> set l)\<close>
  by (induct l) auto

lemma stop: \<open>stop [t @ [(0,r)]] (Pre (\<not> b) i v) l =
  (if member (Pre (\<not> b) i v) l then [] else [t @ [(0,r)]])\<close>
  by (induct l) simp_all

lemma pre: \<open>(n,(m,Pre b i v) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Pre b i v) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,Pre b i v)]) \<in> calculation(nfs)\<close>
  and con1: \<open>(n,(m,Con p q) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Con p q) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,p)]) \<in> calculation(nfs)\<close>
  and con2: \<open>(n,(m,Con p q) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Con p q) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,q)]) \<in> calculation(nfs)\<close>
  and dis: \<open>(n,(m,Dis p q) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Dis p q) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,p),(0,q)]) \<in> calculation(nfs)\<close>
  and uni: \<open>(n,(m,Uni p) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Uni p) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,sv (bind (fresh ((concat \<circ> map free) (list_sequent ((m,Uni p) # xs))))) p)])
      \<in> calculation(nfs)\<close>
  and exi: \<open>(n,(m,Exi p) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Exi p) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,sv (bind m) p),(Suc m,Exi p)]) \<in> calculation(nfs)\<close>
  using instt_def
  by (auto simp: instt list_sequent_def maps inst_def stop member_set calculation.intros base frees)

lemmas not_is_axiom_subs = pre con1 con2 dis uni exi

lemma calculation_init: \<open>(0,k) \<in> calculation s = (k = s)\<close>
  using calculation.simps
  by blast

lemma calculation_upwards:
  assumes \<open>(n,k) \<in> calculation s\<close> and \<open>\<not> is_axiom (list_sequent (k))\<close>
  shows \<open>(\<exists>l. (Suc n,l) \<in> calculation s \<and> l \<in> set (solve k))\<close>
proof (cases k)
  case Nil then show ?thesis using assms(1) calculation.intros(2) by auto
next
  case (Cons a _) then show ?thesis
  proof (cases a)
    case (Pair _ p) then show ?thesis
      using Cons assms calculation.intros(2)
      by (cases p) (fastforce simp: list_sequent_def stop member_set base)+
  qed
qed

lemma calculation_downwards: \<open>(Suc n,k) \<in> calculation s \<Longrightarrow>
  \<exists>t. (n,t) \<in> calculation s \<and> k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)\<close>
proof (erule calculation.cases)
  assume \<open>Suc n = 0\<close>
  then show ?thesis using list_sequent_def by simp
next
  fix m l k'
  assume 1: \<open>Suc n = Suc m\<close>
    and 2: \<open>k = k'\<close>
    and 3: \<open>(m,l) \<in> calculation s\<close>
    and 4: \<open>k' \<in> set (solve l)\<close>
  then show ?thesis
  proof (cases l)
    case Nil then show ?thesis using 1 2 3 4 list_sequent_def by fastforce
  next
    case (Cons a _) then show ?thesis
    proof (cases a)
      case (Pair _ p) then show ?thesis
        using 1 2 3 4 Cons list_sequent_def by (cases p) (auto simp: stop member_set base)
    qed
  qed
qed

lemma calculation_calculation_child:
  \<open>\<forall>s t. (Suc n,s) \<in> calculation t =
    (\<exists>k. k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t) \<and> (n,s) \<in> calculation k)\<close>
  by (induct n) (metis calculation.intros(2) calculation_downwards calculation_init,
      meson calculation.intros(2) calculation_downwards)

lemma calculation_progress:
  assumes \<open>(n,a # l) \<in> calculation s\<close> and \<open>\<not> is_axiom (list_sequent (a # l))\<close>
  shows \<open>(\<exists>k. (Suc n,l@k) \<in> calculation s)\<close>
proof (cases a)
  case (Pair _ p) then show ?thesis using assms by (cases p) (auto dest: not_is_axiom_subs)
qed

definition inc :: \<open>nat \<times> sequent \<Rightarrow> nat \<times> sequent\<close> where
  \<open>inc \<equiv> \<lambda>(n,fs). (Suc n,fs)\<close>

lemma inj_inc: \<open>inj inc\<close>
  by (simp add: inc_def inj_on_def)

lemma calculation: \<open>calculation s =
  insert (0,s) (inc ` (\<Union> (calculation ` {k. \<not> is_axiom (list_sequent s) \<and> k \<in> set (solve s)})))\<close>
proof (rule set_eqI,simp add: split_paired_all)
  fix n k
  show \<open>((n,k) \<in> calculation s) =
    (n = 0 \<and> k = s \<or> (n,k) \<in> inc ` (\<Union>x\<in>{k. \<not> is_axiom (list_sequent s) \<and> k \<in> set (solve s)}.
      calculation x))\<close>
    by (cases n) (auto simp: calculation_init calculation_calculation_child inc_def)
qed

lemma calculation_is_axiom:
  assumes \<open>is_axiom (list_sequent s)\<close>
  shows \<open>calculation s = {(0,s)}\<close>
proof (rule set_eqI,simp add: split_paired_all)
  fix n k
  show \<open>((n,k) \<in> calculation s) = (n = 0 \<and> k = s)\<close>
  proof (rule iffI)
    assume \<open>(n,k) \<in> calculation s\<close> then show \<open>(n = 0 \<and> k = s)\<close>
      using assms calculation.simps calculation_calculation_child by metis
  next
    assume \<open>(n = 0 \<and> k = s)\<close> then show \<open>(n,k) \<in> calculation s\<close>
      using assms calculation.simps by blast
  qed
qed

lemma is_axiom_finite_calculation: \<open>is_axiom (list_sequent s) \<Longrightarrow> finite (calculation s)\<close>
  by (simp add: calculation_is_axiom)

primrec failing_path :: \<open>(nat \<times> sequent) set \<Rightarrow> nat \<Rightarrow> (nat \<times> sequent)\<close> where
  \<open>failing_path ns 0 = (SOME x. x \<in> ns \<and> fst x = 0 \<and> infinite (calculation (snd x)) \<and>
    \<not> is_axiom (list_sequent (snd x)))\<close> |
  \<open>failing_path ns (Suc n) = (let fn = failing_path ns n in
    (SOME fsucn. fsucn \<in> ns \<and> fst fsucn = Suc n \<and> (snd fsucn) \<in> set (solve (snd fn)) \<and>
      infinite (calculation (snd fsucn)) \<and> \<not> is_axiom (list_sequent (snd fsucn))))\<close>

lemma f0:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
  shows \<open>f 0 \<in> (calculation s) \<and> fst (f 0) = 0 \<and> infinite (calculation (snd (f 0))) \<and>
    \<not> is_axiom (list_sequent (snd (f 0)))\<close>
proof -
  have \<open>\<And>p P. p \<notin> P \<or> fst p \<noteq> (0::nat) \<or> finite (calculation (snd p)) \<or>
    (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
      \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
      infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
      \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))\<close>
  proof -
    fix p :: \<open>nat \<times> (nat \<times> nnf) list\<close> and P :: \<open>(nat \<times> (nat \<times> nnf) list) set\<close>
    have f1: \<open>\<forall>p pa. \<not> p (pa::nat \<times> (nat \<times> nnf) list) \<or> p (Eps p)\<close> by (metis someI)
    { assume \<open>(SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
      \<not> is_axiom (list_sequent (snd p))) \<notin> P \<or> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) \<noteq> 0 \<or>
      finite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
      \<not> is_axiom (list_sequent (snd p))))) \<or> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and>
      fst p = 0 \<and> infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))\<close>
      then have \<open>\<not> ((SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
        \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
        infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
        \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))))\<close>
        by metis
      then have \<open>\<not> (p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
        \<not> is_axiom (list_sequent (snd p)))\<close>
        using f1 by (metis (mono_tags, lifting) someI)
      then have \<open>p \<notin> P \<or> fst p \<noteq> 0 \<or> finite (calculation (snd p)) \<or>
        (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
        \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
        infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
        \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))\<close>
        by (metis (no_types) is_axiom_finite_calculation) }
    then show \<open>p \<notin> P \<or> fst p \<noteq> 0 \<or> finite (calculation (snd p)) \<or>
       (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
       \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
       infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
       infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
       infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
       \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
       infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))\<close>
      by blast
  qed
  then have \<open>\<And>ps. fst (0::nat, ps) \<noteq> 0 \<or> finite (calculation (snd (0::nat, ps))) \<or>
    (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
    \<not> is_axiom (list_sequent (snd p))) \<in> calculation ps \<and>
    fst (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and>
    infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
    infinite (calculation (snd (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and>
    infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
    \<not> is_axiom (list_sequent (snd (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and>
    infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))\<close>
    by (meson calculation.simps)
  then show ?thesis
    using assms(1) assms(2) by auto
qed

lemma infinite_union: \<open>finite Y \<Longrightarrow> infinite (Union (f ` Y)) \<Longrightarrow> \<exists>y. y \<in> Y \<and> infinite (f y)\<close>
  by auto

lemma finite_subs: \<open>finite {w. \<not> is_axiom (list_sequent y) \<and> w \<in> set (solve y)}\<close>
  by simp

lemma fSuc:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and>
    \<not> is_axiom (list_sequent (snd (f n)))\<close>
  shows \<open>f (Suc n) \<in> calculation s \<and> fst (f (Suc n)) = Suc n \<and> (snd (f (Suc n)))
    \<in> set (solve (snd (f n))) \<and> infinite (calculation (snd (f (Suc n)))) \<and>
    \<not> is_axiom (list_sequent (snd (f (Suc n))))\<close>
proof -
  have \<open>infinite (\<Union> (calculation ` {w. \<not> is_axiom (list_sequent (snd (f n))) \<and>
    w \<in> set (solve (snd (f n)))}))\<close>
    using assms
    by (metis (mono_tags,lifting) Collect_cong calculation finite.insertI finite_imageI)
  then show ?thesis using assms calculation.intros(2) is_axiom_finite_calculation
    by simp (rule someI_ex,simp,metis prod.collapse)
qed

lemma is_path_f_0: \<open>infinite (calculation s) \<Longrightarrow> failing_path (calculation s) 0 = (0,s)\<close>
  using calculation_init f0 prod.collapse
  by metis

lemma is_path_f':
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
  shows \<open>f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and>
    \<not> is_axiom (list_sequent (snd (f n)))\<close>
  using assms f0 fSuc
  by (induct n) simp_all

lemma is_path_f:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
  shows \<open>\<forall>n. f n \<in> calculation s \<and> fst (f n) = n \<and> (snd (f (Suc n))) \<in> set (solve (snd (f n))) \<and>
    infinite (calculation (snd (f n)))\<close>
  using assms is_path_f' fSuc
  by simp

lemma dump: \<open>Suc n \<in> set l = (n \<in> set (dump l))\<close>
proof (induct l)
  case Nil then show ?case by simp
next
  case (Cons m _) then show ?case by (cases m) simp_all
qed

lemma ts0: \<open>(\<And>e e'. \<forall>x. x \<in> set (free p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p)
  \<Longrightarrow> \<forall>x. x \<in> set (dump (free p)) \<longrightarrow> e x = e' x \<Longrightarrow>
  (\<forall>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p) =
    (\<forall>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e' n) p)\<close>
proof -
  assume a1: \<open>\<And>e e'. \<forall>x. x \<in> set (free p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p\<close>
  assume a2: \<open>\<forall>x. x \<in> set (dump (free p)) \<longrightarrow> e x = e' x\<close>
  have f3: \<open>((\<forall>us. us \<in> fst m \<longrightarrow> semantics m (case_nat us e) p) \<noteq> (\<forall>us. us \<in> fst m \<longrightarrow>
    semantics m (case_nat us e') p)) = ((\<exists>us. us \<in> fst m \<and>
    \<not> semantics m (case_nat us e) p) = (\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e') p))\<close>
    by blast
  obtain uus and uusa where
    f4: \<open>((\<exists>us. us \<in> fst m \<and> \<not> semantics m (case_nat us e) p) =
      (\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e') p)) =
      (((\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e) p) \<or>
        (\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e') p)) \<and>
        (uusa \<in> fst m \<and> \<not> semantics m (case_nat uusa e) p \<or> uus \<in> fst m \<and>
        \<not> semantics m (case_nat uus e') p))\<close>
    by (metis (no_types))
  then have \<open>(\<exists>us. us \<in> fst m \<and> \<not> semantics m (case_nat us e) p) \<and>
    (\<exists>us. us \<in> fst m \<and> \<not> semantics m (case_nat us e') p) \<or>
    (uusa \<notin> fst m \<or> semantics m (case_nat uusa e) p) \<and> (uus \<notin> fst m \<or>
    semantics m (case_nat uus e') p)\<close>
    using a2 a1 by (metis (no_types,lifting) Nitpick.case_nat_unfold Suc_pred' dump neq0_conv)
  then have \<open>(\<forall>us. us \<in> fst m \<longrightarrow> semantics m (case_nat us e) p) =
    (\<forall>us. us \<in> fst m \<longrightarrow> semantics m (case_nat us e') p)\<close>
    using f4 f3 by blast
  then show ?thesis
    by blast
qed

lemma ts1: \<open>(\<And>e e'. \<forall>x. x \<in> set (free p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p)
  \<Longrightarrow> \<forall>x. x \<in> set (dump (free p)) \<longrightarrow> e x = e' x \<Longrightarrow>
  (\<exists>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p) =
    (\<exists>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e' n) p)\<close>
proof -
  assume a1: \<open>\<And>e e'. \<forall>x. x \<in> set (free p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p\<close>
  assume a2: \<open>\<forall>x. x \<in> set (dump (free p)) \<longrightarrow> e x = e' x\<close>
  have f3: \<open>\<forall>us f n. if n = 0 then (case n of 0 \<Rightarrow> us | Suc x \<Rightarrow> f x) =
    us else (case n of 0 \<Rightarrow> us | Suc x \<Rightarrow> f x) = f (n - 1)\<close>
    by (simp add: Nitpick.case_nat_unfold)
  obtain uus and uusa where
    f4: \<open>((\<forall>us. us \<notin> fst m \<or> \<not> semantics m (case_nat us e) p) =
      (\<exists>us. us \<in> fst m \<and> semantics m (case_nat us e') p)) =
      ((uusa \<in> fst m \<and> semantics m (case_nat uusa e) p \<or> uus \<in> fst m \<and>
      semantics m (case_nat uus e') p) \<and> ((\<forall>us. us \<notin> fst m \<or> \<not> semantics m (case_nat us e) p) \<or>
      (\<forall>us. us \<notin> fst m \<or> \<not> semantics m (case_nat us e') p)))\<close>
    by blast
  have \<open>(uusa \<notin> fst m \<or> \<not> semantics m (case_nat uusa e) p) \<and> (uus \<notin> fst m \<or>
    \<not> semantics m (case_nat uus e') p) \<or> (\<exists>us. us \<in> fst m \<and> semantics m (case_nat us e) p) \<and>
      (\<exists>us. us \<in> fst m \<and> semantics m (case_nat us e') p)\<close>
    using f3 a2 a1
  proof -
    obtain nn :: \<open>(nat \<Rightarrow> proxy) \<Rightarrow> (nat \<Rightarrow> proxy) \<Rightarrow> nat\<close> where
      f1: \<open>\<forall>f fa. nn fa f \<in> set (free p) \<and> f (nn fa f) \<noteq> fa (nn fa f) \<or>
          semantics m f p = semantics m fa p\<close>
      using a1 by metis
    have \<open>\<forall>p f n. if n = 0 then (case n of 0 \<Rightarrow> p::proxy | Suc x \<Rightarrow> f x) = p else
        (case n of 0 \<Rightarrow> p | Suc x \<Rightarrow> f x) = f (n - 1)\<close>
      by (simp add: Nitpick.case_nat_unfold)
    then show ?thesis
      using f1 by (metis (no_types) Suc_pred' a2 dump not_gr0)
  qed
  then show ?thesis
    using f4 by blast
qed

lemma eval_cong: \<open>\<forall>x. x \<in> set (free p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p\<close>
proof (induct p arbitrary: e e')
  case (Pre x1 x2 x3)
  then show ?case
  proof -
    have f1: \<open>map e x3 = map e' x3\<close>
      using Pre by fastforce
    moreover
    { assume \<open>\<not> snd m x2 (map e x3)\<close>
      then have \<open>\<not> semantics m e' (Pre x1 x2 x3) \<or> \<not> x1\<close>
        using f1 by auto }
    moreover
    { assume \<open>\<not> semantics m e' (Pre x1 x2 x3)\<close>
      moreover
      { assume \<open>\<not> semantics m e' (Pre x1 x2 x3) \<and> snd m x2 (map e x3)\<close>
        then have \<open>\<not> x1\<close>
          using f1 by simp }
      ultimately have \<open>\<not> x1 \<or> (\<not> semantics m e (Pre x1 x2 x3)) \<noteq> semantics m e' (Pre x1 x2 x3)\<close>
        using semantics.simps(1) by blast }
    ultimately have \<open>(\<not> semantics m e (Pre x1 x2 x3)) \<noteq> semantics m e' (Pre x1 x2 x3)\<close>
      using semantics.simps(1) by metis
    then show ?thesis
      by blast
  qed
next
  case Con then show ?case using Un_iff free.simps(2) semantics.simps(2) set_append by metis
next
  case Dis then show ?case using Un_iff free.simps(3) semantics.simps(3) set_append by metis
next
  case Uni then show ?case using ts0 by simp
next
  case Exi then show ?case using ts1 by simp
qed

lemma semantics_alternative_def2: \<open>semantics_alternative m e s = (\<exists>p. p \<in> set s \<and> semantics m e p)\<close>
  by (induct s) auto

lemma semantics_alternative_append: \<open>semantics_alternative m e (s @ s') =
  ((semantics_alternative m e s) \<or> (semantics_alternative m e s'))\<close>
  by (induct s) auto

lemma fv_list_cons: \<open>fv_list (a # list) = (free a) @ (fv_list list)\<close>
  by (simp add: fv_list_def maps)

lemma semantics_alternative_cong: \<open>(\<forall>x. x \<in> set (fv_list s) \<longrightarrow> e x = e' x) \<longrightarrow>
  semantics_alternative m e s = semantics_alternative m e' s\<close>
  by (induct s) (simp,metis eval_cong Un_iff set_append fv_list_cons semantics_alternative.simps(2))

subsection \<open>Soundness\<close>

lemma ball: \<open>\<forall>x \<in> m. P x = Q x \<Longrightarrow> (\<exists>x \<in> m. P x) = (\<exists>x \<in> m. Q x)\<close>
  by simp_all

definition bump' :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bump' f x \<equiv> (case x of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n))\<close>

lemma bump': \<open>increase f x = bump' f x\<close>
  by (metis Nitpick.case_nat_unfold increase.simps Suc_pred' bump'_def not_gr0)

lemma s0: \<open>semantics m e (sv f p) = semantics m (e \<circ> f) p \<Longrightarrow>
  (\<And>p e e' m. \<forall>x. x \<in> set (free p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p) \<Longrightarrow>
  (\<forall>z\<in>fst m. semantics m (case_nat z e \<circ> increase f) p) =
    (\<forall>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> (e \<circ> f) n) p)\<close>
proof -
  assume a1: \<open>\<And>p e e' m. \<forall>x. x \<in> set (free p) \<longrightarrow>
              e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p\<close>
  obtain q :: proxy and a :: proxy where
    f2: \<open>((\<exists>pa. pa \<in> fst m \<and> \<not> semantics m (case_nat pa e \<circ> increase f) p) = (\<forall>pa. pa \<notin> fst m \<or>
      semantics m (case_nat pa (e \<circ> f)) p)) = (((\<forall>pa. pa \<notin> fst m \<or> semantics m (case_nat pa e \<circ>
      increase f) p) \<or> (\<forall>pa. pa \<notin> fst m \<or> semantics m (case_nat pa (e \<circ> f)) p)) \<and> (a \<in> fst m \<and>
      \<not> semantics m (case_nat a e \<circ> increase f) p \<or> q \<in> fst m \<and>
      \<not> semantics m (case_nat q (e \<circ> f)) p))\<close>
    by moura
  have f3: \<open>\<forall>n f fa p. (\<exists>na. na \<in> set (free n) \<and> f na \<noteq> fa na)
           \<or> semantics p f n = semantics p fa n\<close>
    using a1 by (metis (no_types))
  obtain nn :: \<open>(nat \<Rightarrow> proxy) \<Rightarrow> (nat \<Rightarrow> proxy) \<Rightarrow> nnf \<Rightarrow> nat\<close> where
    \<open>\<forall>x1 x2 x3. (\<exists>v4. v4 \<in> set (free x3) \<and> x2 v4 \<noteq> x1 v4) = (nn x1 x2 x3 \<in> set (free x3) \<and> x2
      (nn x1 x2 x3) \<noteq> x1 (nn x1 x2 x3))\<close>
    by moura
  then have f4: \<open>\<forall>n f fa p. nn fa f n \<in> set (free n) \<and> f (nn fa f n) \<noteq> fa (nn fa f n) \<or>
      semantics p f n = semantics p fa n\<close>
    using f3 by presburger
  have f5: \<open>\<forall>p f n. if n = 0 then (case n of 0 \<Rightarrow> p::proxy | Suc x \<Rightarrow> f x) = p else
    (case n of 0 \<Rightarrow> p | Suc x \<Rightarrow> f x) = f (n - 1)\<close>
    by (metis (no_types) Nitpick.case_nat_unfold)
  then have f6: \<open>(case increase f (nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p) of 0 \<Rightarrow> a
      | Suc x \<Rightarrow> e x) = a \<and> (case_nat a e \<circ> increase f) (nn (case_nat a (e \<circ> f)) (case_nat a e \<circ>
      increase f) p) \<noteq> (case nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p of 0 \<Rightarrow> a |
      Suc x \<Rightarrow> (e \<circ> f) x) \<longrightarrow> nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p \<noteq> 0\<close>
    by (metis o_apply)
  have f7: \<open>\<forall>n f na. if na = 0 then (case na of 0 \<Rightarrow> n::nat | Suc x \<Rightarrow> f x) = n else
    (case na of 0 \<Rightarrow> n | Suc x \<Rightarrow> f x) = f (na - 1)\<close>
    by (simp add: Nitpick.case_nat_unfold)
  have \<open>(case_nat a e \<circ> increase f) (nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p) \<noteq>
    (case nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p of 0 \<Rightarrow> a | Suc x \<Rightarrow> (e \<circ> f) x)
    \<longrightarrow> nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p \<noteq> 0\<close>
    using f6 bump'_def by fastforce
  then have f8: \<open>(case_nat a e \<circ> increase f) (nn (case_nat a (e \<circ> f))
    (case_nat a e \<circ> increase f) p) \<noteq> (case nn (case_nat a (e \<circ> f))
    (case_nat a e \<circ> increase f) p of 0 \<Rightarrow> a | Suc x \<Rightarrow> (e \<circ> f) x)
    \<longrightarrow> (case_nat a e \<circ> increase f) (nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p) =
    (case nn (case_nat a (e \<circ> f)) (case_nat a e \<circ> increase f) p of 0 \<Rightarrow> a | Suc x \<Rightarrow> (e \<circ> f) x)\<close>
    using f7 f5 bump'_def bump' by force
  have f9: \<open>nn (case_nat q (e \<circ> f)) (case_nat q e \<circ> increase f) p \<noteq> 0 \<longrightarrow>
    (case_nat q e \<circ> increase f)
    (nn (case_nat q (e \<circ> f)) (case_nat q e \<circ> increase f) p) = (case nn (case_nat q (e \<circ> f))
    (case_nat q e \<circ> increase f) p of 0 \<Rightarrow> q | Suc x \<Rightarrow> (e \<circ> f) x)\<close>
    using f7 f5 by (simp add: bump'_def bump')
  then have \<open>(case_nat q e \<circ> increase f) (nn (case_nat q (e \<circ> f)) (case_nat q e \<circ> increase f) p) \<noteq>
    (case nn (case_nat q (e \<circ> f)) (case_nat q e \<circ> increase f) p of 0 \<Rightarrow> q | Suc x \<Rightarrow> (e \<circ> f) x) \<longrightarrow>
    increase f (nn (case_nat q (e \<circ> f)) (case_nat q e \<circ> increase f) p) = 0\<close>
    using f7 by (metis bump' bump'_def)
  then have \<open>(case_nat q e \<circ> increase f) (nn (case_nat q (e \<circ> f)) (case_nat q e \<circ> increase f) p) =
    (case nn (case_nat q (e \<circ> f)) (case_nat q e \<circ> increase f) p of 0 \<Rightarrow> q | Suc x \<Rightarrow> (e \<circ> f) x)\<close>
    using f9 f5 by (metis (no_types) o_apply)
  then have \<open>(\<exists>pa. pa \<in> fst m \<and> \<not> semantics m (case_nat pa e \<circ> increase f) p) \<and> (\<exists>pa. pa \<in> fst m
    \<and> \<not> semantics m (case_nat pa (e \<circ> f)) p) \<or> (a \<notin> fst m \<or>
    semantics m (case_nat a e \<circ> increase f) p) \<and> (q \<notin> fst m \<or> semantics m (case_nat q (e \<circ> f)) p)\<close>
    using f8 f4 by (metis (no_types, lifting))
  then show ?thesis
    using f2 by blast
qed

lemma eval_subst: \<open>semantics m e (sv f p) = semantics m (e \<circ> f) p\<close>
  by (induct p arbitrary: e f) (simp,simp,simp,
      simp add: s0 eval_cong,simp add: Nitpick.case_nat_unfold ball bump'_def eval_cong bump')

definition bind' :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bind' y x \<equiv> (case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n)\<close>

lemma bind': \<open>bind y x = bind' y x\<close>
  by (metis Nitpick.case_nat_unfold bind.simps Suc_pred' bind'_def not_gr0)

lemma eval_bind: \<open>semantics m e (sv (bind n) p) = semantics m (case_nat (e n) e) p\<close>
  using eval_cong eval_subst
  by (simp add: Nitpick.case_nat_unfold bind'_def bind')

lemma sound_Uni':
  assumes \<open>u \<notin> set (fv_list (Uni p # s))\<close>
    and \<open>valid (s@[sv (bind u) p])\<close>
  shows \<open>is_model_environment (M,I) e \<Longrightarrow> \<not> semantics_alternative (M,I) e s \<Longrightarrow> z \<in> M \<Longrightarrow>
    semantics (M,I) (case_nat z e) p\<close>
proof -
  assume zM: \<open>z \<in> M\<close> and sa: \<open>\<not> semantics_alternative (M,I) e s\<close>
    and ime: \<open>is_model_environment (M,I) e\<close>
  have 1: \<open>semantics (M,I) (case_nat z (e(u:=z))) p = semantics (M,I) (case_nat z e) p\<close>
    using assms
    by (clarsimp simp: Nitpick.case_nat_unfold fv_list_cons intro!: eval_cong[rule_format])
      (metis One_nat_def Suc_pred' dump)
  have \<open>is_model_environment (M,I) (e(u := z)) \<longrightarrow> semantics_alternative (M,I) (e(u := z))
      (s @ [sv (bind u) p])\<close>
    using assms valid_def by blast
  then have 2: \<open>(\<forall>n. (if n = u then z else e n) \<in> M) \<longrightarrow>
      semantics_alternative (M,I) (e(u := z)) s \<or> semantics (M,I) (case_nat z e) p\<close>
    using 1 eval_bind is_model_environment_def semantics_alternative_append by simp
  have 3: \<open>u \<notin> set (dump (free p)) \<and> u \<notin> set (fv_list s)\<close>
    using assms fv_list_cons by simp
  have \<open>\<forall>n. e n \<in> M\<close>
    using ime is_model_environment_def by simp
  then show ?thesis
    using 2 3 zM sa
    by (metis (no_types,lifting) fun_upd_apply semantics_alternative_cong)
qed

lemma sound_Uni:
  assumes \<open>u \<notin> set (fv_list (Uni p # s))\<close>
    and \<open>valid (s@[sv (bind u) p])\<close>
  shows \<open>valid (Uni p # s)\<close>
  by (clarsimp simp: valid_def) (meson sound_Uni' assms eval_cong unit.exhaust)

lemma sound_Exi: \<open>valid (s@[sv (bind u) p,Exi p]) \<Longrightarrow> valid (Exi p # s)\<close>
  using valid_def eval_bind
proof -
  assume a1: \<open>valid (s @ [sv (bind u) p, Exi p])\<close>
  obtain pp :: \<open>nnf list \<Rightarrow> proxy set \<times> (nat \<Rightarrow> proxy list \<Rightarrow> bool)\<close>
    and uu :: \<open>nnf list \<Rightarrow> nat \<Rightarrow> proxy\<close> where
    f2: \<open>\<forall>ns. (\<not> valid ns \<or> (\<forall>p f. \<not> is_model_environment p f \<or> semantics_alternative p f ns))
 \<and> (valid ns \<or> is_model_environment (pp ns) (uu ns) \<and> \<not> semantics_alternative (pp ns) (uu ns) ns)\<close>
    using valid_def by moura
  then have \<open>\<forall>pa f. \<not> is_model_environment pa f \<or>
 semantics_alternative pa f (s @ [sv (bind u) p, Exi p])\<close>
    using a1 by auto
  then have \<open>\<not> is_model_environment (pp (Exi p # s)) (uu (Exi p # s)) \<or>
 semantics_alternative (pp (Exi p # s)) (uu (Exi p # s)) (Exi p # s)\<close>
    using eval_bind append_Nil2 is_model_environment_def
      semantics.simps(5) semantics_alternative.simps(2) semantics_alternative_append
    by metis
  then show ?thesis
    using f2 by blast
qed

lemma max_exists: \<open>finite (X::nat set) \<Longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>x. x \<in> X \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<le> x))\<close>
  using Max.coboundedI Max_in
  by blast

definition init :: \<open>sequent \<Rightarrow> bool\<close> where
  \<open>init s == \<forall>x \<in> (set s). fst x = 0\<close>

definition is_Exi :: \<open>nnf \<Rightarrow> bool\<close> where
  \<open>is_Exi f \<equiv> case f of Exi _ \<Rightarrow> True | _ \<Rightarrow> False\<close>

lemma is_Exi: \<open>\<not> is_Exi (Pre b i v) \<and> \<not> is_Exi (Con p q) \<and> \<not> is_Exi (Dis p q) \<and> \<not> is_Exi (Uni p)\<close>
  using is_Exi_def
  by simp

lemma index0:
  assumes \<open>init s\<close>
  shows \<open>\<forall>k m p. (n,k) \<in> calculation s \<longrightarrow> (m,p) \<in> (set k) \<longrightarrow> \<not> is_Exi p \<longrightarrow> m = 0\<close>
proof (induct n)
  case 0 then show ?case using assms init_def calculation_init by fastforce
next
  case IH: (Suc x)
  then show ?case
  proof (intro allI impI)
    fix k m p
    show \<open>(Suc x,k) \<in> calculation s \<Longrightarrow> (m,p) \<in> (set k) \<Longrightarrow> \<not> is_Exi p \<Longrightarrow> m = 0\<close>
    proof -
      assume \<open>(Suc x,k) \<in> calculation s\<close> and 1: \<open>(m,p) \<in> (set k)\<close> and 2: \<open>\<not> is_Exi p\<close>
      then obtain t
        where 3: \<open>(x,t) \<in> calculation s \<and> k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)\<close>
        using calculation_downwards by blast
      then show ?thesis
      proof (cases t)
        case Nil then show ?thesis using assms IH 1 3 by simp
      next
        case (Cons a _) then show ?thesis
        proof (cases a)
          case (Pair _ q)
          then show ?thesis using 1 2 3 IH Cons
            by (cases q) (fastforce simp: list_sequent_def stop is_Exi_def member_set base)+
        qed
      qed
    qed
  qed
qed

lemma maxl: \<open>\<forall>v \<in> set l. v \<le> maxl l\<close>
  by (induct l) (auto simp: max_def mmm)

lemma fresh: \<open>fresh l \<notin> (set l)\<close>
  unfolding fresh'_def fresh'
  using maxl maxl.simps not_less_eq_eq order_refl empty_iff list.set(1) null.simps(2) list.exhaust
  by metis

lemma soundness':
  assumes \<open>init s\<close>
    and \<open>m \<in> (fst ` (calculation s))\<close>
    and \<open>\<forall>y u. (y,u) \<in> (calculation s) \<longrightarrow> y \<le> m\<close>
  shows \<open>\<forall>n t. h = m - n \<and> (n,t) \<in> calculation s \<longrightarrow> valid (list_sequent t)\<close>
proof (induct h)
  case 0 then show ?case
  proof (intro allI impI)
    fix n t
    show \<open>0 = m - n \<and> (n,t) \<in> calculation s \<Longrightarrow> valid (list_sequent t)\<close>
    proof -
      assume *: \<open>0 = m - n \<and> (n,t) \<in> calculation s\<close>
      then show ?thesis
      proof (cases \<open>is_axiom (list_sequent t)\<close>)
        case True then show ?thesis
        proof (cases t)
          case Nil then show ?thesis using True list_sequent_def by simp
        next
          case Cons then show ?thesis
            using True list_sequent_def valid_def semantics_alternative_def2
            by simp (metis (no_types,lifting) semantics.simps(1))
        qed
      next
        case False
        then have \<open>n = m\<close> using assms * by fastforce
        then show ?thesis using assms * False
          by (meson calculation_upwards le_SucI le_antisym n_not_Suc_n)
      qed
    qed
  qed
next
  case IH: (Suc x) then show ?case
  proof (intro allI impI)
    fix n t
    show \<open>Suc x = m - n \<and> (n,t) \<in> calculation s \<Longrightarrow> valid (list_sequent t)\<close>
    proof -
      assume \<open>Suc x = m - n \<and> (n,t) \<in> calculation s\<close>
      then have *: \<open>Suc x = m - n\<close> and **: \<open>(n,t) \<in> calculation s\<close>
        by (simp,simp)
      then show ?thesis
      proof (cases \<open>is_axiom (list_sequent t)\<close>)
        case True then show ?thesis
        proof (cases t)
          case Nil then show ?thesis using True list_sequent_def by simp
        next
          case Cons then show ?thesis
            using True list_sequent_def valid_def semantics_alternative_def2
            by simp (metis (no_types,lifting) semantics.simps(1))
        qed
      next
        case notAxiom: False then show ?thesis
        proof (cases \<open>\<exists>a f list. t = (a,Uni f) # list\<close>)
          case True
          then obtain a and f and list where 1: \<open>t = (a,Uni f) # list\<close> by blast
          then show ?thesis
          proof -
            have f1: \<open>(n, (a, Uni f) # list) \<in> calculation s\<close>
              using ** 1 by simp
            have f2: \<open>\<not> is_axiom (list_sequent ((a, Uni f) # list))\<close>
              using 1 notAxiom by simp
            have f3: \<open>fresh ((concat \<circ> map free) (list_sequent ((a, Uni f) # list))) \<notin>
                       set (fv_list (Uni f # map snd list))\<close>
              using base base.simps(2) fresh fv_list_def list_sequent_def maps snd_conv by metis
            obtain nn :: \<open>nat \<Rightarrow> nat\<close> where
              f4: \<open>\<forall>x0. (\<exists>v2. x0 = Suc v2) = (x0 = Suc (nn x0))\<close>
              by moura
            have f5: \<open>\<forall>n na. \<not> (n::nat) \<le> na \<or> na - (na - n) = n\<close>
              using diff_diff_cancel by blast
            have f6: \<open>\<forall>n na. \<not> n \<le> na \<or> Suc na - n = Suc (na - n)\<close>
              using Suc_diff_le by blast
            have \<open>Suc n \<le> m\<close>
              using f2 f1 assms(3) uni by blast
            then have f7: \<open>(Suc x = Suc (m - Suc n)) = (m - n = Suc m - Suc (m - (m - n)))\<close>
              using f6 f5 f4 * ** assms(3) by metis
            moreover
            { assume \<open>m - n \<noteq> Suc m - Suc (m - (m - n))\<close>
              have \<open>m - n \<le> Suc m\<close>
                by simp
              then have \<open>x = m - Suc n\<close>
                using f7 f6 f5 diff_le_self library(28) by metis }
            ultimately have \<open>valid (list_sequent (list @ [(0, sv (bind (fresh ((concat \<circ> map free)
                              (list_sequent ((a, Uni f) # list))))) f)]))\<close>
              using f2 f1 IH.hyps library(28) uni by metis
            then have \<open>valid (Uni f # map snd list)\<close>
              using f3 list_sequent_def sound_Uni by simp
            then have \<open>valid (list_sequent ((a, Uni f) # list))\<close>
              using list_sequent_def by simp
            then show ?thesis
              using 1 by simp
          qed
        next
          case notUni: False then show ?thesis
          proof (cases \<open>\<exists>a f list. t = (a,Exi f) # list\<close>)
            case True
            then obtain a and f and list where 1: \<open>t = (a,Exi f) # list\<close> by blast
            then show ?thesis using IH assms * ** fresh list_sequent_def inst_def instt
              using instt_def
              by simp (frule calculation.intros(2),simp,
                  metis (no_types,lifting) Suc_leD diff_Suc_Suc diff_diff_cancel diff_le_self
                  le_SucI list.map map_append snd_conv sound_Exi)
          next
            case notExi: False
            then show ?thesis
            proof (cases t)
              case Nil
              then show ?thesis using assms notAxiom IH * ** calculation_upwards
                by (metis (no_types,lifting) calculation.intros(2) diff_Suc_Suc diff_diff_cancel
                    diff_le_self list.set_intros(1) not_less_eq_eq solve.simps(1))
            next
              case (Cons a list)
              then show ?thesis
                using IH
              proof (simp add: valid_def semantics_alternative_def2,intro allI impI)
                fix as gs g
                show \<open>\<forall>n t. x = m - n \<and> (n,t) \<in> calculation s \<longrightarrow>
                       (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow> (\<exists>p. p \<in> set (list_sequent t) \<and>
                         semantics (a,b) e p)) \<Longrightarrow>
                         is_model_environment (as,gs) g \<Longrightarrow> \<exists>p. p \<in> set (list_sequent (a # list))
                         \<and> semantics (as,gs) g p\<close>
                proof -
                  assume ***: \<open>is_model_environment (as,gs) g\<close>
                    and IH': \<open>\<forall>n t. x = m - n \<and> (n,t) \<in> calculation s \<longrightarrow>
                               (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                               (\<exists>p. p \<in> set (list_sequent t) \<and> semantics (a,b) e p))\<close>
                  then show ?thesis
                  proof (cases a)
                    case (Pair _ p) then show ?thesis
                    proof (cases p)
                      case (Pre b i v) then show ?thesis
                        using IH' assms * ** Cons notAxiom *** Pair
                        by (fastforce simp: list_sequent_def dest!: pre)
                    next
                      case (Con q r)
                      then have 1: \<open>(Suc n,list @ [(0,q)]) \<in> calculation s\<close>
                        using ** Pair con1 local.Cons notAxiom by blast
                      then have 2: \<open>x = m - Suc n \<and> (Suc n,list @ [(0,q)]) \<in> calculation s\<close>
                        using * by linarith
                      have 3: \<open>(Suc n,list @ [(0,r)]) \<in> calculation s\<close>
                        using ** Pair Con con2 local.Cons notAxiom by blast
                      then have 4: \<open>x = m - Suc n \<and> (Suc n,list @ [(0,r)]) \<in> calculation s\<close>
                        using * by linarith
                      then have 5: \<open>(Suc n,list @ [(0,q)]) \<in> calculation s \<longrightarrow>
                              (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                              (\<exists>p. p \<in> set (list_sequent (list @ [(0,q)])) \<and> semantics (a,b) e p))\<close>
                        using IH' by blast
                      then have \<open>x = m - Suc n \<and> (Suc n,list @ [(0,r)]) \<in> calculation s \<longrightarrow>
                            (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                            (\<exists>p. p \<in> set (list_sequent (list @ [(0,r)])) \<and> semantics (a,b) e p))\<close>
                        using 2 IH' by blast
                      then show ?thesis
                        using 5
                      proof (elim impE)
                        show \<open>(Suc n,list @ [(0,q)]) \<in> calculation s\<close> using 1 by simp
                      next
                        show \<open>\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                (\<exists>p. p \<in> set (list_sequent (list @ [(0,q)])) \<and>
                                  semantics (a,b) e p) \<Longrightarrow>
                                x = m - Suc n \<and> (Suc n,list @ [(0,r)]) \<in> calculation s\<close>
                          using 2 3 by blast
                      next
                        show \<open>\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                (\<exists>p. p \<in> set (list_sequent (list @ [(0,r)])) \<and>
                                  semantics (a,b) e p) \<Longrightarrow>
                                 (Suc n,list @ [(0,q)]) \<in> calculation s\<close>
                          using 1 by blast
                      next show \<open>\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                              (\<exists>p. p \<in> set (list_sequent (list @ [(0,r)])) \<and> semantics (a,b) e p)
                              \<Longrightarrow> \<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                              (\<exists>p. p \<in> set (list_sequent (list @ [(0,q)])) \<and> semantics (a,b) e p)
                              \<Longrightarrow> \<exists>p. p \<in> set (list_sequent (a # list)) \<and> semantics (as,gs) g p\<close>
                          using Con *** Pair list_sequent_def
                          by simp (metis (no_types,lifting) semantics.simps(2))
                      qed
                    next
                      case (Dis q r)
                      then have \<open>x = m - Suc n \<and> (Suc n,list @ [(0,q),(0,r)]) \<in> calculation s
                                  \<longrightarrow> (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                  (\<exists>p. p \<in> set (list_sequent (list @ [(0,q),(0,r)])) \<and>
                                  semantics (a,b) e p))\<close>
                        using * IH' by blast
                      then show ?thesis
                      proof (elim impE)
                        have 1: \<open>(Suc n,list @ [(0,q),(0,r)]) \<in> calculation s\<close>
                          using ** Dis Pair dis local.Cons notAxiom by blast
                        have \<open>x = m - Suc n\<close> using * by linarith
                        then show \<open>x = m - Suc n \<and> (Suc n,list @ [(0,q),(0,r)]) \<in> calculation s\<close>
                          using 1 by simp
                      next
                        show \<open>\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                               (\<exists>p. p \<in> set (list_sequent (list @ [(0,q),(0,r)])) \<and>
                                 semantics (a,b) e p) \<Longrightarrow>
                                 \<exists>p. p \<in> set (list_sequent (a # list)) \<and> semantics (as,gs) g p\<close>
                          using Dis *** Pair list_sequent_def
                          by simp (metis (no_types,lifting) semantics.simps(3))
                      qed
                    next
                      case Uni then show ?thesis
                        using notUni Pair Cons by blast
                    next
                      case Exi then show ?thesis
                        using notExi Pair Cons by blast
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma list_make_sequent_inverse: \<open>list_sequent (make_sequent s) = s\<close>
  using list_sequent_def make_sequent_def
  by (induct s) simp_all

lemma soundness:
  assumes \<open>finite (calculation (make_sequent s))\<close>
  shows \<open>valid s\<close>
proof -
  have \<open>init (make_sequent s)\<close> and \<open>finite (fst ` (calculation (make_sequent s)))\<close>
    using assms by (simp add: init_def make_sequent_def,simp)
  then show ?thesis using assms soundness' list_make_sequent_inverse max_exists
    by (metis (mono_tags,lifting) empty_iff fst_conv image_eqI calculation.intros(1))
qed

subsection \<open>Contains / Considers\<close>

definition contains :: \<open>(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> nnf \<Rightarrow> bool\<close> where
  \<open>contains f n nf \<equiv> nf \<in> set (snd (f n))\<close>

definition considers :: \<open>(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> nnf \<Rightarrow> bool\<close> where
  \<open>considers f n nf \<equiv> case snd (f n) of [] \<Rightarrow> False | (x # xs) \<Rightarrow> x = nf\<close>

lemma progress:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
  shows \<open>snd (f n) = a # l \<longrightarrow> (\<exists>zs'. snd (f (Suc n)) = l@zs')\<close>
proof -
  obtain suc: \<open>(snd (f (Suc n))) \<in> set (solve (snd (f n)))\<close> using assms is_path_f by blast
  then show ?thesis
  proof (cases a)
    case (Pair _ p)
    then show ?thesis using suc
      by (induct p,safe,simp_all add: stop split: if_splits) blast
  qed
qed

lemma contains_considers':
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
  shows \<open>\<forall>n ys. snd (f n) = xs@y # ys \<longrightarrow> (\<exists>m zs'. snd (f (n+m)) = y # zs')\<close>
proof (induct xs)
  case Nil then show ?case using append.simps(1) by (metis Nat.add_0_right)
next
  case Cons then show ?case using append.simps(2)
    by (metis (no_types,lifting) add_Suc_shift append_assoc assms progress)
qed

lemma contains_considers:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>contains f n y\<close>
  shows \<open>(\<exists>m. considers f (n+m) y)\<close>
  using assms
  by (clarsimp simp: contains_def considers_def dest!: split_list_first)
    (frule contains_considers'[rule_format],simp,simp,metis (mono_tags,lifting) list.simps(5))

lemma contains_propagates_Pre:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>contains f n (0,Pre b i v)\<close>
  shows \<open>contains f (n+q) (0,Pre b i v)\<close>
proof (induct q)
  case 0 then show ?case using assms by simp
next
  case IH: (Suc q')
  then have \<open>\<exists>ys zs. snd (f (n + q')) = ys @ (0,Pre b i v) # zs \<and> (0,Pre b i v) \<notin> set ys\<close>
    by (meson contains_def split_list_first)
  then obtain ys and zs where 1:
    \<open>snd (f (n + q')) = ys @ (0,Pre b i v) # zs \<and> (0,Pre b i v) \<notin> set ys\<close>
    by blast
  then have 2: \<open>(snd (f (Suc (n + q')))) \<in> set (solve (snd (f (n + q'))))\<close>
    using assms is_path_f by blast
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using 1 2 contains_def
      by (simp add: stop split: if_splits)
  next
    case (Cons a _) then show ?thesis
    proof (cases a)
      case (Pair _ p) then show ?thesis
        using 1 contains_def assms Cons progress by fastforce
    qed
  qed
qed

lemma contains_propagates_Con:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>contains f n (0,Con p q)\<close>
  shows \<open>(\<exists>y. contains f (n+y) (0,p) \<or> contains f (n+y) (0,q))\<close>
proof -
  have \<open>(\<exists>l. considers f (n+l) (0,Con p q))\<close> using assms contains_considers by blast
  then obtain l where 1: \<open>considers f (n+l) (0,Con p q)\<close> by blast
  then have 2: \<open>(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))\<close>
    using assms is_path_f by blast
  then show ?thesis
  proof (cases \<open>snd (f (n + l))\<close>)
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis using 1 2 considers_def contains_def
      by (rule_tac x=\<open>Suc l\<close> in exI) auto
  qed
qed

lemma contains_propagates_Dis:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>contains f n (0,Dis p q)\<close>
  shows \<open>(\<exists>y. contains f (n+y) (0,p) \<and> contains f (n+y) (0,q))\<close>
proof -
  have \<open>(\<exists>l. considers f (n+l) (0,Dis p q))\<close> using assms contains_considers by blast
  then obtain l where 1: \<open>considers f (n+l) (0,Dis p q)\<close> by blast
  then have 2: \<open>(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))\<close>
    using assms is_path_f by blast
  then show ?thesis
  proof (cases \<open>snd (f (n + l))\<close>)
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis using 1 2 considers_def contains_def
      by (rule_tac x=\<open>Suc l\<close> in exI) simp_all
  qed
qed

lemma contains_propagates_Uni:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>contains f n (0,Uni p)\<close>
  shows \<open>(\<exists>y. contains f (Suc(n+y)) (0,(sv (bind (fresh (fv_list (map snd (snd (f (n+y))))))) p)))\<close>
proof -
  have \<open>(\<exists>l. considers f (n+l) (0,Uni p))\<close> using assms contains_considers by blast
  then obtain l where 1: \<open>considers f (n+l) (0,Uni p)\<close> by blast
  then have 2: \<open>(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))\<close>
    using assms is_path_f by blast
  then show ?thesis
  proof (cases \<open>snd (f (n + l))\<close>)
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis
      using 1 2 considers_def contains_def inst_def instt base frees instt_def
      by (rule_tac x=\<open>l\<close> in exI) (simp add: fv_list_def maps_def)
  qed
qed

lemma contains_propagates_Exi:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>contains f n (m,Exi p)\<close>
  shows \<open>(\<exists>y. (contains f (n+y) (0,(sv (bind m) p)) \<and> (contains f (n+y) (Suc m,Exi p))))\<close>
proof -
  have \<open>(\<exists>l. considers f (n+l) (m,Exi p))\<close> using assms contains_considers by blast
  then obtain l where 1: \<open>considers f (n+l) (m,Exi p)\<close> by blast
  then have 2: \<open>(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))\<close>
    using assms is_path_f by blast
  then show ?thesis
  proof (cases \<open>snd (f (n + l))\<close>)
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis using 1 2 considers_def contains_def inst_def
      using instt instt_def by (rule_tac x=\<open>Suc l\<close> in exI) simp
  qed
qed

lemma Exi_downward:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
  shows \<open>\<forall>m. (Suc m,Exi g) \<in> set (snd (f n)) \<longrightarrow> (\<exists>n'. (m,Exi g) \<in> set (snd (f n')))\<close>
proof (induct n)
  case 0 then show ?case using assms init_def is_path_f_0 by fastforce
next
  case IH: (Suc x)
  then have fxSuc: \<open>f x \<in> calculation s \<and> fst (f x) = x \<and>
    snd (f (Suc x)) \<in> set (solve (snd (f x))) \<and> infinite (calculation (snd (f x)))\<close>
    using assms is_path_f by blast
  then show ?case
  proof (cases \<open>f x\<close>)
    case fxPair: (Pair _ l)
    then show ?thesis
    proof (cases l)
      case Nil then show ?thesis using fxSuc fxPair by simp
    next
      case (Cons a _) then show ?thesis
      proof (cases a)
        case (Pair _ p) then show ?thesis
        proof (cases p)
          case Pre then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp add: stop split: if_splits)
        next
          case Con then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits) fastforce
        next
          case Dis then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits)
        next
          case Uni then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits)
        next
          case Exi then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits) (metis list.set_intros(1) snd_eqD)
        qed
      qed
    qed
  qed
qed

lemma Exi0:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
  shows \<open>\<forall>n. contains f n (m,Exi g) \<longrightarrow> (\<exists>n'. contains f n' (0,Exi g))\<close>
  using assms Exi_downward contains_def
  by (induct m) auto

lemma Exi_upward':
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
  shows \<open>\<forall>n. contains f n (0,Exi g) \<longrightarrow> (\<exists>n'. contains f n' (m,Exi g))\<close>
  using assms contains_propagates_Exi
  by (induct m) (simp,blast)

lemma Exi_upward:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
    and \<open>contains f n (m,Exi g)\<close>
  shows \<open>(\<forall>m'. \<exists>n'. contains f n' (0,sv (bind m') g))\<close>
proof -
  fix m'
  have \<open>\<exists>n'. contains f n' (m',Exi g)\<close> using assms Exi0 Exi_upward' by metis
  then show ?thesis using assms contains_propagates_Exi Exi0 Exi_upward' by metis
qed

definition ntou :: \<open>nat \<Rightarrow> proxy\<close> where \<open>ntou n \<equiv> replicate n ()\<close>

lemma inj_ntou: \<open>inj ntou\<close>
  unfolding inj_def ntou_def using length_replicate by simp

hide_fact ntou_def

definition uton :: \<open>proxy \<Rightarrow> nat\<close> where \<open>uton \<equiv> inv ntou\<close>

lemma uton_ntou_id[simp]: \<open>uton \<circ> ntou = id\<close>
  unfolding uton_def using inj_ntou by simp

subsection \<open>Falsifying Model From Failing Path\<close>

definition model :: \<open>sequent \<Rightarrow> model\<close> where
  \<open>model s \<equiv> (range ntou,\<lambda> p ms. (let f = failing_path (calculation s) in
    (\<forall>n m. \<not> contains f n (m,Pre True p (map uton ms)))))\<close>

lemma is_env_model_ntou: \<open>is_model_environment (model s) ntou\<close>
  using is_model_environment_def model_def
  by simp

lemma not_is_Exi:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
    and \<open>(contains f n (m,p))\<close>
  shows \<open>\<not> is_Exi p \<Longrightarrow> m = 0\<close>
  using assms contains_def index0 is_path_f' prod.collapse
  by metis

lemma size_subst: \<open>size (sv f p) = size p\<close>
  by (induct p arbitrary: f) simp_all

lemma model'':
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
    and *: \<open>\<forall>m<n. \<forall>p. size p = m \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> semantics (model s) ntou p)\<close>
  shows \<open>p = Exi q \<Longrightarrow> n = Suc (size q) \<Longrightarrow> z \<in> fst (model s) \<Longrightarrow> contains f na (m,Exi q)
            \<Longrightarrow> semantics (model s) (case_nat z ntou) q \<Longrightarrow> False\<close>
proof -
  assume 1: \<open>n = Suc (size q)\<close>
  assume 2: \<open>z \<in> fst (model s)\<close>
  assume 3: \<open>contains f na (m,Exi q)\<close>
  assume 4: \<open>semantics (model s) (case_nat z ntou) q\<close>
  have \<open>semantics (model s) ntou (sv (bind (inv ntou z)) q)\<close>
    using 2 4 model_def eval_bind by (simp add: f_inv_into_f)
  then show ?thesis
    using 1 3 * assms(1) assms(2) assms(3) Exi_upward lessI size_subst by metis
qed

lemma model':
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
  shows \<open>\<forall>p. size p = h \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> (semantics (model s) ntou p))\<close>
proof (rule nat_less_induct,rule allI)
  fix p n
  show \<open>\<forall>m<n. \<forall>p. size p = m \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> semantics (model s) ntou p) \<Longrightarrow>
    size p = n \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> semantics (model s) ntou p)\<close>
  proof -
    assume *: \<open>\<forall>m<n. \<forall>p. size p = m \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow>
      \<not> semantics (model s) ntou p)\<close>
    show ?thesis
    proof (cases p)
      case (Pre b i v) then show ?thesis
      proof (cases b)
        case True then show ?thesis using Pre assms model_def by auto
      next
        case False then show ?thesis using Pre
        proof (clarsimp simp: model_def)
          fix na m nb ma
          show \<open>n = 0 \<Longrightarrow> contains f na (m,Pre False i v) \<Longrightarrow>
            contains (failing_path (calculation s)) nb (ma,Pre True i v) \<Longrightarrow> False\<close>
          proof -
            assume 1: \<open>contains f na (m,Pre False i v)\<close> and
              2: \<open>contains (failing_path (calculation s)) nb (ma,Pre True i v)\<close>
            then have 3: \<open>m = 0 \<and> ma = 0\<close> using assms is_Exi not_is_Exi by simp
            then have \<open>\<exists>y. considers (failing_path (calculation s)) (nb+na+y) (0,Pre True i v)\<close>
              using assms 2 contains_considers contains_propagates_Pre by simp
            then obtain y
              where 4: \<open>considers (failing_path (calculation s)) (nb+na+y) (0,Pre True i v)\<close>
              by blast
            then have 5: \<open>contains (failing_path (calculation s)) (na+nb+y) (0,Pre False i v)\<close>
              using assms 1 3 contains_propagates_Pre by simp
            then have 6: \<open>nb+na=na+nb\<close>
              by simp
            then have \<open>is_axiom (list_sequent (snd ((failing_path (calculation s)) (na+nb+y))))\<close>
            proof (cases \<open>snd ((failing_path (calculation s)) (na + nb + y))\<close>)
              case Nil then show ?thesis using 5 contains_def by simp
            next
              case Cons then show ?thesis
                using 4 5 6 unfolding contains_def list_sequent_def considers_def by force
            qed
            then show ?thesis using assms is_path_f' by blast
          qed
        qed
      qed
    next
      case Con then show ?thesis using assms * is_Exi not_is_Exi contains_propagates_Con
        by (metis Nat.add_0_right add_Suc_right nnf.size(7)
            less_add_Suc1 less_add_Suc2 semantics.simps(2))
    next
      case Dis then show ?thesis using assms * contains_propagates_Dis is_Exi not_is_Exi
        by (metis Nat.add_0_right add_Suc_right nnf.size(8)
            less_add_Suc1 less_add_Suc2 semantics.simps(3))
    next
      case (Uni q) then show ?thesis
      proof (intro impI allI)
        fix na m
        show \<open>size p = n \<Longrightarrow> contains f na (m,p) \<Longrightarrow> \<not> semantics (model s) ntou p\<close>
        proof -
          assume 1: \<open>size p = n\<close> and 2: \<open>contains f na (m,p)\<close>
          then have \<open>m = 0\<close> using assms Uni is_Exi not_is_Exi by simp
          then have \<open>\<exists>y. contains f (Suc (na + y)) (0,(sv (bind (fresh (fv_list
              (map snd (snd (f (na + y))))))) q))\<close>
            using assms Uni 2 contains_propagates_Uni by simp
          then obtain y where 3: \<open>contains f (Suc (na + y)) (0,sv (bind (fresh (fv_list
              (map snd (snd (f (na + y))))))) q)\<close>
            by blast
          have \<open>Suc (size q) = n\<close> using Uni 1 by simp
          then show ?thesis
            using Uni * 3 eval_bind is_env_model_ntou
              is_model_environment_def semantics.simps(4) size_subst by blast
        qed
      qed
    next
      case (Exi q)
      have \<open>p = Exi q \<Longrightarrow> n = Suc (size q) \<Longrightarrow> z \<in> fst (model s) \<Longrightarrow> contains f na (m,Exi q)
          \<Longrightarrow> semantics (model s) (case_nat z ntou) q \<Longrightarrow> False\<close> for z na m
        using model'' * assms by blast
      then show ?thesis
        using Exi add.right_neutral add_Suc_right nnf.size(10) semantics.simps(5) by metis
    qed
  qed
qed

lemma model:
  assumes \<open>f = failing_path (calculation s)\<close>
    and \<open>infinite (calculation s)\<close>
    and \<open>init s\<close>
  shows \<open>(\<forall>p m n. contains f n (m,p) \<longrightarrow> \<not> (semantics (model s) ntou p))\<close>
  using assms model'
  by simp

subsection \<open>Completeness\<close>

lemma completeness': \<open>infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow>
    \<forall>mA \<in> set s. \<not> semantics (model s) ntou (snd mA)\<close>
  by (metis contains_def eq_snd_iff is_path_f_0 model)

lemma completeness'': \<open>infinite (calculation (make_sequent s)) \<Longrightarrow>
    init (make_sequent s) \<Longrightarrow> \<forall>p. p \<in> set s \<longrightarrow> \<not> semantics (model (make_sequent s)) ntou p\<close>
  using completeness' make_sequent_def
  by fastforce

lemma completeness: \<open>infinite (calculation (make_sequent s)) \<Longrightarrow> \<not> valid s\<close>
  using valid_def init_def make_sequent_def is_env_model_ntou semantics_alternative_def2
    completeness''
  by (subgoal_tac \<open>init (make_sequent s)\<close>) (metis,simp)

subsection \<open>Algorithm\<close>

definition loop :: \<open>sequent list \<Rightarrow> nat \<Rightarrow> sequent list\<close> where
  \<open>loop s n \<equiv> repeat' (concat \<circ> map solve) s n\<close>

lemma loop_upwards: \<open>loop s n = [] \<Longrightarrow> loop s (n+m) = []\<close>
  using loop_def
  by (induct m) auto

lemma concat_append: \<open>concat (xs@ys) = ((concat xs) @ (concat ys))\<close>
  by (induct xs) auto

lemma set_concat: \<open>set (concat xs) = \<Union> (set ` set xs)\<close>
  by (induct xs) auto

lemma loop: \<open>\<forall>x. ((n,x) \<in> calculation s) = (x \<in> set (loop [s] n))\<close>
proof (induct n)
  case 0 then show ?case using loop_def calculation_init by simp
next
  case (Suc m) then show ?case
  proof (intro allI iffI)
    fix x ys z
    assume \<open>(Suc m,x) \<in> calculation s\<close>
    then have \<open>\<exists>t. (m,t) \<in> calculation s \<and> x \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)\<close>
      using calculation_downwards by blast
    then obtain t
      where 1: \<open>(m,t) \<in> calculation s \<and> x \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)\<close>
      by blast
    then show \<open>(x \<in> set (loop [s] (Suc m)))\<close>
      using Suc loop_def by (clarsimp dest!: split_list_first)
  next
    fix x
    assume \<open>(x \<in> set (loop [s] (Suc m)))\<close>
    then show \<open>(Suc m,x) \<in> calculation s\<close>
      using Suc by (fastforce simp: set_concat loop_def calculation.intros(2))
  qed
qed

lemma calculation_f: \<open>calculation s = UNION UNIV (\<lambda>x. set (map (\<lambda>y. (x,y)) (loop [s] x)))\<close>
  using loop
  by fastforce

lemma finite_calculation':
  assumes \<open>finite (calculation s)\<close>
  shows \<open>(\<exists>m. loop [s] m = [])\<close>
proof -
  have \<open>finite (fst ` (calculation s))\<close> using assms by simp
  then obtain x where xMax: \<open>x \<in> fst ` calculation s \<and> (\<forall>y. y \<in> fst ` calculation s \<longrightarrow> y \<le> x)\<close>
    using max_exists calculation.simps by (metis empty_iff image_is_empty)
  then show ?thesis
  proof (cases \<open>loop [s] (Suc x)\<close>)
    assume \<open>loop [s] (Suc x) = []\<close> then show ?thesis by blast
  next
    fix a l
    assume \<open>loop [s] (Suc x) = a # l\<close>
    then have \<open>(Suc x,a) \<in> calculation s\<close> using loop by simp
    then show ?thesis using xMax by fastforce
  qed
qed

lemma finite_calculation'':
  assumes \<open>(\<exists>m. loop [s] m = [])\<close>
  shows \<open>finite (calculation s)\<close>
proof -
  obtain m where \<open>loop [s] m = []\<close> using assms by blast
  then have \<open>\<forall>y. loop [s] (m+y) = []\<close> using loop_upwards by simp
  then have 1: \<open>(UN x:Collect (less_eq m). Pair x ` set (loop [s] x)) =
                (UN x:Collect (less_eq m). {})\<close>
    using SUP_cong image_is_empty le_Suc_ex mem_Collect_eq set_empty
    by (metis (no_types,lifting))
  then have \<open>(UNIV::nat set) = {y. y < m} Un {y. m \<le> y}\<close> by fastforce
  then show ?thesis using 1 calculation_f by (clarsimp elim!: ssubst)
qed

lemma finite_calculation: \<open>finite (calculation s) = (\<exists>m. loop [s] m = [])\<close>
  using finite_calculation' finite_calculation''
  by blast

corollary finite_calculation_prover': \<open>finite (calculation s) = iterator null (maps solve) [s]\<close>
  using finite_calculation loop_def iterator_def maps null.simps list.exhaust rr
  by metis

corollary finite_calculation_prover: \<open>finite (calculation s) = iterator null solves [s]\<close>
  using finite_calculation_prover' ms by simp

section \<open>Correctness\<close>

lemmas magic = soundness completeness finite_calculation_prover

theorem correctness: CHECK VALID
proof -
  have \<open>\<forall>p. [[(0,p)]] = [map (Pair 0) [p]]\<close> by simp
  then have CHECK
    unfolding check_def
    using magic valid_def make_sequent_def semantics_alternative.simps main_def
    by (metis (no_types,hide_lams))
  moreover have VALID
    using magic make_sequent_def by fastforce
  ultimately show CHECK VALID .
qed

corollary \<open>\<exists>p. check p\<close> \<open>\<exists>p. \<not> check p\<close>
proof -
  have \<open>\<not> valid [Pre True 0 []]\<close> \<open>valid [Dis (Pre True 0 []) (Pre False 0 [])]\<close>
    using valid_def is_model_environment_def by auto
  then show \<open>\<exists>p. check p\<close> \<open>\<exists>p. \<not> check p\<close>
    using correctness semantics_alternative.simps valid_def by (metis,metis)
qed

section \<open>Code Generation\<close>

value \<open>check test\<close>

value \<open>check (Dis (Pre True 0 []) (Pre False 0 []))\<close>

(* value \<open>check (Pre True 0 [])\<close> *)

proposition \<open>check test\<close>
  by eval

proposition \<open>check (Dis (Pre True 0 []) (Pre False 0 []))\<close>
  by eval

proposition \<open>check test\<close>
  by normalization

proposition \<open>check (Dis (Pre b i v) (Pre (\<not> b) i v))\<close>
  by normalization

code_reflect X datatypes nnf = _ and nat = _ functions check

ML_val

\<open>

val true = X.check (X.Dis (X.Uni (X.Con (X.Pre (false,X.Zero_nat,[X.Zero_nat]),
                                         X.Pre (false,X.Suc X.Zero_nat,[X.Zero_nat]))),
                           X.Dis (X.Exi (X.Pre (true,X.Suc X.Zero_nat,[X.Zero_nat])),
                                  X.Exi (X.Pre (true,X.Zero_nat,[X.Zero_nat])))))

\<close>

export_code check test in SML module_name X

section \<open>Acknowledgements\<close>

text \<open>Based on the Archive of Formal Proofs entry Verified_Prover by Tom Ridge (TPHOLs 2005)\<close>

end
