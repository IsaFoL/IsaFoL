theory Hybrid_Logic_STB imports "HOL-Library.Countable" begin

section \<open>Syntax\<close>

datatype ('a, 'b) fm
  = Pro 'a
  | Nom 'b
  | Neg \<open>('a, 'b) fm\<close> (\<open>\<^bold>\<not> _\<close> [40] 40)
  | Dis \<open>('a, 'b) fm\<close> \<open>('a, 'b) fm\<close> (infixr \<open>\<^bold>\<or>\<close> 30)
  | Dia \<open>('a, 'b) fm\<close> (\<open>\<^bold>\<diamond> _\<close> 10)
  | Sat 'b \<open>('a, 'b) fm\<close> (\<open>\<^bold>@ _ _\<close> 10)

abbreviation Top (\<open>\<^bold>\<top>\<close>) where
  \<open>\<^bold>\<top> \<equiv> (undefined \<^bold>\<or> \<^bold>\<not> undefined)\<close>

abbreviation Con (infixr \<open>\<^bold>\<and>\<close> 35) where
  \<open>p \<^bold>\<and> q \<equiv> \<^bold>\<not> (\<^bold>\<not> p \<^bold>\<or> \<^bold>\<not> q)\<close>

abbreviation Imp (infixr \<open>\<^bold>\<longrightarrow>\<close> 25) where
  \<open>p \<^bold>\<longrightarrow> q \<equiv> \<^bold>\<not> (p \<^bold>\<and> \<^bold>\<not> q)\<close>

abbreviation Box (\<open>\<^bold>\<box> _\<close> 10) where
  \<open>\<^bold>\<box> p \<equiv> \<^bold>\<not> (\<^bold>\<diamond> \<^bold>\<not> p)\<close>

primrec nominals :: \<open>('a, 'b) fm \<Rightarrow> 'b set\<close> where
  \<open>nominals (Pro x) = {}\<close>
| \<open>nominals (Nom i) = {i}\<close>
| \<open>nominals (\<^bold>\<not> p) = nominals p\<close>
| \<open>nominals (p \<^bold>\<or> q) = nominals p \<union> nominals q\<close>
| \<open>nominals (\<^bold>\<diamond> p) = nominals p\<close>
| \<open>nominals (\<^bold>@ i p) = {i} \<union> nominals p\<close>

primrec sub :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'c) fm\<close> where
  \<open>sub _ (Pro x) = Pro x\<close>
| \<open>sub f (Nom i) = Nom (f i)\<close>
| \<open>sub f (\<^bold>\<not> p) = (\<^bold>\<not> sub f p)\<close>
| \<open>sub f (p \<^bold>\<or> q) = (sub f p \<^bold>\<or> sub f q)\<close>
| \<open>sub f (\<^bold>\<diamond> p) = (\<^bold>\<diamond> sub f p)\<close>
| \<open>sub f (\<^bold>@ i p) = (\<^bold>@ (f i) (sub f p))\<close>

lemma sub_nominals: \<open>nominals (sub f p) = f ` nominals p\<close>
  by (induct p) auto

lemma sub_id: \<open>sub id p = p\<close>
  by (induct p) simp_all

lemma sub_upd_fresh: \<open>i \<notin> nominals p \<Longrightarrow> sub (f(i := j)) p = sub f p\<close>
  by (induct p) auto

section \<open>Semantics\<close>

datatype ('w, 'a) model =
  Model (R: \<open>'w \<Rightarrow> 'w set\<close>) (V: \<open>'w \<Rightarrow> 'a \<Rightarrow> bool\<close>)

primrec semantics
  :: \<open>('w, 'a) model \<Rightarrow> ('b \<Rightarrow> 'w) \<Rightarrow> 'w \<Rightarrow> ('a, 'b) fm \<Rightarrow> bool\<close>
  (\<open>_, _, _ \<Turnstile> _\<close> [50, 50, 50] 50) where
  \<open>(M, _, w \<Turnstile> Pro x) = V M w x\<close>
| \<open>(_, g, w \<Turnstile> Nom i) = (w = g i)\<close>
| \<open>(M, g, w \<Turnstile> \<^bold>\<not> p) = (\<not> M, g, w \<Turnstile> p)\<close>
| \<open>(M, g, w \<Turnstile> (p \<^bold>\<or> q)) = ((M, g, w \<Turnstile> p) \<or> (M, g, w \<Turnstile> q))\<close>
| \<open>(M, g, w \<Turnstile> \<^bold>\<diamond> p) = (\<exists>v \<in> R M w. M, g, v \<Turnstile> p)\<close>
| \<open>(M, g, _ \<Turnstile> \<^bold>@ i p) = (M, g, g i \<Turnstile> p)\<close>

lemma \<open>M, g, w \<Turnstile> \<^bold>\<top>\<close>
  by simp

lemma semantics_fresh: \<open>i \<notin> nominals p \<Longrightarrow> (M, g, w \<Turnstile> p) = (M, g(i := v), w \<Turnstile> p)\<close>
  by (induct p arbitrary: w) auto

abbreviation is_named :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>is_named M \<equiv> \<forall>w. \<exists>a. V M a = w\<close>

abbreviation reflexive :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>reflexive M \<equiv> \<forall>w. w \<in> R M w\<close>

abbreviation irreflexive :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>irreflexive M \<equiv> \<forall>w. w \<notin> R M w\<close>

abbreviation symmetric :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>symmetric M \<equiv> \<forall>v w. w \<in> R M v \<longleftrightarrow> v \<in> R M w\<close>

abbreviation asymmetric :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>asymmetric M \<equiv> \<forall>v w. \<not> (w \<in> R M v \<and> v \<in> R M w)\<close>

abbreviation transitive :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>transitive M \<equiv> \<forall>v w x. w \<in> R M v \<and> x \<in> R M w \<longrightarrow> x \<in> R M v\<close>

abbreviation universal :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>universal M \<equiv> \<forall>v w. v \<in> R M w\<close>

lemma \<open>irreflexive M \<Longrightarrow> M, g, w \<Turnstile> \<^bold>@ i \<^bold>\<not> (\<^bold>\<diamond> Nom i)\<close>
proof -
  assume \<open>irreflexive M\<close>
  then have \<open>g i \<notin> R M (g i)\<close>
    by simp
  then have \<open>\<not> (\<exists>v \<in> R M (g i). g i = v)\<close>
    by simp
  then have \<open>\<not> M, g, g i \<Turnstile> \<^bold>\<diamond> Nom i\<close>
    by simp
  then have \<open>M, g, g i \<Turnstile> \<^bold>\<not> (\<^bold>\<diamond> Nom i)\<close>
    by simp
  then show \<open>M, g, w \<Turnstile> \<^bold>@ i \<^bold>\<not> (\<^bold>\<diamond> Nom i)\<close>
    by simp
qed

lemma \<open>irreflexive M = (\<forall>g w. M, g, w \<Turnstile> \<^bold>@ i \<^bold>\<not> (\<^bold>\<diamond> Nom i))\<close>
  by auto

lemma \<open>asymmetric M = (\<forall>g w. M, g, w \<Turnstile> \<^bold>@ i (\<^bold>\<box> \<^bold>\<not> (\<^bold>\<diamond> Nom i)))\<close>
  by auto

lemma \<open>universal M = (\<forall>g w. M, g, w \<Turnstile> \<^bold>\<diamond> Nom i)\<close>
  by auto

section \<open>Tableau\<close>

subsection \<open>Definition\<close>

type_synonym ('a, 'b) block = \<open>('a, 'b) fm list \<times> 'b\<close>
type_synonym ('a, 'b) branch = \<open>('a, 'b) block list\<close>

primrec on :: \<open>('a, 'b) fm \<Rightarrow> ('a, 'b) block \<Rightarrow> bool\<close> (\<open>_ on _\<close> [51, 51] 50) where
  \<open>p on (ps, i) = (p \<in> set ps \<or> p = Nom i)\<close>

syntax
  "_Ballon" :: \<open>pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close> (\<open>(3\<forall>(_/on_)./ _)\<close> [0, 0, 10] 10)
  "_Bexon" :: \<open>pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close> (\<open>(3\<exists>(_/on_)./ _)\<close> [0, 0, 10] 10)

translations
  "\<forall>p on A. P" \<rightharpoonup> "\<forall>p. p on A \<longrightarrow> P"
  "\<exists>p on A. P" \<rightharpoonup> "\<exists>p. p on A \<and> P"

abbreviation list_nominals :: \<open>('a, 'b) fm list \<Rightarrow> 'b set\<close> where
  \<open>list_nominals ps \<equiv> (\<Union>p \<in> set ps. nominals p)\<close>

primrec block_nominals :: \<open>('a, 'b) block \<Rightarrow> 'b set\<close> where
  \<open>block_nominals (ps, i) = {i} \<union> list_nominals ps\<close>

definition branch_nominals :: \<open>('a, 'b) branch \<Rightarrow> 'b set\<close> where
  \<open>branch_nominals branch \<equiv> (\<Union>block \<in> set branch. block_nominals block)\<close>

inductive STB :: \<open>('a, 'b) branch \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [50] 50) where
  Close:
  \<open>(ps, i) \<in> set branch \<Longrightarrow> (qs, i) \<in> set branch \<Longrightarrow>
    p on (ps, i) \<Longrightarrow> (\<^bold>\<not> p) on (qs, i) \<Longrightarrow>
    \<turnstile> branch\<close>
| Neg:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>\<not> \<^bold>\<not> p) on (qs, a) \<Longrightarrow>
    \<turnstile> (p # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| DisP:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> (p \<^bold>\<or> q) on (qs, a) \<Longrightarrow>
    \<turnstile> (p # ps, a) # branch \<Longrightarrow> \<turnstile> (q # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| DisN:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>\<not> (p \<^bold>\<or> q)) on (qs, a) \<Longrightarrow>
    \<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| DiaP:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>\<diamond> p) on (qs, a) \<Longrightarrow>
    \<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch \<Longrightarrow>
    \<nexists>a. p = Nom a \<Longrightarrow> i \<notin> branch_nominals ((ps, a) # branch) \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| DiaN:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>\<not> (\<^bold>\<diamond> p)) on (qs, a) \<Longrightarrow>
   (rs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>\<diamond> Nom i) on (rs, a) \<Longrightarrow>
    \<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| SatP:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> Nom i on (qs, a) \<Longrightarrow>
   (rs, b) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>@ i p) on (rs, b) \<Longrightarrow>
    \<turnstile> (p # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| SatN:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> Nom i on (qs, a) \<Longrightarrow>
   (rs, b) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>\<not> (\<^bold>@ i p)) on (rs, b) \<Longrightarrow>
    \<turnstile> ((\<^bold>\<not> p) # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| GoTo:
  \<open>i \<in> branch_nominals branch \<Longrightarrow> \<turnstile> ([], i) # branch \<Longrightarrow> \<turnstile> branch\<close>
| Nom:
  \<open>(qs, b) \<in> set ((ps, a) # branch) \<Longrightarrow>
    p on (qs, b) \<Longrightarrow> Nom i on (qs, b) \<Longrightarrow>
    Nom i on (ps, a) \<Longrightarrow>
    \<turnstile> (p # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>
| Bridge:
  \<open>(qs, a) \<in> set ((ps, a) # branch) \<Longrightarrow> (\<^bold>\<diamond> Nom j) on (qs, a) \<Longrightarrow>
    (rs, j) \<in> set ((ps, a) # branch) \<Longrightarrow> Nom k on (rs, j) \<Longrightarrow>
    \<turnstile> ((\<^bold>\<diamond> Nom k) # ps, a) # branch \<Longrightarrow>
    \<turnstile> (ps, a) # branch\<close>

lemma \<open>\<turnstile> [([\<^bold>\<not> (\<^bold>@ i (Nom i))], a)]\<close>
proof -
  let ?init = \<open>[\<^bold>\<not> (\<^bold>@ i (Nom i))]\<close>
  have \<open>\<turnstile> [([\<^bold>\<not> Nom i], i), (?init, a)]\<close>
    using STB.Close[where i=i and p=\<open>Nom i\<close> and ps=\<open>[\<^bold>\<not> Nom i]\<close> and qs=\<open>[\<^bold>\<not> Nom i]\<close>] by force
  then have \<open>\<turnstile> [([], i), (?init, a)]\<close>
    using STB.SatN[where i=i and a=i and b=a and p=\<open>Nom i\<close> and ps=\<open>[]\<close> and qs=\<open>[]\<close> and rs=\<open>?init\<close>]
    by force
  then show \<open>\<turnstile> [(?init, a)]\<close>
    using STB.GoTo[where i=i and branch=\<open>[(?init, a)]\<close>] unfolding branch_nominals_def by force
qed

section \<open>Soundness\<close>

abbreviation block_sat :: \<open>('w, 'a) model \<Rightarrow> ('b \<Rightarrow> 'w) \<Rightarrow> ('a, 'b) block \<Rightarrow> bool\<close> where
  \<open>block_sat M g block \<equiv> \<exists>w. \<forall>p on block. M, g, w \<Turnstile> p\<close>

abbreviation branch_sat :: \<open>('w, 'a) model \<Rightarrow> ('b \<Rightarrow> 'w) \<Rightarrow> ('a, 'b) branch \<Rightarrow> bool\<close> where
  \<open>branch_sat M g branch \<equiv> \<forall>block \<in> set branch. block_sat M g block\<close>

lemma add_prop_sat:
  assumes \<open>branch_sat M g ((ps, i) # branch)\<close> \<open>block_sat M g ((p # ps, i))\<close>
  shows \<open>branch_sat M g ((p # ps, i) # branch)\<close>
  using assms by simp

lemma block_nominals: \<open>i \<notin> block_nominals block \<Longrightarrow> p on block \<Longrightarrow> i \<notin> nominals p\<close>
  by (induct block) auto

lemma block_sat_fresh:
  assumes \<open>block_sat M g block\<close> \<open>i \<notin> block_nominals block\<close>
  shows \<open>block_sat M (g(i := v)) block\<close>
  using assms block_nominals semantics_fresh by metis

lemma branch_sat_fresh:
  assumes \<open>branch_sat M g branch\<close> \<open>i \<notin> branch_nominals branch\<close>
  shows \<open>branch_sat M (g(i := v)) branch\<close>
proof
  fix block
  assume \<open>block \<in> set branch\<close>
  then have \<open>block_sat M g block\<close>
    using \<open>branch_sat M g branch\<close> by blast
  moreover have \<open>i \<notin> block_nominals block\<close>
    using \<open>block \<in> set branch\<close> \<open>i \<notin> branch_nominals branch\<close>
    unfolding branch_nominals_def by blast
  ultimately show \<open>block_sat M (g(i := v)) block\<close>
    using block_sat_fresh by metis
qed

lemma named_block_sat:
  \<open>block_sat M g block \<Longrightarrow> Nom i on block \<Longrightarrow> p on block \<Longrightarrow> M, g, g i \<Turnstile> p\<close>
  by (metis semantics.simps(2))

lemma branch_sat_opening:
  assumes \<open>branch_sat M g branch\<close> \<open>(ps, i) \<in> set branch\<close> \<open>p on (ps, i)\<close>
  shows \<open>M, g, g i \<Turnstile> p\<close>
  using assms named_block_sat[where block=\<open>(ps, i)\<close> and M=M and g=g and i=i] by fastforce

lemma branch_sat_current:
  assumes \<open>branch_sat M g ((ps, i) # branch)\<close> \<open>p on (ps, i)\<close>
  shows \<open>M, g, g i \<Turnstile> p\<close>
  using assms named_block_sat[where block=\<open>(ps, i)\<close> and M=M and g=g and i=i] by simp

lemma branch_sat_add_fm:
  assumes \<open>branch_sat M g ((ps, i) # branch)\<close> \<open>M, g, g i \<Turnstile> p\<close>
  shows \<open>branch_sat M g ((p # ps, i) # branch)\<close>
  using assms by simp metis

lemma soundness': \<open>\<turnstile> branch \<Longrightarrow> branch_sat M g branch \<Longrightarrow> False\<close>
proof (induct branch arbitrary: g rule: STB.induct)
  case (Close ps i branch qs p)
  have \<open>M, g, g i \<Turnstile> p\<close>
    using Close(1, 3, 5) branch_sat_opening by metis
  moreover have \<open>M, g, g i \<Turnstile> \<^bold>\<not> p\<close>
    using Close(2, 4, 5) branch_sat_opening by metis
  ultimately show ?case
    by simp
next
  case (Neg qs a ps branch p)
  then have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using branch_sat_opening by metis
  then have \<open>M, g, g a \<Turnstile> p\<close>
    using \<open>(\<^bold>\<not> \<^bold>\<not> p) on (qs, a)\<close> by auto
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using Neg branch_sat_current by metis
  ultimately have \<open>branch_sat M g ((p # ps, a) # branch)\<close>
    using Neg branch_sat_add_fm by auto
  then show ?case
    using Neg by blast
next
  case (DisP qs a ps branch p q)
  have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using DisP(1, 7) branch_sat_opening by metis
  then have \<open>(M, g, g a \<Turnstile> p) \<or> (M, g, g a \<Turnstile> q)\<close>
    using \<open>(p \<^bold>\<or> q) on (qs, a)\<close> by auto
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using DisP(7) branch_sat_current by metis
  ultimately have
    \<open>branch_sat M g ((p # ps, a) # branch) \<or>
     branch_sat M g ((q # ps, a) # branch)\<close>
    using DisP(7) by (metis list.set_intros(2) on.simps semantics.simps(2) set_ConsD)
  then show ?case
    using DisP by blast
next
  case (DisN qs a ps branch p q)
  then have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using branch_sat_opening by metis
  then have \<open>M, g, g a \<Turnstile> \<^bold>\<not> p\<close> \<open>M, g, g a \<Turnstile> \<^bold>\<not> q\<close>
    using \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) on (qs, a)\<close> by auto
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using DisN branch_sat_current by metis
  ultimately have \<open>branch_sat M g (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch)\<close>
    using DisN branch_sat_add_fm by auto
  then show ?case
    using DisN by blast
next
  case (DiaP qs a ps branch p i)
  then have \<open>i \<notin> nominals p\<close>
    unfolding branch_nominals_def by fastforce

  have *: \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using DiaP branch_sat_current by metis

  have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using DiaP branch_sat_opening by metis
  then obtain v where \<open>v \<in> R M (g a)\<close> \<open>M, g, v \<Turnstile> p\<close>
    using \<open>(\<^bold>\<diamond> p) on (qs, a)\<close> by fastforce
  then have \<open>M, g(i := v), v \<Turnstile> p\<close>
    using \<open>i \<notin> nominals p\<close> semantics_fresh by metis
  then have \<open>M, g(i := v), g a \<Turnstile> \<^bold>@ i p\<close>
    by simp
  moreover have \<open>M, g(i := v), g a \<Turnstile> \<^bold>\<diamond> Nom i\<close>
    using \<open>v \<in> R M (g a)\<close> by simp

  moreover have \<open>branch_sat M (g(i := v)) ((ps, a) # branch)\<close>
    using DiaP(6, 7) branch_sat_fresh[where g=g] by blast
  moreover have \<open>i \<notin> block_nominals (ps, a)\<close>
    using \<open>i \<notin> branch_nominals ((ps, a) # branch)\<close> unfolding branch_nominals_def by simp
  then have \<open>\<forall>p on (ps, a). M, g(i := v), g a \<Turnstile> p\<close>
    using * semantics_fresh by fastforce
  ultimately have \<open>branch_sat M (g(i := v)) (((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch)\<close>
    by auto
  then show ?case
    using DiaP by blast
next
  case (DiaN qs a ps branch p rs i)
  have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using DiaN(1, 7) branch_sat_opening by meson
  moreover have \<open>\<forall>p on (rs, a). M, g, g a \<Turnstile> p\<close>
    using DiaN(3, 7) branch_sat_opening by meson
  ultimately obtain v where \<open>v \<in> R M (g a)\<close> \<open>g i = v\<close> \<open>\<not> M, g, g i \<Turnstile> p\<close>
    using \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) on (qs, a)\<close> \<open>(\<^bold>\<diamond> Nom i) on (rs, a)\<close> by fastforce
  then have \<open>M, g, g a \<Turnstile> \<^bold>\<not> (\<^bold>@ i p)\<close>
    by simp
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using DiaN branch_sat_current by metis
  ultimately have \<open>branch_sat M g (((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch)\<close>
    using DiaN by simp
  then show ?thesis
    using DiaN by blast
next
  case (SatP qs a ps branch i rs b p)
  then have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using branch_sat_opening by metis
  then have \<open>g i = g a\<close>
    using \<open>Nom i on (qs, a)\<close> by auto
  moreover have \<open>\<forall>p on (rs, b). M, g, g b \<Turnstile> p\<close>
    using SatP branch_sat_opening by metis
  then have \<open>M, g, g i \<Turnstile> p\<close>
    using \<open>(\<^bold>@ i p) on (rs, b)\<close> by auto
  ultimately have \<open>M, g, g a \<Turnstile> p\<close>
    using SatP by simp
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using SatP branch_sat_current by metis
  ultimately have \<open>branch_sat M g ((p # ps, a) # branch)\<close>
    using SatP branch_sat_add_fm by auto
  then show ?case
    using SatP by blast
next
  case (SatN qs a ps branch i rs b p)
  then have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using branch_sat_opening by metis
  then have \<open>g i = g a\<close>
    using \<open>Nom i on (qs, a)\<close> by auto
  moreover have \<open>\<forall>p on (rs, b). M, g, g b \<Turnstile> p\<close>
    using SatN branch_sat_opening by metis
  then have \<open>M, g, g i \<Turnstile> \<^bold>\<not> p\<close>
    using \<open>(\<^bold>\<not> (\<^bold>@ i p)) on (rs, b)\<close> by auto
  ultimately have \<open>M, g, g a \<Turnstile> \<^bold>\<not> p\<close>
    using SatN by simp
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using SatN branch_sat_current by metis
  ultimately have \<open>branch_sat M g (((\<^bold>\<not> p) # ps, a) # branch)\<close>
    using SatN branch_sat_add_fm by auto
  then show ?case
    using SatN by blast
next
  case (GoTo i branch)
  then show ?case
    by auto
next
  case (Nom qs b ps a branch p i)
  then have \<open>\<forall>p on (qs, b). M, g, g b \<Turnstile> p\<close>
    using branch_sat_opening by metis
  then have \<open>M, g, g b \<Turnstile> p\<close> \<open>M, g, g b \<Turnstile> Nom i\<close>
    using \<open>p on (qs, b)\<close> \<open>Nom i on (qs, b)\<close> by blast+
  then have \<open>M, g, g i \<Turnstile> p\<close>
    by simp
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using Nom branch_sat_current by metis
  moreover have \<open>\<forall>p on (ps, a). M, g, g i \<Turnstile> p\<close>
    using calculation \<open>Nom i on (ps, a)\<close> by (metis semantics.simps(2))
  ultimately have \<open>block_sat M g (p # ps, a)\<close>
    by auto
  then have \<open>branch_sat M g ((p # ps, a) # branch)\<close>
    using Nom by auto
  then show ?case
    using Nom by blast
next
  case (Bridge qs a ps branch j rs k)
  have \<open>\<forall>p on (rs, j). M, g, g j \<Turnstile> p\<close>
    using Bridge branch_sat_opening by metis
  then have \<open>M, g, g j \<Turnstile> Nom k\<close>
    using \<open>Nom k on (rs, j)\<close> by blast
  then have \<open>g j = g k\<close>
    by simp

  have \<open>\<forall>p on (qs, a). M, g, g a \<Turnstile> p\<close>
    using Bridge branch_sat_opening by metis
  then have \<open>M, g, g a \<Turnstile> \<^bold>\<diamond> Nom j\<close>
    using \<open>(\<^bold>\<diamond> Nom j) on (qs, a)\<close> by auto
  then have \<open>M, g, g a \<Turnstile> \<^bold>\<diamond> Nom k\<close>
    using \<open>g j = g k\<close> by simp
  moreover have \<open>\<forall>p on (ps, a). M, g, g a \<Turnstile> p\<close>
    using Bridge branch_sat_current by metis
  ultimately have \<open>branch_sat M g (((\<^bold>\<diamond> Nom k) # ps, a) # branch)\<close>
    using Bridge branch_sat_add_fm by auto
  then show ?case
    using Bridge by blast
qed

lemma soundness: \<open>\<turnstile> branch \<Longrightarrow> \<exists>block \<in> set branch. \<exists>p on block. \<not> M, g, w \<Turnstile> p\<close>
  using soundness' by fast

corollary \<open>\<not> \<turnstile> []\<close>
  using soundness by fastforce

proposition \<open>\<not> \<turnstile> []\<close>
proof -
  have \<open>\<turnstile> branch \<Longrightarrow> branch = [] \<Longrightarrow> False\<close> for branch :: \<open>('a, 'b) branch\<close>
    by (induct branch rule: STB.induct) (auto simp: branch_nominals_def)
  then show ?thesis
    by blast
qed

theorem soundness_fresh:
  assumes \<open>\<turnstile> [([\<^bold>\<not> p], i)]\<close> \<open>i \<notin> nominals p\<close>
  shows \<open>M, g, w \<Turnstile> p\<close>
proof -
  from assms(1) have \<open>M, g, g i \<Turnstile> p\<close> for g
    using soundness by fastforce
  then have \<open>M, g(i := w), (g(i := w)) i \<Turnstile> p\<close>
    by blast
  then have \<open>M, g(i := w), w \<Turnstile> p\<close>
    by simp
  then have \<open>M, g(i := g i), w \<Turnstile> p\<close>
    using assms(2) semantics_fresh by metis
  then show ?thesis
    by simp
qed

section \<open>Substitution\<close>

lemma finite_nominals: \<open>finite (nominals p)\<close>
  by (induct p) simp_all

lemma finite_block_nominals: \<open>finite (block_nominals block)\<close>
  using finite_nominals by (induct block) auto

lemma finite_branch_nominals: \<open>finite (branch_nominals branch)\<close>
  unfolding branch_nominals_def by (induct branch) (auto simp: finite_block_nominals)

lemma ex_fresh_nom:
  fixes branch :: \<open>('a, 'b) branch\<close>
  assumes \<open>infinite (UNIV :: 'b set)\<close>
  shows \<open>\<exists>i. i \<notin> branch_nominals branch\<close>
  using assms ex_new_if_finite finite_branch_nominals by blast

abbreviation sub_list :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) fm list \<Rightarrow> ('a, 'c) fm list\<close> where
  \<open>sub_list f ps \<equiv> map (sub f) ps\<close>

primrec sub_block :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) block \<Rightarrow> ('a, 'c) block\<close> where
  \<open>sub_block f (ps, i) = (sub_list f ps, f i)\<close>

definition sub_branch :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) branch \<Rightarrow> ('a, 'c) branch\<close> where
  \<open>sub_branch f blocks \<equiv> map (sub_block f) blocks\<close>

lemma sub_block_mem: \<open>p on block \<Longrightarrow> sub f p on sub_block f block\<close>
  by (induct block) auto

lemma sub_block_mem': \<open>p on (ps, i) \<Longrightarrow> sub f p on (sub_list f ps, f i)\<close>
  using sub_block_mem by auto

lemma sub_branch_mem:
  assumes \<open>(ps, i) \<in> set branch\<close>
  shows \<open>(sub_list f ps, f i) \<in> set (sub_branch f branch)\<close>
  unfolding sub_branch_def using assms image_iff by fastforce

lemma sub_branch_mem':
  assumes \<open>(qs, i) \<in> set ((ps, a) # branch)\<close>
  shows \<open>(sub_list f qs, f i) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
  using assms sub_branch_mem[where branch=\<open>(ps, a) # branch\<close>]
  unfolding sub_branch_def by auto

lemma sub_block_nominals:
  \<open>block_nominals (sub_block f block) = f ` block_nominals block\<close>
  by (induct block) (auto simp: sub_nominals)

lemma sub_branch_nominals:
  \<open>branch_nominals (sub_branch f branch) = f ` branch_nominals branch\<close>
  unfolding branch_nominals_def sub_branch_def
proof (induct branch)
  case (Cons block branch)
  then show ?case
    using sub_block_nominals[where f=f and block=block]
    by auto
qed simp

lemma sub_list_id: \<open>sub_list id ps = ps\<close>
  using sub_id by (induct ps) auto

lemma sub_block_id: \<open>sub_block id block = block\<close>
  using sub_list_id by (induct block) auto

lemma sub_branch_id: \<open>sub_branch id branch = branch\<close>
  unfolding sub_branch_def using sub_block_id by (induct branch) auto

lemma sub_block_upd_fresh:
  assumes \<open>i \<notin> block_nominals block\<close>
  shows \<open>sub_block (f(i := j)) block = sub_block f block\<close>
  using assms by (induct block) (auto simp add: sub_upd_fresh)

lemma sub_branch_upd_fresh:
  assumes \<open>i \<notin> branch_nominals branch\<close>
  shows \<open>sub_branch (f(i := j)) branch = sub_branch f branch\<close>
  using assms unfolding branch_nominals_def sub_branch_def
  by (induct branch) (auto simp: sub_block_upd_fresh)

lemma sub_add_fm:
  \<open>sub_branch f ((p # ps, a) # branch) = (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
  unfolding sub_branch_def by simp

lemma STB_sub:
  fixes f :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>infinite (UNIV :: 'c set)\<close>
  shows \<open>\<turnstile> branch \<Longrightarrow> \<turnstile> sub_branch f branch\<close>
proof (induct branch arbitrary: f rule: STB.induct)
  case (Close ps i branch qs p)
  then have
    \<open>(sub_list f ps, f i) \<in> set (sub_branch f branch)\<close>
    \<open>(sub_list f qs, f i) \<in> set (sub_branch f branch)\<close>
    using sub_branch_mem by fast+
  moreover have
    \<open>sub f p on (sub_list f ps, f i)\<close>
    \<open>(\<^bold>\<not> sub f p) on (sub_list f qs, f i)\<close>
    using Close sub_block_mem' by fastforce+
  ultimately show ?case
    using STB.Close by fast
next
  case (Neg qs a ps branch p)
  then have \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(sub_list f qs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using Neg sub_branch_mem' by fast
  moreover have \<open>(\<^bold>\<not> \<^bold>\<not> sub f p) on (sub_list f qs, f a)\<close>
    using Neg sub_block_mem' by fastforce
  ultimately show ?case
    unfolding sub_branch_def by (simp add: STB.Neg)
next
  case (DisP qs a ps branch p q)
  then have
    \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    \<open>\<turnstile> (sub f q # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp_all
  moreover have \<open>(sub_list f qs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using DisP sub_branch_mem' by fast
  moreover have \<open>(sub f p \<^bold>\<or> sub f q) on (sub_list f qs, f a)\<close>
    using DisP(2) sub_block_mem' by fastforce
  ultimately show ?case
    unfolding sub_branch_def by (simp add: STB.DisP)
next
  case (DisN qs a ps branch p q)
  then have \<open>\<turnstile> ((\<^bold>\<not> sub f q) # (\<^bold>\<not> sub f p) # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(sub_list f qs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using DisN sub_branch_mem' by fast
  moreover have \<open>(\<^bold>\<not> (sub f p \<^bold>\<or> sub f q)) on (sub_list f qs, f a)\<close>
    using DisN(2) sub_block_mem' by fastforce
  ultimately show ?case
    unfolding sub_branch_def by (simp add: STB.DisN)
next
  case (DiaP qs a ps branch p i)
  have \<open>finite (f ` branch_nominals ((ps, a) # branch))\<close>
    by (simp add: finite_branch_nominals)
  then obtain j where *: \<open>j \<notin> f ` branch_nominals ((ps, a) # branch)\<close>
    using assms ex_new_if_finite by blast

  let ?f = \<open>f(i := j)\<close>
  have \<open>sub_branch ?f ((ps, a) # branch) = sub_branch f ((ps, a) # branch)\<close>
    using DiaP sub_branch_upd_fresh by fast
  then have **: \<open>(sub_list ?f ps, ?f a) # sub_branch ?f branch = sub_branch f ((ps, a) # branch)\<close>
    unfolding sub_branch_def by simp

  have \<open>\<turnstile> ((sub ?f (\<^bold>@ i p)) # (sub ?f (\<^bold>\<diamond> Nom i)) # sub_list ?f ps, ?f a) # sub_branch ?f branch\<close>
    using DiaP(4) sub_add_fm by (metis map_eq_Cons_conv)
  then have \<open>\<turnstile> ((\<^bold>@ (?f i) (sub ?f p)) # (\<^bold>\<diamond> Nom (?f i)) # sub_list ?f ps, ?f a) # sub_branch ?f branch\<close>
    by simp
  moreover have \<open>(sub_list ?f qs, ?f a) \<in> set ((sub_list ?f ps, ?f a) # sub_branch ?f branch)\<close>
    using DiaP sub_branch_mem' by fast
  moreover have \<open>(\<^bold>\<diamond> sub ?f p) on (sub_list ?f qs, ?f a)\<close>
    using DiaP(2) sub_block_mem by fastforce
  moreover have \<open>\<nexists>a. sub ?f p = Nom a\<close>
    using DiaP by (induct p) simp_all
  moreover have \<open>?f i \<notin> branch_nominals ((sub_list ?f ps, ?f a) # sub_branch ?f branch)\<close>
    using * ** sub_branch_nominals by (metis fun_upd_same)
  ultimately have \<open>\<turnstile> (sub_list ?f ps, ?f a) # sub_branch ?f branch\<close>
    using STB.DiaP by fast
  then show ?case
    using ** by metis
next
  case (DiaN qs a ps branch p rs i)
  then have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ (f i) (sub f p))) # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have
    \<open>(sub_list f qs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    \<open>(sub_list f rs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using DiaN sub_branch_mem' by fast+
  moreover have
    \<open>(\<^bold>\<not> (\<^bold>\<diamond> sub f p)) on (sub_list f qs, f a)\<close>
    \<open>(\<^bold>\<diamond> Nom (f i)) on (sub_list f rs, f a)\<close>
    using DiaN(2, 4) sub_block_mem by fastforce+
  ultimately show ?case
    unfolding sub_branch_def by (simp add: STB.DiaN)
next
  case (SatP qs a ps branch i rs b p)
  then have \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(sub_list f qs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using SatP sub_branch_mem' by fast
  moreover have \<open>Nom (f i) on (sub_list f qs, f a)\<close>
    using SatP sub_block_mem' by (metis sub.simps(2))
  moreover have \<open>(sub_list f rs, f b) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using SatP sub_branch_mem' by fast
  moreover have \<open>(\<^bold>@ (f i) (sub f p)) on (sub_list f rs, f b)\<close>
    using SatP(4) sub_block_mem' by fastforce
  ultimately show ?case
    unfolding sub_branch_def by (simp add: STB.SatP)
next
  case (SatN qs a ps branch i rs b p)
  then have \<open>\<turnstile> ((\<^bold>\<not> sub f p) # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have
    \<open>(sub_list f qs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using SatN sub_branch_mem' by fast
  moreover have \<open>Nom (f i) on (sub_list f qs, f a)\<close>
    using SatN sub_block_mem' by (metis sub.simps(2))
  moreover have \<open>(sub_list f rs, f b) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using SatN sub_branch_mem' by fast
  moreover have \<open>(\<^bold>\<not> (\<^bold>@ (f i) (sub f p))) on (sub_list f rs, f b)\<close>
    using SatN(4) sub_block_mem' by fastforce
  ultimately show ?case
    unfolding sub_branch_def by (simp add: STB.SatN)
next
  case (GoTo i branch)
  then have \<open>\<turnstile> ([], f i) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>f i \<in> branch_nominals (sub_branch f branch)\<close>
    using GoTo sub_branch_nominals by fast
  ultimately show ?case
    by (simp add: STB.GoTo)
next
  case (Nom qs b ps a branch p i)
  then have \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(sub_list f qs, f b) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using Nom sub_branch_mem' by fast
  moreover have
    \<open>Nom (f i) on (sub_list f qs, f b)\<close>
    \<open>Nom (f i) on (sub_list f ps, f a)\<close>
    using Nom sub_block_mem' by (metis sub.simps(2))+
  moreover have \<open>sub f p on (sub_list f qs, f b)\<close>
    using Nom(2) sub_block_mem' by fastforce
  ultimately show ?case
    using STB.Nom
    unfolding sub_branch_def by (simp add: STB.Nom)
next
  case (Bridge qs a ps branch j rs k)
  then have \<open>\<turnstile> ((\<^bold>\<diamond> Nom (f k)) # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(sub_list f qs, f a) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using Bridge sub_branch_mem' by fast
  moreover have \<open>(\<^bold>\<diamond> Nom (f j)) on (sub_list f qs, f a)\<close>
    using Bridge(2) by (induct qs) auto
  moreover have \<open>(sub_list f rs, f j) \<in> set ((sub_list f ps, f a) # sub_branch f branch)\<close>
    using Bridge sub_branch_mem' by fast
  moreover have \<open>(Nom (f k)) on (sub_list f rs, f j)\<close>
    using Bridge(4) by (induct rs) auto
  ultimately show ?case
    unfolding sub_branch_def by (simp add: STB.Bridge)
qed

lemma sub_swap: \<open>sub (id(i := j, j := i)) (sub (id(i := j, j := i)) p) = p\<close>
  by (induct p) simp_all

lemma sub_block_swap:
  \<open>sub_block (id(i := j, j := i)) (sub_block (id(i := j, j := i)) block) = block\<close>
proof (induct block)
  case (Pair ps i)
  then show ?case
    using sub_swap by (induct ps) fastforce+
qed

lemma sub_range: \<open>i \<notin> range f \<Longrightarrow> i \<notin> nominals (sub f p)\<close>
  by (induct p) auto

lemma sub_block_range: \<open>i \<notin> range f \<Longrightarrow> i \<notin> block_nominals (sub_block f block)\<close>
  using sub_range by (induct block) fastforce+

lemma sub_branch_range: \<open>i \<notin> range f \<Longrightarrow> i \<notin> branch_nominals (sub_branch f branch)\<close>
  unfolding branch_nominals_def sub_branch_def using sub_block_range by fastforce

section \<open>Completeness\<close>

subsection \<open>Hintikka\<close>

definition hintikka :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>hintikka H \<equiv>
   ((\<forall>x i j. (\<exists>ps. (ps, i) \<in> H \<and> Nom j on (ps, i)) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H \<and> Pro x on (qs, j)) \<longrightarrow>
      (\<nexists>rs. (rs, i) \<in> H \<and> (\<^bold>\<not> Pro x) on (rs, i))) \<and>
    (\<forall>a i. (\<exists>ps. (ps, i) \<in> H \<and> Nom a on (ps, i)) \<longrightarrow> (\<nexists>qs. (qs, i) \<in> H \<and> (\<^bold>\<not> Nom a) on (qs, i))) \<and>
    (\<forall>i j. (\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (ps, i)) \<longrightarrow>
      (\<nexists>qs. (qs, i) \<in> H \<and> (\<^bold>\<not> (\<^bold>\<diamond> Nom j)) on (qs, i))) \<and>
    (\<forall>p i. i \<in> nominals p \<and> (\<exists>block \<in> H. p on block) \<longrightarrow> (\<exists>qs. (qs, i) \<in> H)) \<and>
    (\<forall>i j. (\<exists>ps. (ps, i) \<in> H \<and> Nom j on (ps, i)) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H \<and> Nom i on (qs, j))) \<and>
    (\<forall>i j k. (\<exists>ps. (ps, i) \<in> H \<and> Nom j on (ps, i)) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H \<and> Nom k on (qs, j)) \<longrightarrow>
      (\<exists>rs. (rs, i) \<in> H \<and> Nom k on (rs, i))) \<and>
    (\<forall>i j k. (\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (ps, i)) \<longrightarrow>
      (\<exists>qs. (qs, j) \<in> H \<and> Nom k on (qs, j)) \<longrightarrow> (\<exists>rs. (rs, i) \<in> H \<and> (\<^bold>\<diamond> Nom k) on (rs, i))) \<and>
    (\<forall>i j k. (\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (ps, i)) \<longrightarrow>
      (\<exists>qs. (qs, i) \<in> H \<and> Nom k on (qs, i)) \<longrightarrow> (\<exists>rs. (rs, k) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (rs, k))) \<and>
    (\<forall>p q i. (\<exists>ps. (ps, i) \<in> H \<and> (p \<^bold>\<or> q) on (ps, i)) \<longrightarrow>
      (\<exists>qs. (qs, i) \<in> H \<and> (p on (qs, i) \<or> q on (qs, i)))) \<and>
    (\<forall>p q i. (\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<not> (p \<^bold>\<or> q)) on (ps, i)) \<longrightarrow>
      (\<exists>qs. (qs, i) \<in> H \<and> (\<^bold>\<not> p) on (qs, i) \<and> (\<^bold>\<not> q) on (qs, i))) \<and>
    (\<forall>p i. (\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<not> \<^bold>\<not> p) on (ps, i)) \<longrightarrow> (\<exists>qs. (qs, i) \<in> H \<and> p on (qs, i))) \<and>
    (\<forall>p i. (\<exists>block \<in> H. (\<^bold>@ i p) on block) \<longrightarrow> (\<exists>qs. (qs, i) \<in> H \<and> p on (qs, i))) \<and>
    (\<forall>p i. (\<exists>block \<in> H. (\<^bold>\<not> (\<^bold>@ i p)) on block) \<longrightarrow> (\<exists>qs. (qs, i) \<in> H \<and> (\<^bold>\<not> p) on (qs, i))) \<and>
    (\<forall>p i. (\<nexists>a. p = Nom a) \<longrightarrow> (\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<diamond> p) on (ps, i)) \<longrightarrow>
      (\<exists>j. (\<exists>qs. (qs, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (qs, i)) \<and> (\<exists>rs. (rs, i) \<in> H \<and> (\<^bold>@ j p) on (rs, i)))) \<and>
    (\<forall>p i j. (\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<not> (\<^bold>\<diamond> p)) on (ps, i)) \<longrightarrow>
      (\<exists>qs. (qs, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (qs, i)) \<longrightarrow>
      (\<exists>rs. (rs, i) \<in> H \<and> (\<^bold>\<not> (\<^bold>@ j p)) on (rs, i))))\<close>

definition hequiv :: \<open>('a, 'b) block set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool\<close> where
  \<open>hequiv H i j \<equiv> \<exists>ps. (ps, i) \<in> H \<and> Nom j on (ps, i)\<close>

abbreviation hequiv_rel :: \<open>('a, 'b) block set \<Rightarrow> ('b \<times> 'b) set\<close> where
  \<open>hequiv_rel H \<equiv> {(i, j) |i j. hequiv H i j}\<close>

definition names :: \<open>('a, 'b) block set \<Rightarrow> 'b set\<close> where
  \<open>names H \<equiv> {i |block i. (block, i) \<in> H}\<close>

lemma hequiv_refl: \<open>hintikka H \<Longrightarrow> i \<in> names H \<Longrightarrow> hequiv H i i\<close>
  unfolding hintikka_def hequiv_def names_def by auto

lemma hequiv_refl': \<open>hintikka H \<Longrightarrow> (ps, i) \<in> H \<Longrightarrow> hequiv H i i\<close>
  using hequiv_refl unfolding names_def by fast

lemma hequiv_sym: \<open>hintikka H \<Longrightarrow> hequiv H i j = hequiv H j i\<close>
  unfolding hintikka_def hequiv_def by meson

lemma hequiv_trans: \<open>hintikka H \<Longrightarrow> hequiv H i j \<Longrightarrow> hequiv H j k \<Longrightarrow> hequiv H i k\<close>
  unfolding hintikka_def hequiv_def by meson

lemma hequiv_names: \<open>hequiv H i j \<Longrightarrow> i \<in> names H\<close>
  unfolding hequiv_def names_def by blast

lemma hequiv_names_rel: \<open>hintikka H \<Longrightarrow> hequiv_rel H \<subseteq> names H \<times> names H\<close>
  using hequiv_sym hequiv_names by fast

lemma hequiv_refl_rel: \<open>hintikka H \<Longrightarrow> refl_on (names H) (hequiv_rel H)\<close>
  unfolding refl_on_def using hequiv_refl hequiv_names_rel by fast

lemma hequiv_sym_rel: \<open>hintikka H \<Longrightarrow> sym (hequiv_rel H)\<close>
  unfolding sym_def using hequiv_sym by fast

lemma hequiv_trans_rel: \<open>hintikka H \<Longrightarrow> trans (hequiv_rel H)\<close>
  unfolding trans_def using hequiv_trans by fast

lemma hequiv_rel: \<open>hintikka H \<Longrightarrow> equiv (names H) (hequiv_rel H)\<close>
  using hequiv_refl_rel hequiv_sym_rel hequiv_trans_rel by (rule equivI)

subsection \<open>Named Model\<close>

abbreviation \<open>proj \<equiv> Equiv_Relations.proj\<close>

abbreviation assign :: \<open>('a, 'b) block set \<Rightarrow> 'b \<Rightarrow> 'b set\<close> where
  \<open>assign H i \<equiv> proj (hequiv_rel H) i\<close>

abbreviation reach :: \<open>('a, 'b) block set \<Rightarrow> 'b set \<Rightarrow> 'b set set\<close> where
  \<open>reach H is \<equiv> {assign H j |i j ps. i \<in> is \<and> (ps, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (ps, i)}\<close>

abbreviation val :: \<open>('a, 'b) block set \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>val H is x \<equiv> \<exists>i \<in> is. \<exists>ps. (ps, i) \<in> H \<and> Pro x on (ps, i)\<close>

lemma hequiv_assign: \<open>hintikka H \<Longrightarrow> hequiv H i j \<Longrightarrow> assign H i = assign H j\<close>
  unfolding proj_def using equiv_class_eq hequiv_rel by fast

lemma hequiv_model:
  assumes \<open>hintikka H\<close> \<open>hequiv H i j\<close>
  shows
    \<open>(Model (reach H) (val H), assign H, assign H i \<Turnstile> p) =
     (Model (reach H) (val H), assign H, assign H j \<Turnstile> p)\<close>
  using assms hequiv_assign by fastforce

lemma assign_refl: \<open>hintikka H \<Longrightarrow> i \<in> names H \<Longrightarrow> i \<in> assign H i\<close>
  unfolding proj_def using hequiv_refl by fastforce

lemma assign_refl': \<open>hintikka H \<Longrightarrow> (ps, i) \<in> H \<Longrightarrow> i \<in> assign H i\<close>
  using assign_refl unfolding names_def by fast

lemma assign_named: \<open>hintikka H \<Longrightarrow> i \<in> names H \<Longrightarrow> \<forall>j \<in> assign H i. \<exists>ps. (ps, j) \<in> H\<close>
  using hequiv_sym unfolding proj_def hequiv_def by fast

lemma nominal_in_names:
  assumes \<open>hintikka H\<close> \<open>\<exists>block \<in> H. i \<in> block_nominals block\<close>
  shows \<open>i \<in> names H\<close>
proof -
  have \<open>(\<forall>p. i \<in> nominals p \<and> (\<exists>block \<in> H. p on block) \<longrightarrow> (\<exists>br. (br, i) \<in> H))\<close>
    using \<open>hintikka H\<close> unfolding hintikka_def by meson
  then show ?thesis
    unfolding names_def using assms(2) by fastforce
qed

lemma assign_sym: \<open>hintikka H \<Longrightarrow> j \<in> assign H i \<longleftrightarrow> i \<in> assign H j\<close>
  unfolding proj_def using hequiv_sym by fast

lemma hintikka_model:
  assumes \<open>hintikka H\<close>
  shows
    \<open>(ps, i) \<in> H \<Longrightarrow> p on (ps, i) \<Longrightarrow> Model (reach H) (val H), assign H, assign H i \<Turnstile> p\<close>
    \<open>(ps, i) \<in> H \<Longrightarrow> (\<^bold>\<not> p) on (ps, i) \<Longrightarrow> \<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> p\<close>
proof (induct p arbitrary: i ps)
  fix ps i
  case (Pro x)
  assume \<open>Pro x on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  then show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> Pro x\<close>
    using assms assign_refl' by fastforce
next
  fix ps i
  case (Pro x)
  assume \<open>(\<^bold>\<not> Pro x) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  then have \<open>\<exists>ps. (ps, i) \<in> H \<and> Nom j on (ps, i) \<Longrightarrow> \<nexists>qs. (qs, j) \<in> H \<and> Pro x on (qs, j)\<close> for j
    using assms unfolding hintikka_def by meson
  then have \<open>hequiv H i j \<Longrightarrow> \<nexists>qs. (qs, j) \<in> H \<and> Pro x on (qs, j)\<close> for j
    unfolding hequiv_def by simp
  then have \<open>\<not> val H (assign H i) x\<close>
    unfolding proj_def by blast
  then show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> Pro x\<close>
    by simp
next
  fix ps i
  case (Nom a)
  assume \<open>Nom a on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  then have \<open>assign H a = assign H i\<close>
    using assms hequiv_assign hequiv_sym unfolding hequiv_def by fast
  then show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> Nom a\<close>
    by simp
next
  fix ps i
  case (Nom a)
  assume \<open>(\<^bold>\<not> Nom a) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  then have \<open>\<nexists>qs. (qs, i) \<in> H \<and> Nom a on (qs, i)\<close>
    using assms unfolding hintikka_def by meson
  then have \<open>\<not> hequiv H i a\<close>
    unfolding hequiv_def by blast
  then have \<open>\<not> hequiv H a i\<close>
    using assms hequiv_sym by fast
  moreover have \<open>hequiv H i i\<close>
    using assms \<open>(ps, i) \<in> H\<close> hequiv_refl' by fast
  ultimately have \<open>assign H a \<noteq> assign H i\<close>
    unfolding proj_def by blast
  then show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> Nom a\<close>
    by simp
next
  fix ps i
  case (Neg p)
  moreover assume \<open>(\<^bold>\<not> p) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  ultimately show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<not> p\<close>
    using assms by simp
next
  fix ps i
  case (Neg p)
  moreover assume \<open>(\<^bold>\<not> \<^bold>\<not> p) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  then have \<open>\<exists>ps. (ps, i) \<in> H \<and> p on (ps, i)\<close>
    using assms unfolding hintikka_def by meson
  ultimately show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<not> p\<close>
    using assms by auto
next
  fix ps i
  case (Dis p q)
  moreover assume \<open>(p \<^bold>\<or> q) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  then have \<open>\<exists>ps. (ps, i) \<in> H \<and> (p on (ps, i) \<or> q on (ps, i))\<close>
    using assms unfolding hintikka_def by meson
  ultimately show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> (p \<^bold>\<or> q)\<close>
    by (meson semantics.simps(4))
next
  fix ps i
  case (Dis p q)
  moreover assume \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  then have \<open>\<exists>ps. (ps, i) \<in> H \<and> (\<^bold>\<not> p) on (ps, i) \<and> (\<^bold>\<not> q) on (ps, i)\<close>
    using assms unfolding hintikka_def by meson
  ultimately show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> (p \<^bold>\<or> q)\<close>
    by auto
next
  fix ps i
  case (Dia p)
  moreover assume \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  ultimately show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<diamond> p\<close>
  proof (cases \<open>\<exists>j. p = Nom j\<close>)
    case True
    then obtain j where \<open>p = Nom j\<close>
      by blast
    have \<open>i \<in> assign H i\<close>
      using assms \<open>(ps, i) \<in> H\<close> assign_refl' by fast
    moreover have \<open>j \<in> nominals (\<^bold>\<diamond> p)\<close>
      using \<open>p = Nom j\<close> by simp
    then have \<open>(\<exists>block \<in> H. (\<^bold>\<diamond> p) on block) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H)\<close>
      using assms unfolding hintikka_def by meson
    then have \<open>\<exists>bl. (bl, j) \<in> H\<close>
      using \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close> by blast
    then have \<open>j \<in> assign H j\<close>
      using assms \<open>(ps, i) \<in> H\<close> assign_refl' by fast
    moreover have \<open>(\<^bold>\<diamond> Nom j) on (ps, i)\<close>
      using \<open>p = Nom j\<close> \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> by blast
    ultimately have \<open>assign H j \<in> reach H (assign H i)\<close>
      using \<open>(ps, i) \<in> H\<close> by auto
    then show ?thesis
      using \<open>p = Nom j\<close> by simp
  next
    case False
    then have
      \<open>\<exists>j. (\<exists>qs. (qs, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (qs, i)) \<and> (\<exists>rs. (rs, i) \<in> H \<and> (\<^bold>@ j p) on (rs, i))\<close>
      using assms \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close> unfolding hintikka_def by blast
    then obtain j qs rs where
      qs: \<open>(qs, i) \<in> H\<close> \<open>(\<^bold>\<diamond> Nom j) on (qs, i)\<close> and
      rs: \<open>(rs, i) \<in> H\<close> \<open>(\<^bold>@ j p) on (rs, i)\<close>
      by blast

    from rs have \<open>\<exists>ts. (ts, j) \<in> H \<and> p on (ts, j)\<close>
      using assms unfolding hintikka_def by blast
    then have \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close>
      using Dia by blast

    have \<open>i \<in> assign H i\<close>
      using assms assign_refl' \<open>(ps, i) \<in> H\<close> by fast
    moreover have \<open>j \<in> assign H j\<close>
      using assms assign_refl' \<open>\<exists>ts. (ts, j) \<in> H \<and> p on (ts, j)\<close> by fast
    ultimately have \<open>assign H j \<in> reach H (assign H i)\<close>
      using qs by auto
    then show ?thesis
      using \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close> by auto
  qed
next
  fix ps i
  case (Dia p)
  assume \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<diamond> p\<close>
  proof
    assume \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<diamond> p\<close>
    then obtain i' j qs where
      \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close>
      \<open>i' \<in> assign H i\<close> \<open>(qs, i') \<in> H\<close> \<open>(\<^bold>\<diamond> Nom j) on (qs, i')\<close>
      by auto

    have \<open>\<exists>rs. (rs, i) \<in> H \<and> Nom i' on (rs, i)\<close>
      using \<open>i' \<in> assign H i\<close> \<open>(qs, i') \<in> H\<close> unfolding hequiv_def proj_def by auto
    then have \<open>\<exists>rs. (rs, i') \<in> H \<and> Nom i on (rs, i')\<close>
      using assms unfolding hintikka_def by meson
    then have \<open>\<exists>rs. (rs, i) \<in> H \<and> (\<^bold>\<diamond> Nom j) on (rs, i)\<close>
      using assms \<open>(\<^bold>\<diamond> Nom j) on (qs, i')\<close> \<open>(qs, i') \<in> H\<close> unfolding hintikka_def by meson
    then have \<open>\<exists>rs. (rs, i) \<in> H \<and> (\<^bold>\<not> (\<^bold>@ j p)) on (rs, i)\<close>
      using assms \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close> unfolding hintikka_def by meson
    moreover have \<open>(\<exists>block \<in> H. (\<^bold>\<not> (\<^bold>@ j p)) on block) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H \<and> (\<^bold>\<not> p) on (qs, j))\<close>
      using assms unfolding hintikka_def by meson
    ultimately obtain rs where \<open>(rs, j) \<in> H\<close> \<open>(\<^bold>\<not> p) on (rs, j)\<close>
      by blast
    then have \<open>\<not> Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close>
      using Dia by blast
    then show False
      using \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close> by blast
  qed
next
  fix ps i
  case (Sat j p)
  assume \<open>(\<^bold>@ j p) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  moreover have \<open>(\<exists>block \<in> H. (\<^bold>@ j p) on block) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H \<and> p on (qs, j))\<close>
    using assms unfolding hintikka_def by meson
  ultimately obtain qs where \<open>(qs, j) \<in> H\<close> \<open>p on (qs, j)\<close>
    by blast
  then show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>@ j p\<close>
    using Sat by simp
next
  fix ps i
  case (Sat j p)
  assume \<open>(\<^bold>\<not> (\<^bold>@ j p)) on (ps, i)\<close> \<open>(ps, i) \<in> H\<close>
  moreover have \<open>(\<exists>block \<in> H. (\<^bold>\<not> (\<^bold>@ j p)) on block) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H \<and> (\<^bold>\<not> p) on (qs, j))\<close>
    using assms unfolding hintikka_def by meson
  ultimately obtain qs where \<open>(qs, j) \<in> H\<close> \<open>(\<^bold>\<not> p) on (qs, j)\<close>
    by blast
  then show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>@ j p\<close>
    using Sat by simp
qed

subsection \<open>Structural Property\<close>

lemma block_nominals_branch:
  assumes \<open>block \<in> set branch\<close>
  shows \<open>block_nominals block \<subseteq> branch_nominals branch\<close>
  unfolding branch_nominals_def using assms by blast

lemma sub_comp: \<open>sub f (sub g p) = sub (f o g) p\<close>
  by (induct p) simp_all

lemma sub_list_comp: \<open>sub_list f (sub_list g ps) = sub_list (f o g) ps\<close>
  using sub_comp by (induct ps) auto

lemma sub_block_comp: \<open>sub_block f (sub_block g block) = sub_block (f o g) block\<close>
  using sub_comp by (induct block) auto

lemma sub_branch_comp: \<open>sub_branch f (sub_branch g branch) = sub_branch (f o g) branch\<close>
  unfolding sub_branch_def using sub_block_comp by (induct branch) fastforce+

lemma swap_id: \<open>(id(i := j, j := i)) o (id(i := j, j := i)) = id\<close>
  by auto

lemma opening_in_branch: \<open>(ps, i) \<in> set branch \<Longrightarrow> i \<in> branch_nominals branch\<close>
  unfolding branch_nominals_def by (induct branch) auto

lemma sub_block_fresh:
  assumes \<open>i \<notin> branch_nominals branch\<close> \<open>block \<in> set branch\<close>
  shows \<open>sub_block (f(i := j)) block = sub_block f block\<close>
  using assms block_nominals_branch sub_block_upd_fresh by fast

lemma list_down_induct [consumes 1, case_names Start Cons]:
  assumes \<open>\<forall>y \<in> set ys. Q y\<close> \<open>P (ys @ xs)\<close> \<open>\<And>y ys. Q y \<Longrightarrow> P (y # ys) \<Longrightarrow> P ys\<close>
  shows \<open>P xs\<close>
  using assms by (induct ys) auto

lemma STB_drop_prefix:
  assumes
    \<open>\<turnstile> (ps @ ps', a) # branch\<close> \<open>set ps \<subseteq> set qs\<close> \<open>(qs, b) \<in> set branch\<close> \<open>Nom a on (qs, b)\<close>
  shows \<open>\<turnstile> (ps', a) # branch\<close>
proof -
  have \<open>\<forall>p \<in> set ps. p on (qs, b)\<close>
    using assms(2) by fastforce
  then show ?thesis
  proof (induct ps' rule: list_down_induct)
    case Start
    then show ?case
      using assms(1) .
  next
    case (Cons p ps)
    then show ?case
      using assms STB.Nom by (metis list.set_intros(2) on.simps)
  qed
qed

lemma STB_drop_block:
  assumes
    \<open>\<turnstile> (ps, a) # branch\<close> \<open>(qs, b) \<in> set branch\<close>
    \<open>set ps \<subseteq> set qs\<close> \<open>Nom a on (qs, b)\<close>
  shows \<open>\<turnstile> branch\<close>
proof -
  have \<open>\<turnstile> ([], a) # branch\<close>
    using assms STB_drop_prefix[where ps'=\<open>[]\<close>] by simp
  moreover have \<open>a \<in> branch_nominals branch\<close>
    unfolding branch_nominals_def using \<open>Nom a on (qs, b)\<close> \<open>(qs, b) \<in> set branch\<close>
    by fastforce
  ultimately show ?thesis
    using STB.GoTo by fast
qed

lemma STB_drop_block':
  assumes \<open>\<turnstile> (ps, a) # branch\<close> \<open>(ps, a) \<in> set branch\<close>
  shows \<open>\<turnstile> branch\<close>
  using assms STB_drop_block by fastforce

lemma sub_branch_image: \<open>set (sub_branch f branch) = sub_block f ` set branch\<close>
  unfolding sub_branch_def by simp

lemma sub_block_repl:
  \<open>j \<notin> block_nominals block \<Longrightarrow> i \<notin> block_nominals (sub_block (id(i := j, j := i)) block)\<close>
  by (simp add: image_iff sub_block_nominals)

lemma sub_branch_repl:
  \<open>j \<notin> branch_nominals branch \<Longrightarrow> i \<notin> branch_nominals (sub_branch (id(i := j, j := i)) branch)\<close>
  by (simp add: image_iff sub_branch_nominals)

lemma STB_struct:
  fixes branch :: \<open>('a, 'b) branch\<close>
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>\<turnstile> branch\<close>
    \<open>set branch \<subseteq> set branch'\<close>
  shows \<open>\<turnstile> branch'\<close>
  using assms(2-3)
proof (induct branch arbitrary: branch' rule: STB.induct)
  case (Close ps i branch qs p)
  then show ?case
    using STB.Close[where branch=branch'] by blast
next
  case (Neg qs a ps branch p)
  then have \<open>set ((p # ps, a) # branch) \<subseteq> set ((p # ps, a) # (ps, a) # branch')\<close>
    by auto
  then have \<open>\<turnstile> (p # ps, a) # (ps, a) # branch'\<close>
    using Neg by blast
  moreover have \<open>(qs, a) \<in> set ((ps, a) # branch')\<close>
    using Neg by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using Neg by (simp add: STB.Neg)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (DisP qs a ps branch p q)
  then have
    \<open>set ((p # ps, a) # branch) \<subseteq> set ((p # ps, a) # (ps, a) # branch')\<close>
    \<open>set ((q # ps, a) # branch) \<subseteq> set ((q # ps, a) # (ps, a) # branch')\<close>
    by auto
  then have \<open>\<turnstile> (p # ps, a) # (ps, a) # branch'\<close> \<open>\<turnstile> (q # ps, a) # (ps, a) # branch'\<close>
    using DisP by blast+
  moreover have \<open>(qs, a) \<in> set ((ps, a) # branch')\<close>
    using DisP by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using DisP by (simp add: STB.DisP)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (DisN qs a ps branch p q)
  then have \<open>set (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch) \<subseteq>
      set (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # (ps, a) # branch')\<close>
    by auto
  then have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # (ps, a) # branch'\<close>
    using DisN by blast
  moreover have \<open>(qs, a) \<in> set ((ps, a) # branch')\<close>
    using DisN by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using DisN by (simp add: STB.DisN)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (DiaP qs a ps branch p i)
  have \<open>finite (branch_nominals ((ps, a) # branch'))\<close>
    by (simp add: finite_branch_nominals)
  then obtain j where j: \<open>j \<notin> branch_nominals ((ps, a) # branch')\<close>
    using assms ex_new_if_finite by blast
  then have j': \<open>j \<notin> branch_nominals ((ps, a) # branch)\<close>
    using DiaP unfolding branch_nominals_def by (simp add: subset_code(1))

  let ?f = \<open>id(i := j, j := i)\<close>
  let ?branch' = \<open>sub_branch ?f ((ps, a) # branch')\<close>
  have branch': \<open>sub_branch ?f ?branch' = ((ps, a) # branch')\<close>
    using sub_branch_comp sub_branch_id swap_id by metis

  have branch: \<open>sub_branch ?f ((ps, a) # branch) = (ps, a) # branch\<close>
    using \<open>i \<notin> branch_nominals ((ps, a) # branch)\<close> j' sub_branch_id sub_branch_upd_fresh by metis
  moreover have \<open>set (sub_branch ?f ((ps, a) # branch)) \<subseteq> set (sub_branch ?f branch')\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> sub_branch_image by blast
  ultimately have *: \<open>set ((ps, a) # branch) \<subseteq> set ?branch'\<close>
    unfolding sub_branch_def by auto

  have \<open>i \<notin> block_nominals (ps, a)\<close>
    using DiaP unfolding branch_nominals_def by simp
  moreover have \<open>i \<notin> branch_nominals ?branch'\<close>
    using j sub_branch_repl by metis
  ultimately have i: \<open>i \<notin> branch_nominals ((ps, a) # ?branch')\<close>
    unfolding branch_nominals_def by simp

  have \<open>set (((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch) \<subseteq>
      set (((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # ?branch')\<close>
    using * by auto
  then have \<open>\<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # ?branch'\<close>
    using DiaP by blast
  moreover have \<open>(qs, a) \<in> set ((ps, a) # ?branch')\<close>
    using DiaP * by auto
  ultimately have \<open>\<turnstile> (ps, a) # ?branch'\<close>
    using DiaP i by (simp add: STB.DiaP)
  then have \<open>\<turnstile> sub_branch ?f ((ps, a) # ?branch')\<close>
    using STB_sub inf by blast
  then have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using branch' branch unfolding sub_branch_def by simp
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (DiaN qs a ps branch p rs i)
  then have \<open>set (((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch) \<subseteq>
      set (((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # (ps, a) # branch')\<close>
    by auto
  then have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # (ps, a) # branch'\<close>
    using DiaN by blast
  moreover have \<open>(qs, a) \<in> set ((ps, a) # branch')\<close> \<open>(rs, a) \<in> set ((ps, a) # branch')\<close>
    using DiaN by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using DiaN by (simp add: STB.DiaN)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (SatP qs a ps branch i rs b p)
  then have \<open>set ((p # ps, a) # branch) \<subseteq> set ((p # ps, a) # (ps, a) # branch')\<close>
    by auto
  then have \<open>\<turnstile> (p # ps, a) # (ps, a) # branch'\<close>
    using SatP by blast
  moreover have \<open>(qs, a) \<in> set ((ps, a) # branch')\<close> \<open>(rs, b) \<in> set ((ps, a) # branch')\<close>
    using SatP by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using SatP by (simp add: STB.SatP)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (SatN qs a ps branch i rs b p)
  then have \<open>set (((\<^bold>\<not> p) # ps, a) # branch) \<subseteq> set (((\<^bold>\<not> p) # ps, a) # (ps, a) # branch')\<close>
    by auto
  then have \<open>\<turnstile> ((\<^bold>\<not> p) # ps, a) # (ps, a) # branch'\<close>
    using SatN by blast
  moreover have \<open>(qs, a) \<in> set ((ps, a) # branch')\<close> \<open>(rs, b) \<in> set ((ps, a) # branch')\<close>
    using SatN by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using SatN by (simp add: STB.SatN)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (GoTo i branch)
  then have \<open>set (([], i) # branch) \<subseteq> set (([], i) # branch')\<close>
    by auto
  then have \<open>\<turnstile> ([], i) # branch'\<close>
    using GoTo by simp
  moreover have \<open>i \<in> branch_nominals branch'\<close>
    using GoTo unfolding branch_nominals_def by blast
  ultimately show ?case
    by (simp add: STB.GoTo)
next
  case (Nom qs b ps a branch p i)
  have \<open>set ((p # ps, a) # branch) \<subseteq> set ((p # ps, a) # (ps, a) # branch')\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by auto
  then have \<open>\<turnstile> (p # ps, a) # (ps, a) # branch'\<close>
    using Nom by blast
  moreover have \<open>(qs, b) \<in> set ((ps, a) # branch')\<close>
    using Nom by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using Nom by (simp add: STB.Nom)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
next
  case (Bridge qs a ps branch j rs k)
  then have \<open>set (((\<^bold>\<diamond> Nom k) # ps, a) # branch) \<subseteq> set (((\<^bold>\<diamond> Nom k) # ps, a) # (ps, a) # branch')\<close>
    by auto
  then have \<open>\<turnstile> ((\<^bold>\<diamond> Nom k) # ps, a) # (ps, a) # branch'\<close>
    using Bridge by blast
  moreover have \<open>(qs, a) \<in> set ((ps, a) # branch')\<close>
    using Bridge by auto
  moreover have \<open>(rs, j) \<in> set ((ps, a) # branch')\<close>
    using Bridge by auto
  ultimately have \<open>\<turnstile> (ps, a) # (ps, a) # branch'\<close>
    using Bridge by (simp add: STB.Bridge)
  moreover have \<open>(ps, a) \<in> set branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    by (metis STB_drop_block' list.set_intros(1))
qed

lemma STB_struct_block:
  fixes branch :: \<open>('a, 'b) branch\<close>
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>\<turnstile> (ts, a) # branch\<close> \<open>set ts \<subseteq> set ts'\<close>
  shows \<open>\<turnstile> (ts', a) # branch\<close>
  using assms(2-3)
proof (induct \<open>(ts, a) # branch\<close> arbitrary: ts ts' rule: STB.induct)
  case (Close ps i qs p)
  then obtain ps' where \<open>(ps', i) \<in> set ((ts', a) # branch)\<close> \<open>p on (ps', i)\<close>
    by auto
  moreover obtain qs' where \<open>(qs', i) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>\<not> p) on (qs', i)\<close>
    using Close by auto
  ultimately show ?case
    by (simp add: STB.Close)
next
  case (Neg qs ps p)
  then obtain qs' where \<open>(qs', a) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>\<not> \<^bold>\<not> p) on (qs', a)\<close>
    by auto
  moreover have \<open>set (p # ps) \<subseteq> set (p # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> (p # ts', a) # branch\<close>
    using Neg by blast
  ultimately show ?case
    by (simp add: STB.Neg)
next
  case (DisP qs ps p q)
  then obtain qs' where \<open>(qs', a) \<in> set ((ts', a) # branch)\<close> \<open>(p \<^bold>\<or> q) on (qs', a)\<close>
    by auto
  moreover have \<open>set (p # ps) \<subseteq> set (p # ts')\<close> \<open>set (q # ps) \<subseteq> set (q # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> (p # ts', a) # branch\<close> \<open>\<turnstile> (q # ts', a) # branch\<close>
    using DisP by blast+
  ultimately show ?case
    by (simp add: STB.DisP)
next
  case (DisN qs ps p q)
  then obtain qs' where \<open>(qs', a) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) on (qs', a)\<close>
    by auto
  moreover have \<open>set ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps) \<subseteq> set ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ts', a) # branch\<close>
    using DisN by blast
  ultimately show ?case
    by (simp add: STB.DisN)
next
  case (DiaP qs ps p i)
  have \<open>finite (branch_nominals ((ts', a) # branch))\<close>
    using finite_branch_nominals by blast
  then obtain j where j: \<open>j \<notin> branch_nominals ((ts', a) # branch)\<close>
    using assms ex_new_if_finite by blast
  then have j': \<open>j \<notin> block_nominals (ps, a)\<close>
    using DiaP unfolding branch_nominals_def by auto

  let ?f = \<open>id(i := j, j := i)\<close>
  let ?ts' = \<open>sub_list ?f ts'\<close>
  have ts': \<open>sub_list ?f ?ts' = ts'\<close>
    using sub_list_comp sub_list_id swap_id by metis

  have \<open>i \<notin> block_nominals (ps, a)\<close>
    using DiaP unfolding branch_nominals_def by simp
  then have ps: \<open>sub_block ?f (ps, a) = (ps, a)\<close>
    using j' sub_block_id sub_block_upd_fresh by metis
  moreover have \<open>set (sub_list ?f ps) \<subseteq> set (sub_list ?f ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  ultimately have *: \<open>set ps \<subseteq> set ?ts'\<close>
    by simp

  have \<open>i \<notin> branch_nominals branch\<close>
    using DiaP unfolding branch_nominals_def by simp
  moreover have \<open>j \<notin> branch_nominals branch\<close>
    using j unfolding branch_nominals_def by simp
  ultimately have branch: \<open>sub_branch ?f branch = branch\<close>
    using sub_branch_id sub_branch_upd_fresh by metis

  have \<open>i \<noteq> a\<close> \<open>j \<noteq> a\<close>
    using DiaP j unfolding branch_nominals_def by simp_all
  then have \<open>?f a = a\<close>
    by simp
  moreover have \<open>j \<notin> block_nominals (ts', a)\<close>
    using j unfolding branch_nominals_def by simp
  ultimately have \<open>i \<notin> block_nominals (?ts', a)\<close>
    using sub_block_repl[where block=\<open>(ts', a)\<close> and i=i and j=j] by simp

  obtain qs' where \<open>(qs', a) \<in> set ((?ts', a) # branch)\<close> \<open>(\<^bold>\<diamond> p) on (qs', a)\<close>
    using DiaP(1, 2, 4) * by force
  moreover have \<open>set ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps) \<subseteq> set ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ?ts')\<close>
    using * by auto
  then have \<open>\<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ?ts', a) # branch\<close>
    using DiaP by blast
  moreover have \<open>i \<notin> branch_nominals ((?ts', a) # branch)\<close>
    using DiaP \<open>i \<notin> block_nominals (?ts', a)\<close> unfolding branch_nominals_def by simp
  ultimately have \<open>\<turnstile> (?ts', a) # branch\<close>
    using DiaP by (simp add: STB.DiaP)
  then have \<open>\<turnstile> sub_branch ?f ((?ts', a) # branch)\<close>
    using STB_sub inf by blast
  then have \<open>\<turnstile> (sub_list ?f ?ts', ?f a) # sub_branch ?f branch\<close>
    unfolding sub_branch_def by simp
  then show ?case
    using \<open>?f a = a\<close> ts' branch by simp
next
  case (DiaN qs ps p rs i)
  then obtain qs' where \<open>(qs', a) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) on (qs', a)\<close>
    by auto
  moreover obtain rs' where \<open>(rs', a) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>\<diamond> Nom i) on (rs', a)\<close>
    using DiaN by auto
  moreover have \<open>set ((\<^bold>\<not> (\<^bold>@ i p)) # ps) \<subseteq> set ((\<^bold>\<not> (\<^bold>@ i p)) # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ts', a) # branch\<close>
    using DiaN by blast
  ultimately show ?case
    by (simp add: STB.DiaN)
next
  case (SatP qs ps i rs b p)
  then obtain qs' where \<open>(qs', a) \<in> set ((ts', a) # branch)\<close> \<open>Nom i on (qs', a)\<close>
    by auto
  moreover obtain rs' where \<open>(rs', b) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>@ i p) on (rs', b)\<close>
    using SatP by auto
  moreover have \<open>set (p # ps) \<subseteq> set (p # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> (p # ts', a) # branch\<close>
    using SatP by blast
  ultimately show ?case
    by (simp add: STB.SatP)
next
  case (SatN qs ps i rs b p)
  then obtain qs' where \<open>(qs', a) \<in> set ((ts', a) # branch)\<close> \<open>Nom i on (qs', a)\<close>
    by auto
  moreover obtain rs' where \<open>(rs', b) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>\<not> (\<^bold>@ i p)) on (rs', b)\<close>
    using SatN by auto
  moreover have \<open>set ((\<^bold>\<not> p) # ps) \<subseteq> set ((\<^bold>\<not> p) # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> ((\<^bold>\<not> p) # ts', a) # branch\<close>
    using SatN by blast
  ultimately show ?case
    by (simp add: STB.SatN)
next
  case (GoTo i)
  then have \<open>\<turnstile> (ts, a) # branch\<close>
    using GoTo by (simp add: STB.GoTo)
  moreover have \<open>set ((ts, a) # branch) \<subseteq> set ((ts, a) # (ts', a) # branch)\<close>
    by auto
  ultimately have \<open>\<turnstile> (ts, a) # (ts', a) # branch\<close>
    using STB_struct inf by blast
  then show ?case
    using STB_drop_block inf \<open>set ts \<subseteq> set ts'\<close> by fastforce
next
  case (Nom qs b ps p i)
  then obtain qs' where \<open>(qs', b) \<in> set ((ts', a) # branch)\<close> \<open>Nom i on (qs', b)\<close> \<open>p on (qs', b)\<close>
    by auto
  moreover have \<open>Nom i on (ts', a)\<close>
    using Nom by auto
  moreover have \<open>set (p # ps) \<subseteq> set (p # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> (p # ts', a) # branch\<close>
    using Nom by blast
  ultimately show ?case
    using Nom by (simp add: STB.Nom)
next
  case (Bridge qs ps j rs k)
  then obtain qs' where \<open>(qs', a) \<in> set ((ts', a) # branch)\<close> \<open>(\<^bold>\<diamond> Nom j) on (qs', a)\<close>
    by auto
  moreover obtain rs' where \<open>(rs', j) \<in> set ((ts', a) # branch)\<close> \<open>Nom k on (rs', j)\<close>
    using Bridge by auto
  moreover have \<open>set ((\<^bold>\<diamond> Nom k) # ps) \<subseteq> set ((\<^bold>\<diamond> Nom k) # ts')\<close>
    using \<open>set ps \<subseteq> set ts'\<close> by auto
  then have \<open>\<turnstile> ((\<^bold>\<diamond> Nom k) # ts', a) # branch\<close>
    using Bridge by blast
  ultimately show ?case
    by (simp add: STB.Bridge)
qed

subsection \<open>Lindenbaum-Henkin\<close>

definition consistent :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> \<turnstile> S'\<close>

instance fm :: (countable, countable) countable
  by countable_datatype

fun proper_dia :: \<open>('a, 'b) fm \<Rightarrow> ('a, 'b) fm option\<close> where
  \<open>proper_dia (\<^bold>\<diamond> p) = (if \<nexists>a. p = Nom a then Some p else None)\<close>
| \<open>proper_dia _ = None\<close>

lemma proper_dia: \<open>proper_dia p = Some q \<Longrightarrow> p = (\<^bold>\<diamond> q) \<and> (\<nexists>a. q = Nom a)\<close>
  by (cases p) (simp_all, metis option.discI option.inject)

primrec witness_list :: \<open>('a, 'b) fm list \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) fm list\<close> where
  \<open>witness_list [] _ = []\<close>
| \<open>witness_list (p # ps) used =
    (case proper_dia p of
      None \<Rightarrow> witness_list ps used
    | Some q \<Rightarrow>
        let i = SOME i. i \<notin> used
        in (\<^bold>@ i q) # (\<^bold>\<diamond> Nom i) # witness_list ps ({i} \<union> used))\<close>

primrec witness :: \<open>('a, 'b) block \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) block\<close> where
  \<open>witness (ps, a) used = (witness_list ps used, a)\<close>

lemma witness_list:
  \<open>proper_dia p = Some q \<Longrightarrow> witness_list (p # ps) used =
    (let i = SOME i. i \<notin> used in (\<^bold>@ i q) # (\<^bold>\<diamond> Nom i) # witness_list ps ({i} \<union> used))\<close>
  by simp

primrec extend ::
  \<open>('a, 'b) block set \<Rightarrow> (nat \<Rightarrow> ('a, 'b) block) \<Rightarrow> nat \<Rightarrow> ('a, 'b) block set\<close> where
  \<open>extend S f 0 = S\<close> |
  \<open>extend S f (Suc n) =
    (if \<not> consistent ({f n} \<union> extend S f n)
     then extend S f n
     else
      (if \<nexists>p. (\<^bold>\<diamond> p) on f n
       then {f n} \<union> extend S f n
       else
        let used = (\<Union>block \<in> {f n} \<union> extend S f n. block_nominals block)
        in {f n, witness (f n) used} \<union> extend S f n))\<close>

definition Extend :: \<open>('a, 'b) block set \<Rightarrow> (nat \<Rightarrow> ('a, 'b) block) \<Rightarrow> ('a, 'b) block set\<close> where
  \<open>Extend S f \<equiv> (\<Union>n. extend S f n)\<close>

lemma extend_chain: \<open>extend S f n \<subseteq> extend S f (Suc n)\<close>
  by auto

lemma extend_mem: \<open>S \<subseteq> extend S f n\<close>
  by (induct n) auto

lemma Extend_mem: \<open>S \<subseteq> Extend S f\<close>
  unfolding Extend_def using extend_mem by blast

subsubsection \<open>Consistency\<close>

lemma split_list: \<open>set A \<subseteq> {x} \<union> X \<Longrightarrow> x \<in> set A \<Longrightarrow> \<exists>B. set (x # B) = set A \<and> x \<notin> set B\<close>
  by simp (metis Diff_insert_absorb mk_disjoint_insert set_removeAll)

lemma consistent_drop_single:
  fixes a :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and cons: \<open>consistent ({(p # ps, a)} \<union> S)\<close>
  shows \<open>consistent ({(ps, a)} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {(ps, a)} \<union> S \<and> \<turnstile> S'\<close>
  then obtain S' where \<open>set S' \<subseteq> {(ps, a)} \<union> S\<close> \<open>(ps, a) \<in> set S'\<close> \<open>\<turnstile> S'\<close>
    using assms unfolding consistent_def by blast
  then obtain S'' where \<open>set ((ps, a) # S'') = set S'\<close> \<open>(ps, a) \<notin> set S''\<close>
    using split_list by metis
  then have \<open>\<turnstile> (ps, a) # S''\<close>
    using inf STB_struct \<open>\<turnstile> S'\<close> by blast
  then have \<open>\<turnstile> (p # ps, a) # S''\<close>
    using inf STB_struct_block[where ts'=\<open>p # ps\<close>] by auto
  moreover have \<open>set ((p # ps, a) # S'') \<subseteq> {(p # ps, a)} \<union> S\<close>
    using \<open>(ps, a) \<notin> set S''\<close> \<open>set ((ps, a) # S'') = set S'\<close> \<open>set S' \<subseteq> {(ps, a)} \<union> S\<close> by auto
  ultimately show False
    using cons unfolding consistent_def by blast
qed

lemma consistent_drop_block: \<open>consistent ({block} \<union> S) \<Longrightarrow> consistent S\<close>
  unfolding consistent_def by blast

lemma inconsistent_weaken: \<open>\<not> consistent S \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> \<not> consistent S'\<close>
  unfolding consistent_def by blast

lemma finite_nominals_set: \<open>finite S \<Longrightarrow> finite (\<Union>block \<in> S. block_nominals block)\<close>
  by (induct S rule: finite_induct) (simp_all add: finite_block_nominals)

lemma witness_list_used:
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>finite used\<close> \<open>i \<notin> list_nominals ps\<close>
  shows \<open>i \<notin> list_nominals (witness_list ps ({i} \<union> used))\<close>
  using assms(2-3)
proof (induct ps arbitrary: used)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then show ?case
  proof (induct \<open>proper_dia p\<close>)
    case None
    then show ?case
      by simp
  next
    case (Some q)
    let ?j = \<open>SOME j. j \<notin> {i} \<union> used\<close>
    have \<open>finite ({i} \<union> used)\<close>
      using \<open>finite used\<close> by simp
    then have \<open>\<exists>j. j \<notin> {i} \<union> used\<close>
      using inf ex_new_if_finite by metis
    then have j: \<open>?j \<notin> {i} \<union> used\<close>
      using someI_ex by metis

    have \<open>witness_list (p # ps) ({i} \<union> used) =
        (\<^bold>@ ?j q) # (\<^bold>\<diamond> Nom ?j) # witness_list ps ({?j} \<union> ({i} \<union> used))\<close>
      using \<open>Some q = proper_dia p\<close> witness_list by metis
    then have *: \<open>list_nominals (witness_list (p # ps) ({i} \<union> used)) =
        {?j} \<union> nominals q \<union> list_nominals (witness_list ps ({?j} \<union> ({i} \<union> used)))\<close>
      by simp

    have \<open>finite ({?j} \<union> used)\<close>
      using \<open>finite used\<close> by simp
    moreover have \<open>i \<notin> list_nominals ps\<close>
      using \<open>i \<notin> list_nominals (p # ps)\<close> by simp
    ultimately have \<open>i \<notin> list_nominals (witness_list ps ({i} \<union> ({?j} \<union> used)))\<close>
      using Some by metis
    moreover have \<open>{i} \<union> ({?j} \<union> used) = {?j} \<union> ({i} \<union> used)\<close>
      by blast
    moreover have \<open>i \<noteq> ?j\<close>
      using j by auto
    ultimately have \<open>i \<in> list_nominals (witness_list (p # ps) ({i} \<union> used)) \<longleftrightarrow> i \<in> nominals q\<close>
      using * by simp
    moreover have \<open>i \<notin> nominals q\<close>
      using Some proper_dia by (metis UN_iff list.set_intros(1) nominals.simps(5))
    ultimately show ?case
      by blast
  qed
qed

lemma witness_used:
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>finite used\<close> \<open>i \<notin> block_nominals block\<close>
  shows \<open>i \<notin> block_nominals (witness block ({i} \<union> used))\<close>
  using assms witness_list_used by (induct block) fastforce

lemma consistent_witness_list:
  fixes a :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent S\<close> \<open>finite S\<close>
    \<open>(ps, a) \<in> S\<close> \<open>finite used\<close> \<open>(\<Union>block \<in> S. block_nominals block) \<subseteq> used\<close>
  shows \<open>consistent ({(witness_list ps used, a)} \<union> S)\<close>
  using assms(2-6)
proof (induct ps arbitrary: used S)
  case Nil
  then have \<open>{(witness_list [] used, a)} \<union> S = S\<close>
    by auto
  then show ?case
    using \<open>consistent S\<close> by simp
next
  case (Cons p ps)
  have \<open>{(p # ps, a)} \<union> S = S\<close>
    using \<open>(p # ps, a) \<in> S\<close> by blast
  then have \<open>consistent ({(p # ps, a)} \<union> S)\<close>
    using \<open>consistent S\<close> by simp
  then have \<open>consistent ({(ps, a)} \<union> S)\<close>
    using inf consistent_drop_single by fast
  moreover have \<open>finite ({(ps, a)} \<union> S)\<close>
    using \<open>finite S\<close> by simp
  moreover have \<open>(ps, a) \<in> {(ps, a)} \<union> S\<close>
    by simp
  moreover have \<open>\<Union> (block_nominals ` ({(ps, a)} \<union> S)) \<subseteq> extra \<union> used\<close> for extra
    using \<open>(p # ps, a) \<in> S\<close> \<open>\<Union> (block_nominals ` S) \<subseteq> used\<close> by fastforce
  moreover have \<open>finite extra \<Longrightarrow> finite (extra \<union> used)\<close> for extra
    using \<open>finite used\<close> by blast
  ultimately have cons: \<open>finite extra \<Longrightarrow>
        consistent ({(witness_list ps (extra \<union> used), a)} \<union> ({(ps, a)} \<union> S))\<close> for extra
    using Cons by metis

  from Cons show ?case
  proof (induct \<open>proper_dia p\<close>)
    case None
    then have \<open>witness_list (p # ps) used = witness_list ps used\<close>
      by auto
    moreover have \<open>consistent ({(witness_list ps used, a)} \<union> ({(ps, a)} \<union> S))\<close>
      using cons[where extra=\<open>{}\<close>] by simp
    then have \<open>consistent ({(witness_list ps used, a)} \<union> S)\<close>
      by (simp add: Un_commute consistent_drop_block)
    ultimately show ?case
      by simp
  next
    case (Some q)
    let ?i = \<open>SOME i. i \<notin> used\<close>
    have \<open>\<exists>i. i \<notin> used\<close>
      using \<open>finite used\<close> inf ex_new_if_finite by metis
    then have \<open>?i \<notin> used\<close>
      using someI_ex by metis
    then have i: \<open>?i \<notin> \<Union> (block_nominals ` S)\<close>
      using Cons by blast
    then have \<open>?i \<notin> block_nominals (p # ps, a)\<close>
      using Cons by blast

    let ?tail = \<open>witness_list ps ({?i} \<union> used)\<close>

    have \<open>consistent ({(?tail, a)} \<union> ({(ps, a)} \<union> S))\<close>
      using cons[where extra=\<open>{?i}\<close>] by simp
    then have *: \<open>consistent ({(?tail, a)} \<union> S)\<close>
      by (simp add: Un_commute consistent_drop_block)

    have \<open>witness_list (p # ps) used = (\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail\<close>
      using \<open>Some q = proper_dia p\<close> witness_list by metis
    moreover have \<open>consistent ({((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)} \<union> S)\<close>
      unfolding consistent_def
    proof
      assume \<open>\<exists>S'. set S' \<subseteq> {((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)} \<union> S \<and> \<turnstile> S'\<close>
      then obtain S' where
        \<open>\<turnstile> S'\<close> and S':
        \<open>set S' \<subseteq> {((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)} \<union> S\<close>
        \<open>((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) \<in> set S'\<close>
        using * unfolding consistent_def by blast
      then obtain S'' where S'':
        \<open>set (((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # S'') = set S'\<close>
        \<open>((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) \<notin> set S''\<close>
        using split_list[where x=\<open>((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)\<close>] by blast
      then have \<open>\<turnstile> ((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # S''\<close>
        using inf STB_struct \<open>\<turnstile> S'\<close> by blast
      moreover have \<open>set (((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # S'') \<subseteq>
        set (((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # (p # ps, a) # S'')\<close>
        by auto
      ultimately have **: \<open>\<turnstile> ((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # (p # ps, a) # S''\<close>
        using inf STB_struct by blast

      have \<open>?i \<notin> block_nominals (?tail, a)\<close>
        using inf \<open>finite used\<close> \<open>?i \<notin> block_nominals (p # ps, a)\<close> witness_used by fastforce
      moreover have \<open>?i \<notin> branch_nominals S''\<close>
        unfolding branch_nominals_def using i S' S'' by auto
      ultimately have \<open>?i \<notin> branch_nominals ((?tail, a) # (p # ps, a) # S'')\<close>
        using \<open>?i \<notin> block_nominals (p # ps, a)\<close> unfolding branch_nominals_def by simp

      moreover have \<open>\<nexists>a. q = Nom a\<close>
        using Some proper_dia by metis
      moreover have \<open>(p # ps, a) \<in> set ((?tail, a) # (p # ps, a) # S'')\<close>
        by simp
      moreover have \<open>p = (\<^bold>\<diamond> q)\<close>
        using \<open>Some q = proper_dia p\<close> proper_dia by metis
      then have \<open>(\<^bold>\<diamond> q) on (p # ps, a)\<close>
        by simp
      ultimately have \<open>\<turnstile> (?tail, a) # (p # ps, a) # S''\<close>
        using ** STB.DiaP[where qs=\<open>p # ps\<close>] by blast
      moreover have \<open>set ((p # ps, a) # S'') \<subseteq> S\<close>
        using Some S' S'' by auto
      ultimately show False
        using * unfolding consistent_def by (simp add: subset_Un_eq)
    qed
    ultimately show ?case
      by simp
  qed
qed

lemma consistent_witness:
  fixes block :: \<open>('a, 'b) block\<close>
  assumes \<open>infinite (UNIV :: 'b set)\<close> \<open>consistent S\<close> \<open>finite S\<close> \<open>block \<in> S\<close>
  shows \<open>consistent ({witness block ((\<Union>block \<in> S. block_nominals block))} \<union> S)\<close>
  using assms
proof (induct block)
  case (Pair ps i)
  then have \<open>finite (\<Union>block \<in> S. block_nominals block)\<close>
    using finite_nominals_set by blast
  then show ?case
    using Pair consistent_witness_list
    by (metis (full_types) Sup_least finite_imageI le_cSup_finite witness.simps)
qed

lemma finite_extend: \<open>finite S \<Longrightarrow> finite (extend S f n)\<close>
  by (induct n) simp_all

lemma consistent_extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent (extend S f n)\<close> \<open>finite S\<close>
  shows \<open>consistent (extend S f (Suc n))\<close>
proof -
  consider
    (inconsistent) \<open>\<not> consistent ({f n} \<union> extend S f n)\<close> |
    (clear) \<open>consistent ({f n} \<union> extend S f n) \<and> (\<nexists>p. (\<^bold>\<diamond> p) on f n)\<close> |
    (dia) \<open>consistent ({f n} \<union> extend S f n) \<and> (\<exists>p. (\<^bold>\<diamond> p) on f n)\<close>
    by blast
  then show ?thesis
  proof cases
    case inconsistent
    then show ?thesis
      using assms by simp
  next
    case clear
    then show ?thesis
      by simp
  next
    case dia
    let ?used = \<open>\<Union>block \<in> {f n} \<union> extend S f n. block_nominals block\<close>
    have *: \<open>extend S f (n + 1) = {f n, witness (f n) ?used} \<union> extend S f n\<close>
      using dia by simp

    have \<open>consistent ({f n} \<union> extend S f n)\<close>
      using dia by simp
    moreover have \<open>finite ({f n} \<union> extend S f n)\<close>
      using \<open>finite S\<close> finite_extend by blast
    moreover have \<open>f n \<in> {f n} \<union> extend S f n\<close>
      by simp
    ultimately have \<open>consistent ({witness (f n) ?used} \<union> ({f n} \<union> extend S f n))\<close>
      using inf consistent_witness by blast
    then show ?thesis
      using * by simp
  qed
qed

lemma consistent_extend':
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent S\<close> \<open>finite S\<close>
  shows \<open>consistent (extend S f n)\<close>
  using assms by (induct n) (simp, metis consistent_extend)

lemma UN_subset:
  fixes m :: nat
  shows \<open>m \<le> m' \<Longrightarrow> (\<Union>n \<le> m. f n) \<subseteq> (\<Union>n \<le> m'. f n)\<close>
  by fastforce

lemma UN_finite_bound: \<open>finite A \<Longrightarrow> A \<subseteq> (\<Union>n. f n) \<Longrightarrow> \<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
proof (induct A rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using \<open>insert x A \<subseteq> \<Union> (range f)\<close> by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed

lemma extend_bound: \<open>(\<Union>n \<le> m. extend S f n) \<subseteq> extend S f m\<close>
proof (induct m)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  have \<open>\<Union> (extend S f ` {..Suc m}) = \<Union> (extend S f ` {..m}) \<union> extend S f (Suc m)\<close>
    using atMost_Suc by auto
  also have \<open>\<dots> \<subseteq> extend S f m \<union> extend S f (Suc m)\<close>
    using Suc by blast
  also have \<open>\<dots> \<subseteq> extend S f (Suc m)\<close>
    using extend_chain by blast
  finally show ?case
    by simp
qed

lemma consistent_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent S\<close> \<open>finite S\<close>
  shows \<open>consistent (Extend S f)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent (\<Union> (range (extend S f)))\<close>
  then obtain S' where
    \<open>\<turnstile> S'\<close>
    \<open>set S' \<subseteq> (\<Union>n. extend S f n)\<close>
    unfolding consistent_def by blast
  moreover have \<open>finite (set S')\<close>
    by simp
  ultimately obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    using UN_finite_bound by metis
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend' by blast
  ultimately show False
    unfolding consistent_def using \<open>\<turnstile> S'\<close> by blast
qed

subsubsection \<open>Maximality\<close>

lemma STB_drop_opening: \<open>\<turnstile> (Nom a # ps, a) # branch \<Longrightarrow> \<turnstile> (ps, a) # branch\<close>
  using Nom by (metis list.set_intros(1) on.simps)

definition maximal :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>maximal S \<equiv> consistent S \<and> (\<forall>block. block \<notin> S \<longrightarrow> \<not> consistent ({block} \<union> S))\<close>

lemma maximal_single:
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>maximal S\<close> \<open>(ps, i) \<in> S\<close> \<open>p on (ps, i)\<close>
  shows \<open>([p], i) \<in> S\<close>
proof (rule ccontr)
  assume \<open>([p], i) \<notin> S\<close>
  then have \<open>\<not> consistent ({([p], i)} \<union> S)\<close>
    using \<open>maximal S\<close> unfolding maximal_def by simp
  then obtain S' where
    \<open>\<turnstile> S'\<close>
    \<open>set S' \<subseteq> {([p], i)} \<union> S\<close>
    \<open>([p], i) \<in> set S'\<close>
    using \<open>maximal S\<close> unfolding maximal_def consistent_def by fastforce
  then obtain S'' where \<open>set (([p], i) # S'') = set S'\<close> \<open>([p], i) \<notin> set S''\<close>
    using split_list[where x=\<open>([p], i)\<close>] by metis
  then have \<open>\<turnstile> ([p], i) # S''\<close>
    using STB_struct inf \<open>\<turnstile> S'\<close> by blast
  then have \<open>\<turnstile> (ps, i) # S''\<close>
    using \<open>p on (ps, i)\<close> inf STB_struct_block[where ts'=ps]
      STB_drop_opening[where ps=\<open>[]\<close> and a=i and branch=S'']
    by (induct \<open>p = Nom i\<close>) simp_all
  moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
    using \<open>([p], i) \<notin> set S''\<close> \<open>set S' \<subseteq> {([p], i)} \<union> S\<close>
      \<open>set (([p], i) # S'') = set S'\<close> assms(3)
    by auto
  ultimately show False
    using \<open>maximal S\<close> unfolding maximal_def consistent_def by blast
qed

lemma maximal_drop_single:
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>maximal S\<close> \<open>(p # ps, i) \<in> S\<close>
  shows \<open>(ps, i) \<in> S\<close>
proof (rule ccontr)
  assume \<open>(ps, i) \<notin> S\<close>
  then have \<open>\<not> consistent ({(ps, i)} \<union> S)\<close>
    using \<open>maximal S\<close> unfolding maximal_def by simp
  then obtain S' where
    \<open>\<turnstile> S'\<close>
    \<open>set S' \<subseteq> {(ps, i)} \<union> S\<close>
    \<open>(ps, i) \<in> set S'\<close>
    using \<open>maximal S\<close> unfolding maximal_def consistent_def by fastforce
  then obtain S'' where \<open>set ((ps, i) # S'') = set S'\<close> \<open>(ps, i) \<notin> set S''\<close>
    using split_list[where x=\<open>(ps, i)\<close>] by metis
  then have \<open>\<turnstile> (ps, i) # S''\<close>
    using STB_struct inf \<open>\<turnstile> S'\<close> by blast
  then have \<open>\<turnstile> (p # ps, i) # S''\<close>
    using inf STB_struct_block[where ts'=\<open>p # ps\<close>] by auto
  moreover have \<open>set ((p # ps, i) # S'') \<subseteq> S\<close>
    using \<open>(p # ps, i) \<in> S\<close> \<open>(ps, i) \<notin> set S''\<close> \<open>set ((ps, i) # S'') = set S'\<close>
      \<open>set S' \<subseteq> {(ps, i)} \<union> S\<close> by auto
  ultimately show False
    using \<open>maximal S\<close> unfolding maximal_def consistent_def by blast
qed

lemma extend_not_mem: \<open>f n \<notin> extend S f (Suc n) \<Longrightarrow> \<not> consistent ({f n} \<union> extend S f n)\<close>
  by (metis Un_insert_left extend.simps(2) insertI1)

lemma maximal_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent S\<close> \<open>finite S\<close> \<open>surj f\<close>
  shows \<open>maximal (Extend S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal (Extend S f)\<close>
  then obtain block where \<open>block \<notin> Extend S f\<close> \<open>consistent ({block} \<union> Extend S f)\<close>
    unfolding maximal_def using assms consistent_Extend by blast
  obtain n where n: \<open>f n = block\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>block \<notin> extend S f (Suc n)\<close>
    using \<open>block \<notin> Extend S f\<close> extend_chain unfolding Extend_def by blast
  then have \<open>\<not> consistent ({block} \<union> extend S f n)\<close>
    using n extend_not_mem by blast
  moreover have \<open>block \<notin> extend S f n\<close>
    using \<open>block \<notin> extend S f (Suc n)\<close> extend_chain by auto
  then have \<open>{block} \<union> extend S f n \<subseteq> {block} \<union> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent ({block} \<union> Extend S f)\<close>
    using inconsistent_weaken by blast
  then show False
    using \<open>consistent ({block} \<union> Extend S f)\<close> by blast
qed

subsubsection \<open>Saturation\<close>

definition saturated :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>saturated S \<equiv> \<forall>(ps, i) \<in> S.
    \<forall>p. (\<^bold>\<diamond> p) on (ps, i) \<longrightarrow> (\<nexists>a. p = Nom a) \<longrightarrow> (\<exists>j.
      (\<exists>qs. (qs, i) \<in> S \<and> (\<^bold>@ j p) on (qs, i)) \<and>
      (\<exists>rs. (rs, i) \<in> S \<and> (\<^bold>\<diamond> Nom j) on (rs, i)))\<close>

lemma ballI' [intro!]: \<open>(\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x, y) \<in> A. P x y\<close>
  by blast

lemma witness_list_append:
  \<open>\<exists>extra. witness_list (ps @ qs) used = witness_list ps used @ witness_list qs (extra \<union> used)\<close>
proof (induct ps arbitrary: used)
  case Nil
  then show ?case
    by (metis Un_absorb append_self_conv2 witness_list.simps(1))
next
  case (Cons p ps)
  then show ?case
  proof (induct \<open>\<exists>q. proper_dia p = Some q\<close>)
    case True
    let ?i = \<open>SOME i. i \<notin> used\<close>
    from True obtain q where q: \<open>proper_dia p = Some q\<close>
      by blast
    moreover have \<open>(p # ps) @ qs = p # (ps @ qs)\<close>
      by simp
    ultimately have \<open>witness_list ((p # ps) @ qs) used = (\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) #
        witness_list (ps @ qs) ({?i} \<union> used)\<close>
      using witness_list by metis
    then have \<open>\<exists>extra. witness_list ((p # ps) @ qs) used = (\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) #
        witness_list ps ({?i} \<union> used) @ witness_list qs (extra \<union> ({?i} \<union> used))\<close>
      using True by metis
    moreover have \<open>(\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # witness_list ps ({?i} \<union> used) =
        witness_list (p # ps) used\<close>
      using q witness_list by metis
    ultimately have \<open>\<exists>extra. witness_list ((p # ps) @ qs) used =
        witness_list (p # ps) used @ witness_list qs (extra \<union> ({?i} \<union> used))\<close>
      by (metis append_Cons)
    then have \<open>\<exists>extra. witness_list ((p # ps) @ qs) used =
        witness_list (p # ps) used @ witness_list qs (({?i} \<union> extra) \<union> used)\<close>
      by simp
    then show ?case
      by blast
  next
    case False
    then show ?case
      by simp
  qed
qed

lemma ex_witness_list:
  assumes \<open>p \<in> set ps\<close> \<open>proper_dia p = Some q\<close>
  shows \<open>\<exists>i. {\<^bold>@ i q, \<^bold>\<diamond> Nom i} \<subseteq> set (witness_list ps used)\<close>
  using \<open>p \<in> set ps\<close>
proof (induct ps arbitrary: used)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ps)
  then show ?case
  proof (induct \<open>a = p\<close>)
    case True
    then have \<open>\<exists>i. witness_list (a # ps) used = (\<^bold>@ i q) # (\<^bold>\<diamond> Nom i) #
        witness_list ps ({i} \<union> used)\<close>
      using \<open>proper_dia p = Some q\<close> witness_list by metis
    then show ?case
      by auto
  next
    case False
    then have \<open>\<exists>i. {\<^bold>@ i q, \<^bold>\<diamond> Nom i} \<subseteq> set (witness_list ps (extra \<union> used))\<close> for extra
      by simp
    moreover have \<open>\<exists>extra. witness_list (a # ps) used =
        witness_list [a] used @ witness_list ps (extra \<union> used)\<close>
      using witness_list_append[where ps=\<open>[a]\<close>] by simp
    ultimately show ?case
      by fastforce
  qed
qed

lemma ex_witness:
  assumes \<open>p on block\<close> \<open>proper_dia p = Some q\<close>
  shows \<open>\<exists>i. (\<^bold>@ i q) on witness block used \<and> (\<^bold>\<diamond> Nom i) on witness block used\<close>
  using assms ex_witness_list by (induct block) auto

lemma saturated_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent S\<close> \<open>finite S\<close> \<open>surj f\<close>
  shows \<open>saturated (Extend S f)\<close>
  unfolding saturated_def
proof (intro ballI' allI impI)
  fix ps i p
  assume \<open>(ps, i) \<in> Extend S f\<close> \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> \<open>\<nexists>a. p = Nom a\<close>
  obtain n where n: \<open>f n = (ps, i)\<close>
    using \<open>surj f\<close> unfolding surj_def by metis

  let ?used = \<open>(\<Union>block \<in> {f n} \<union> extend S f n. block_nominals block)\<close>

  have \<open>extend S f n \<subseteq> Extend S f\<close>
    unfolding Extend_def by auto
  moreover have \<open>consistent (Extend S f)\<close>
    using assms consistent_Extend by blast
  ultimately have \<open>consistent ({(ps, i)} \<union> extend S f n)\<close>
    using \<open>(ps, i) \<in> Extend S f\<close> inconsistent_weaken by blast
  then have \<open>extend S f (Suc n) = {f n, witness (f n) ?used} \<union> extend S f n\<close>
    using n \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> by auto
  then have \<open>witness (f n) ?used \<in> Extend S f\<close>
    unfolding Extend_def by blast
  then have *: \<open>(witness_list ps ?used, i) \<in> Extend S f\<close>
    using n by simp

  have \<open>(\<^bold>\<diamond> p) \<in> set ps\<close>
    using \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> by simp
  moreover have \<open>proper_dia (\<^bold>\<diamond> p) = Some p\<close>
    using \<open>\<nexists>a. p = Nom a\<close> by simp
  ultimately have
    \<open>\<exists>j. (\<^bold>@ j p) on (witness_list ps ?used, i) \<and> (\<^bold>\<diamond> Nom j) on (witness_list ps ?used, i)\<close>
    using ex_witness_list by fastforce
  then show
    \<open>\<exists>j. (\<exists>qs. (qs, i) \<in> Extend S f \<and> (\<^bold>@ j p) on (qs, i)) \<and>
         (\<exists>rs. (rs, i) \<in> Extend S f \<and> (\<^bold>\<diamond> Nom j) on (rs, i))\<close>
    using * by blast
qed

subsection \<open>Smullyan-Fitting\<close>

lemma hintikka_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>maximal S\<close> \<open>consistent S\<close> \<open>saturated S\<close>
  shows \<open>hintikka S\<close>
  unfolding hintikka_def
proof safe
  fix x i j ps qs rs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>Nom j on (ps, i)\<close> and
    qs: \<open>(qs, j) \<in> S\<close> \<open>Pro x on (qs, j)\<close> and
    rs: \<open>(rs, i) \<in> S\<close> \<open>(\<^bold>\<not> Pro x) on (rs, i)\<close>
  then have \<open>\<not> \<turnstile> [(ps, i), (qs, j), (rs, i)]\<close>
    using \<open>consistent S\<close> unfolding consistent_def by simp
  moreover have \<open>\<turnstile> [(Pro x # ps, i), (qs, j), (rs, i)]\<close>
    using ps rs STB.Close[where p=\<open>Pro x\<close> and ps=\<open>Pro x # ps\<close> and i=i and qs=rs] by simp
  then have \<open>\<turnstile> [(ps, i), (qs, j), (rs, i)]\<close>
    using ps qs STB.Nom[where p=\<open>Pro x\<close> and ps=\<open>ps\<close> and qs=qs and i=j and b=j] by simp
  ultimately show False
    by blast
next
  fix a i ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>Nom a on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>(\<^bold>\<not> Nom a) on (qs, i)\<close>
  then have \<open>\<not> \<turnstile> [(ps, i), (qs, i)]\<close>
    using \<open>consistent S\<close> unfolding consistent_def by simp
  moreover have \<open>\<turnstile> [(ps, i), (qs, i)]\<close>
    using ps qs STB.Close[where p=\<open>Nom a\<close> and ps=ps and qs=qs and i=i] by simp
  ultimately show False
    by blast
next
  fix i j ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>(\<^bold>\<not> (\<^bold>\<diamond> Nom j)) on (qs, i)\<close>
  then have \<open>\<not> \<turnstile> [(ps, i), (qs, i)]\<close>
    using \<open>consistent S\<close> unfolding consistent_def by simp
  moreover have \<open>\<turnstile> [(ps, i), (qs, i)]\<close>
    using ps qs STB.Close[where p=\<open>\<^bold>\<diamond> Nom j\<close> and ps=ps and qs=qs and i=i] by simp
  ultimately show False
    by blast
next
  fix p i ps a
  assume i: \<open>i \<in> nominals p\<close> and ps: \<open>(ps, a) \<in> S\<close> \<open>p on (ps, a)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([], i)} \<union> S\<close> and \<open>([], i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def by blast
    then obtain S'' where S'': \<open>set (([], i) # S'') = set S'\<close> \<open>([], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([], i)\<close>] by blast
    moreover have \<open>set (([], i) # S'') \<subseteq> set (([], i) # (ps, a) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([], i) # (ps, a) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    moreover have \<open>i \<in> branch_nominals ((ps, a) # S'')\<close>
      using i ps unfolding branch_nominals_def by auto
    ultimately have \<open>\<turnstile> (ps, a) # S''\<close>
      using STB.GoTo[where i=i] by blast
    moreover have \<open>set ((ps, a) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>Nom j on (ps, i)\<close>
  show \<open>\<exists>qs. (qs, j) \<in> S \<and> Nom i on (qs, j)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, j) \<in> S \<and> Nom i on (qs, j)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([Nom i], j)} \<union> S\<close> and \<open>([Nom i], j) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set (([Nom i], j) # S'') = set S'\<close> \<open>([Nom i], j) \<notin> set S''\<close>
      using split_list[where x=\<open>([Nom i], j)\<close>] by blast
    moreover have \<open>set (([Nom i], j) # S'') \<subseteq> set (([Nom i], j) # (ps, i) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([Nom i], j) # (ps, i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], j) # (ps, i) # S''\<close>
      using \<open>Nom j on (ps, i)\<close> STB.Nom[where p=\<open>Nom i\<close> and i=j and a=j and b=i and qs=ps] by simp
    moreover have \<open>j \<in> branch_nominals ((ps, i) # S'')\<close>
      using \<open>Nom j on (ps, i)\<close> unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, i) # S''\<close>
      using STB.GoTo[where i=j] by blast
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j k ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>Nom j on (ps, i)\<close> and
    qs: \<open>(qs, j) \<in> S\<close> \<open>Nom k on (qs, j)\<close>
  show \<open>\<exists>rs. (rs, i) \<in> S \<and> Nom k on (rs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>rs. (rs, i) \<in> S \<and> Nom k on (rs, i)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([Nom k], i)} \<union> S\<close> and \<open>([Nom k], i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set (([Nom k], i) # S'') = set S'\<close> \<open>([Nom k], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([Nom k], i)\<close>] by blast
    moreover have \<open>set (([Nom k], i) # S'') \<subseteq> set (([Nom k], i) # (Nom k # ps, i) # (qs, j) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([Nom k], i) # (Nom k # ps, i) # (qs, j) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], i) # (Nom k # ps, i) # (qs, j) # S''\<close>
      using STB.Nom[where p=\<open>Nom k\<close> and i=i and b=i and qs=\<open>Nom k # ps\<close>] by simp
    moreover have \<open>i \<in> branch_nominals ((Nom k # ps, i) # (qs, j) # S'')\<close>
      unfolding branch_nominals_def by simp
    ultimately have \<open>\<turnstile> (Nom k # ps, i) # (qs, j) # S''\<close>
      using STB.GoTo[where i=i] by blast
    then have \<open>\<turnstile> (ps, i) # (qs, j) # S''\<close>
      using ps qs STB.Nom[where p=\<open>Nom k\<close> and i=j and a=i and b=j and ps=ps and qs=qs] by simp
    moreover have \<open>set ((ps, i) # (qs, j) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j k ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (ps, i)\<close> and
    qs: \<open>(qs, j) \<in> S\<close> \<open>Nom k on (qs, j)\<close>
  show \<open>\<exists>rs. (rs, i) \<in> S \<and> (\<^bold>\<diamond> Nom k) on (rs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>rs. (rs, i) \<in> S \<and> (\<^bold>\<diamond> Nom k) on (rs, i)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<diamond> Nom k], i)} \<union> S\<close> and \<open>([\<^bold>\<diamond> Nom k], i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set (([\<^bold>\<diamond> Nom k], i) # S'') = set S'\<close> \<open>([\<^bold>\<diamond> Nom k], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<diamond> Nom k], i)\<close>] by blast
    moreover have \<open>set (([\<^bold>\<diamond> Nom k], i) # S'') \<subseteq> set (([\<^bold>\<diamond> Nom k], i) # (ps, i) # (qs, j) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([\<^bold>\<diamond> Nom k], i) # (ps, i) # (qs, j) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], i) # (ps, i) # (qs, j) # S''\<close>
      using ps qs STB.Bridge[where k=k and rs=qs and j=j and ps=\<open>[]\<close> and a=i and qs=ps] by simp
    moreover have \<open>i \<in> branch_nominals ((ps, i) # (qs, j) # S'')\<close>
      using ps unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, i) # (qs, j) # S''\<close>
      using STB.GoTo[where i=i] by blast
    moreover have \<open>set ((ps, i) # (qs, j) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j k ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>Nom k on (qs, i)\<close>
  show \<open>\<exists>rs. (rs, k) \<in> S \<and> (\<^bold>\<diamond> Nom j) on (rs, k)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>rs. (rs, k) \<in> S \<and> (\<^bold>\<diamond> Nom j) on (rs, k)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<diamond> Nom j], k)} \<union> S\<close> and \<open>([\<^bold>\<diamond> Nom j], k) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set (([\<^bold>\<diamond> Nom j], k) # S'') = set S'\<close> \<open>([\<^bold>\<diamond> Nom j], k) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<diamond> Nom j], k)\<close>] by blast
    moreover have \<open>set (([\<^bold>\<diamond> Nom j], k) # S'') \<subseteq>
        set (([\<^bold>\<diamond> Nom j], k) # (Nom k # ps, i) # (qs, i) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([\<^bold>\<diamond> Nom j], k) # (Nom k # ps, i) # (qs, i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], k) # (Nom k # ps, i) # (qs, i) # S''\<close>
      using ps STB.Nom[where p=\<open>\<^bold>\<diamond> Nom j\<close> and i=k and a=k and b=i and ps=\<open>[]\<close> and qs=\<open>Nom k # ps\<close>]
      by simp
    moreover have \<open>k \<in> branch_nominals ((Nom k # ps, i) # (qs, i) # S'')\<close>
      unfolding branch_nominals_def by simp
    ultimately have \<open>\<turnstile> (Nom k # ps, i) # (qs, i) # S''\<close>
      using STB.GoTo[where i=k] by blast
    then have \<open>\<turnstile> (ps, i) # (qs, i) # S''\<close>
      using ps qs STB.Nom[where p=\<open>Nom k\<close> and i=i and a=i and b=i and ps=ps and qs=qs] by simp
    moreover have \<open>set ((ps, i) # (qs, i) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p q i ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>(p \<^bold>\<or> q) on (ps, i)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> (p on (qs, i) \<or> q on (qs, i))\<close>
  proof (rule ccontr)
    assume *: \<open>\<nexists>qs. (qs, i) \<in> S \<and> (p on (qs, i) \<or> q on (qs, i))\<close>
    then obtain Sp' where
      \<open>\<turnstile> Sp'\<close> and Sp': \<open>set Sp' \<subseteq> {(p # ps, i)} \<union> S\<close> and \<open>(p # ps, i) \<in> set Sp'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain Sp'' where Sp'': \<open>set ((p # ps, i) # Sp'') = set Sp'\<close> \<open>(p # ps, i) \<notin> set Sp''\<close>
      using split_list[where x=\<open>(p # ps, i)\<close>] by blast
    then have \<open>\<turnstile> (p # ps, i) # Sp''\<close>
      using \<open>\<turnstile> Sp'\<close> inf STB_struct by blast

    obtain Sq' where
      \<open>\<turnstile> Sq'\<close> and Sq': \<open>set Sq' \<subseteq> {(q # ps, i)} \<union> S\<close> and \<open>(q # ps, i) \<in> set Sq'\<close>
      using * \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain Sq'' where Sq'': \<open>set ((q # ps, i) # Sq'') = set Sq'\<close> \<open>(q # ps, i) \<notin> set Sq''\<close>
      using split_list[where x=\<open>(q # ps, i)\<close>] by blast
    then have \<open>\<turnstile> (q # ps, i) # Sq''\<close>
      using \<open>\<turnstile> Sq'\<close> inf STB_struct by blast

    obtain S'' where S'': \<open>set S'' = set Sp'' \<union> set Sq''\<close>
      by (meson set_union)
    then have
      \<open>set ((p # ps, i) # Sp'') \<subseteq> set ((p # ps, i) # S'')\<close>
      \<open>set ((q # ps, i) # Sq'') \<subseteq> set ((q # ps, i) # S'')\<close>
      by auto
    then have \<open>\<turnstile> (p # ps, i) # S''\<close> \<open>\<turnstile> (q # ps, i) # S''\<close>
      using \<open>\<turnstile> (p # ps, i) # Sp''\<close> \<open>\<turnstile> (q # ps, i) # Sq''\<close> inf STB_struct by blast+
    then have \<open>\<turnstile> (ps, i) # S''\<close>
      using ps STB.DisP[where p=p and q=q and ps=ps and qs=ps and a=i] by simp
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using ps Sp' Sp'' Sq' Sq'' S'' by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p q i ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) on (ps, i)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> p) on (qs, i) \<and> (\<^bold>\<not> q) on (qs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> p) on (qs, i) \<and> (\<^bold>\<not> q) on (qs, i)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and
      S': \<open>set S' \<subseteq> {((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i)} \<union> S\<close> and
      \<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis (mono_tags, lifting) insert_is_Un insert_subset list.simps(15) on.simps
          set_subset_Cons subset_insert)
    then obtain S'' where S'':
      \<open>set (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) # S'') = set S'\<close>
      \<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) \<notin> set S''\<close>
      using split_list[where x=\<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i)\<close>] by blast
    then have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> (ps, i) # S''\<close>
      using ps STB.DisN[where p=p and q=q and ps=ps and qs=ps] by simp
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<not> \<^bold>\<not> p) on (ps, i)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {(p # ps, i)} \<union> S\<close> and \<open>(p # ps, i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set ((p # ps, i) # S'') = set S'\<close> \<open>(p # ps, i) \<notin> set S''\<close>
      using split_list[where x=\<open>(p # ps, i)\<close>] by blast
    then have \<open>\<turnstile> (p # ps, i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> (ps, i) # S''\<close>
      using ps STB.Neg[where p=p and ps=ps and qs=ps] by simp
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps a
  assume ps: \<open>(ps, a) \<in> S\<close> \<open>(\<^bold>@ i p) on (ps, a)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([p], i)} \<union> S\<close> and \<open>([p], i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set (([p], i) # S'') = set S'\<close> \<open>([p], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([p], i)\<close>] by blast
    then have \<open>\<turnstile> ([p], i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    moreover have \<open>set (([p], i) # S'') \<subseteq> set (([p], i) # (ps, a) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([p], i) # (ps, a) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], i) # (ps, a) # S''\<close>
      using ps STB.SatP[where i=i and p=p and ps=\<open>[]\<close> and a=i and rs=ps and b=a and qs=\<open>[]\<close>] by simp
    moreover have \<open>i \<in> branch_nominals ((ps, a) # S'')\<close>
      using ps unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, a) # S''\<close>
      using STB.GoTo[where i=i] by blast
    moreover have \<open>set ((ps, a) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps a
  assume ps: \<open>(ps, a) \<in> S\<close> \<open>(\<^bold>\<not> (\<^bold>@ i p)) on (ps, a)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> p) on (qs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> p) on (qs, i)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<not> p], i)} \<union> S\<close> and \<open>([\<^bold>\<not> p], i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set (([\<^bold>\<not> p], i) # S'') = set S'\<close> \<open>([\<^bold>\<not> p], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<not> p], i)\<close>] by blast
    then have \<open>\<turnstile> ([\<^bold>\<not> p], i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    moreover have \<open>set (([\<^bold>\<not> p], i) # S'') \<subseteq> set (([\<^bold>\<not> p], i) # (ps, a) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([\<^bold>\<not> p], i) # (ps, a) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], i) # (ps, a) # S''\<close>
      using ps STB.SatN[where i=i and p=p and ps=\<open>[]\<close> and a=i and rs=ps and b=a and qs=\<open>[]\<close>] by simp
    moreover have \<open>i \<in> branch_nominals ((ps, a) # S'')\<close>
      using ps unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, a) # S''\<close>
      using STB.GoTo[where i=i] by blast
    moreover have \<open>set ((ps, a) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps
  assume
    \<open>\<nexists>a. p = Nom a\<close> and
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> p) on (ps, i)\<close>
  then show \<open>\<exists>j.
      (\<exists>qs. (qs, i) \<in> S \<and> (\<^bold>\<diamond> Nom j) on (qs, i)) \<and>
      (\<exists>rs. (rs, i) \<in> S \<and> (\<^bold>@ j p) on (rs, i))\<close>
    using \<open>saturated S\<close> unfolding saturated_def by blast
next
  fix p i j ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (qs, i)\<close>
  show \<open>\<exists>rs. (rs, i) \<in> S \<and> (\<^bold>\<not> (\<^bold>@ j p)) on (rs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> (\<^bold>@ j p)) on (qs, i)\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<not> (\<^bold>@ j p)], i)} \<union> S\<close> and \<open>([\<^bold>\<not> (\<^bold>@ j p)], i) \<in> set S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'': \<open>set (([\<^bold>\<not> (\<^bold>@ j p)], i) # S'') = set S'\<close> \<open>([\<^bold>\<not> (\<^bold>@ j p)], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<not> (\<^bold>@ j p)], i)\<close>] by blast
    then have \<open>\<turnstile> ([\<^bold>\<not> (\<^bold>@ j p)], i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    moreover have \<open>set (([\<^bold>\<not> (\<^bold>@ j p)], i) # S'') \<subseteq>
        set (([\<^bold>\<not> (\<^bold>@ j p)], i) # (ps, i) # (qs, i) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([\<^bold>\<not> (\<^bold>@ j p)], i) # (ps, i) # (qs, i) # S''\<close>
      using inf STB_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], i) # (ps, i) # (qs, i) # S''\<close>
      using ps qs STB.DiaN[where i=j and rs=qs and a=i and p=p and ps=\<open>[]\<close> and qs=ps] by simp
    moreover have \<open>i \<in> branch_nominals ((ps, i) # (qs, i) # S'')\<close>
      unfolding branch_nominals_def by simp
    ultimately have \<open>\<turnstile> (ps, i) # (qs, i) # S''\<close>
      using STB.GoTo[where i=i] by blast
    moreover have \<open>set ((ps, i) # (qs, i) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
qed

subsection \<open>Result\<close>

theorem completeness:
  fixes p :: \<open>('a :: countable, 'b :: countable) fm\<close>
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    valid: \<open>\<forall>(M :: ('b set, 'a) model) g w. M, g, w \<Turnstile> p\<close>
  shows \<open>\<turnstile> [([\<^bold>\<not> p], i)]\<close>
proof (rule ccontr)
  assume \<open>\<not> \<turnstile> [([\<^bold>\<not> p], i)]\<close>
  then have *: \<open>consistent {([\<^bold>\<not> p], i)}\<close>
    unfolding consistent_def using STB_struct inf by fastforce

  let ?S = \<open>Extend {([\<^bold>\<not> p], i)} from_nat\<close>

  have \<open>consistent ?S\<close>
    using consistent_Extend inf * by blast
  moreover have \<open>maximal ?S\<close>
    using maximal_Extend inf * by fastforce
  moreover have \<open>saturated ?S\<close>
    using saturated_Extend inf * by fastforce
  ultimately have \<open>hintikka ?S\<close>
    using hintikka_Extend inf by blast

  moreover have \<open>([\<^bold>\<not> p], i) \<in> ?S\<close>
    using Extend_mem by blast

  moreover have \<open>(\<^bold>\<not> p) on ([\<^bold>\<not> p], i)\<close>
    by simp

  ultimately have \<open>\<not> Model (reach ?S) (val ?S), assign ?S, assign ?S i \<Turnstile> p\<close>
    using hintikka_model by fast

  then show False
    using valid by blast
qed

abbreviation \<open>valid p \<equiv> \<forall>(M :: (nat set, nat) model) (g :: nat \<Rightarrow> _) w. M, g, w \<Turnstile> p\<close>

theorem main:
  assumes \<open>i \<notin> nominals p\<close>
  shows \<open>valid p \<longleftrightarrow> \<turnstile> [([\<^bold>\<not> p], i)]\<close>
proof
  assume \<open>valid p\<close>
  then show \<open>\<turnstile> [([\<^bold>\<not> p], i)]\<close>
    using completeness by blast
next
  assume \<open>\<turnstile> [([\<^bold>\<not> p], i)]\<close>
  then show \<open>valid p\<close>
    using assms soundness_fresh by fast
qed

theorem valid_semantics:
  \<open>valid p \<longrightarrow> M, g, w \<Turnstile> p\<close>
proof
  assume \<open>valid p\<close>
  then have \<open>i \<notin> nominals p \<Longrightarrow> \<turnstile> [([\<^bold>\<not> p], i)]\<close> for i
    using main by blast
  moreover have \<open>\<exists>i. i \<notin> nominals p\<close>
    by (simp add: finite_nominals ex_new_if_finite)
  ultimately show \<open>M, g, w \<Turnstile> p\<close>
    using soundness_fresh by fast
qed

end