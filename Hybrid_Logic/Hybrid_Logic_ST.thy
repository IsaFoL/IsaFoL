theory Hybrid_Logic_ST imports Main begin

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
  \<open>\<^bold>\<box> \<phi> \<equiv> \<^bold>\<not> (\<^bold>\<diamond> \<^bold>\<not> \<phi>)\<close>

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

inductive ST :: \<open>('a, 'b) branch \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [50] 50) where
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

lemma \<open>\<turnstile> [([\<^bold>\<not> (\<^bold>@ i (Nom i))], a)]\<close>
proof -
  let ?init = \<open>[\<^bold>\<not> (\<^bold>@ i (Nom i))]\<close>
  have \<open>\<turnstile> [([\<^bold>\<not> Nom i], i), (?init, a)]\<close>
    using ST.Close[where i=i and p=\<open>Nom i\<close> and ps=\<open>[\<^bold>\<not> Nom i]\<close> and qs=\<open>[\<^bold>\<not> Nom i]\<close>] by force
  then have \<open>\<turnstile> [([], i), (?init, a)]\<close>
    using ST.SatN[where i=i and a=i and b=a and p=\<open>Nom i\<close> and ps=\<open>[]\<close> and qs=\<open>[]\<close> and rs=\<open>?init\<close>]
    by force
  then show \<open>\<turnstile> [(?init, a)]\<close>
    using ST.GoTo[where i=i and branch=\<open>[(?init, a)]\<close>] unfolding branch_nominals_def by force
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
proof (induct branch arbitrary: g rule: ST.induct)
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
qed

lemma soundness: \<open>\<turnstile> branch \<Longrightarrow> \<exists>block \<in> set branch. \<exists>p on block. \<not> M, g, w \<Turnstile> p\<close>
  using soundness' by fast

corollary \<open>\<not> \<turnstile> []\<close>
  using soundness by fastforce

proposition \<open>\<not> \<turnstile> []\<close>
proof -
  have \<open>\<turnstile> branch \<Longrightarrow> branch = [] \<Longrightarrow> False\<close> for branch :: \<open>('a, 'b) branch\<close>
    by (induct branch rule: ST.induct) (auto simp: branch_nominals_def)
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

end
