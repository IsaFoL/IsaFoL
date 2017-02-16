section{* Terms and Literals *}

theory TermsAndLiterals imports Main "~~/src/HOL/Library/Countable_Set" begin

type_synonym var_sym  = string
type_synonym fun_sym  = string
type_synonym pred_sym = string

datatype fterm = 
  Fun fun_sym (get_sub_terms: "fterm list")
| Var var_sym

datatype hterm = HFun fun_sym "hterm list" -- {* Herbrand terms defined as in Berghofer's FOL-Fitting *}


type_synonym 't atom = "pred_sym * 't list"

datatype 't literal = 
  sign: Pos (get_pred: pred_sym) (get_terms: "'t list")
| Neg (get_pred: pred_sym) (get_terms: "'t list")

fun get_atom :: "'t literal \<Rightarrow> 't atom" where
  "get_atom (Pos p ts) = (p, ts)"
| "get_atom (Neg p ts) = (p, ts)"

subsection {* Ground *}

fun ground\<^sub>t :: "fterm \<Rightarrow> bool" where
  "ground\<^sub>t (Var x) \<longleftrightarrow> False"
| "ground\<^sub>t (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground\<^sub>t t)"

abbreviation ground\<^sub>t\<^sub>s :: "fterm list \<Rightarrow> bool" where
  "ground\<^sub>t\<^sub>s ts \<equiv> (\<forall>t \<in> set ts. ground\<^sub>t t)"

abbreviation ground\<^sub>l :: "fterm literal \<Rightarrow> bool" where
  "ground\<^sub>l l \<equiv> ground\<^sub>t\<^sub>s (get_terms l)"

abbreviation ground\<^sub>l\<^sub>s :: "fterm literal set \<Rightarrow> bool" where
  "ground\<^sub>l\<^sub>s C \<equiv> (\<forall>l \<in> C. ground\<^sub>l l)"


definition ground_fatoms :: "fterm atom set" where
  "ground_fatoms \<equiv> {a. ground\<^sub>t\<^sub>s (snd a)}"

lemma ground\<^sub>l_ground_fatom: "ground\<^sub>l l \<Longrightarrow> get_atom l \<in> ground_fatoms"
  unfolding ground_fatoms_def by (induction l) auto

subsection {* Auxiliary *}

lemma infinity:
  assumes inj: "\<forall>n :: nat. undiago (diago n) = n" 
  assumes all_tree: "\<forall>n :: nat. (diago n) \<in> S"
  shows "\<not>finite S"
proof -
  from inj all_tree have "\<forall>n. n = undiago (diago n) \<and> (diago n) \<in> S" by auto
  then have "\<forall>n. \<exists>ds. n = undiago ds \<and> ds \<in> S" by auto
  then have "undiago ` S = (UNIV :: nat set)" by auto
  then show "\<not>finite S" by (metis finite_imageI infinite_UNIV_nat) 
qed

lemma inv_into_f_f:
  assumes "bij_betw f A B"
  assumes "a\<in>A"
  shows "(inv_into A f) (f a) = a"
using assms bij_betw_inv_into_left by metis

lemma f_inv_into_f:
  assumes "bij_betw f A B"
  assumes "b\<in>B"
  shows "f ((inv_into A f) b) = b"
using assms bij_betw_inv_into_right by metis

subsection {* Conversions *}
subsubsection {* Convertions - Terms and Herbrand Terms *}

fun fterm_of_hterm :: "hterm \<Rightarrow> fterm" where
  "fterm_of_hterm (HFun p ts) = Fun p (map fterm_of_hterm ts)"

definition fterms_of_hterms :: "hterm list \<Rightarrow> fterm list" where
  "fterms_of_hterms ts \<equiv> map fterm_of_hterm ts"

fun hterm_of_fterm :: "fterm \<Rightarrow> hterm" where
  "hterm_of_fterm (Fun p ts) = HFun p (map hterm_of_fterm ts)"

definition hterms_of_fterms :: "fterm list \<Rightarrow> hterm list" where
"hterms_of_fterms ts \<equiv> map hterm_of_fterm ts"

lemma [simp]: "hterm_of_fterm (fterm_of_hterm t) = t" 
  by (induction t) (simp add: map_idI)

lemma [simp]: "hterms_of_fterms (fterms_of_hterms ts) = ts" 
  unfolding hterms_of_fterms_def fterms_of_hterms_def by (simp add: map_idI)

lemma [simp]: "ground\<^sub>t t \<Longrightarrow> fterm_of_hterm (hterm_of_fterm t) = t" 
  by (induction t) (auto simp add: map_idI)

lemma [simp]: "ground\<^sub>t\<^sub>s ts \<Longrightarrow> fterms_of_hterms (hterms_of_fterms ts) = ts" 
  unfolding fterms_of_hterms_def hterms_of_fterms_def by (simp add: map_idI)

lemma ground_fterm_of_hterm:  "ground\<^sub>t (fterm_of_hterm t)"
  by (induction t) (auto simp add: map_idI)

lemma ground_fterms_of_hterms: "ground\<^sub>t\<^sub>s (fterms_of_hterms ts)"
  unfolding fterms_of_hterms_def using ground_fterm_of_hterm by auto

subsubsection {* Conversions -  Literals and Herbrand Literals *}

fun flit_of_hlit :: "hterm literal \<Rightarrow> fterm literal" where
  "flit_of_hlit (Pos p ts) = Pos p (fterms_of_hterms ts)"
| "flit_of_hlit (Neg p ts) = Neg p (fterms_of_hterms ts)"

fun hlit_of_flit :: "fterm literal \<Rightarrow> hterm literal" where
  "hlit_of_flit (Pos p ts) = Pos p (hterms_of_fterms ts)"
| "hlit_of_flit (Neg p ts) = Neg p (hterms_of_fterms ts)"

lemma ground_flit_of_hlit: "ground\<^sub>l (flit_of_hlit l)" 
  by  (induction l)  (simp add: ground_fterms_of_hterms)+

theorem hlit_of_flit_flit_of_hlit [simp]: "hlit_of_flit (flit_of_hlit l) =  l" by (cases l) auto

theorem flit_of_hlit_hlit_of_flit [simp]: "ground\<^sub>l l \<Longrightarrow> flit_of_hlit (hlit_of_flit l) = l" by (cases l) auto

lemma sign_flit_of_hlit: "sign (flit_of_hlit l) = sign l" by (cases l) auto

lemma hlit_of_flit_bij: "bij_betw hlit_of_flit {l. ground\<^sub>l l} UNIV" 
 unfolding bij_betw_def
proof
  show "inj_on hlit_of_flit {l. ground\<^sub>l l}" using inj_on_inverseI flit_of_hlit_hlit_of_flit 
    by (metis (mono_tags, lifting) mem_Collect_eq) 
next 
  have "\<forall>l. \<exists>l'. ground\<^sub>l l' \<and> l = hlit_of_flit l'" 
    using ground_flit_of_hlit hlit_of_flit_flit_of_hlit by metis
  then show "hlit_of_flit ` {l. ground\<^sub>l l} = UNIV" by auto
qed

lemma flit_of_hlit_bij: "bij_betw flit_of_hlit UNIV {l. ground\<^sub>l l}" 
 unfolding bij_betw_def inj_on_def
proof
  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. flit_of_hlit x = flit_of_hlit y \<longrightarrow> x = y" 
    using ground_flit_of_hlit hlit_of_flit_flit_of_hlit by metis
next
  have "\<forall>l. ground\<^sub>l l \<longrightarrow> (l = flit_of_hlit (hlit_of_flit l))" using hlit_of_flit_flit_of_hlit by auto
  then have "{l. ground\<^sub>l l}  \<subseteq> flit_of_hlit ` UNIV " by blast
  moreover
  have "\<forall>l. ground\<^sub>l (flit_of_hlit l)" using ground_flit_of_hlit by auto
  ultimately show "flit_of_hlit ` UNIV = {l. ground\<^sub>l l}" using hlit_of_flit_flit_of_hlit ground_flit_of_hlit by auto
qed

subsubsection {* Convertions - Atoms and Herbrand Atoms *}

fun fatom_of_hatom :: "hterm atom \<Rightarrow> fterm atom" where
  "fatom_of_hatom (p, ts) = (p, fterms_of_hterms ts)"

fun hatom_of_fatom :: "fterm atom \<Rightarrow> hterm atom" where
  "hatom_of_fatom (p, ts) = (p, hterms_of_fterms ts)"

lemma ground_fatom_of_hatom: "ground\<^sub>t\<^sub>s (snd (fatom_of_hatom a))" 
  by  (induction a) (simp add: ground_fterms_of_hterms)+

theorem hatom_of_fatom_fatom_of_hatom [simp]: "hatom_of_fatom (fatom_of_hatom l) = l" by (cases l) auto

theorem fatom_of_hatom_hatom_of_fatom [simp]: "ground\<^sub>t\<^sub>s (snd l) \<Longrightarrow> fatom_of_hatom (hatom_of_fatom l) = l" by (cases l) auto

lemma hatom_of_fatom_bij: "bij_betw hatom_of_fatom ground_fatoms UNIV" 
 unfolding bij_betw_def
proof
  show "inj_on hatom_of_fatom ground_fatoms" using inj_on_inverseI fatom_of_hatom_hatom_of_fatom unfolding ground_fatoms_def 
    by (metis (mono_tags, lifting) mem_Collect_eq) 
next 
  have "\<forall>a. \<exists>a'. ground\<^sub>t\<^sub>s (snd a') \<and> a = hatom_of_fatom a'" 
    using ground_fatom_of_hatom hatom_of_fatom_fatom_of_hatom by metis
  then show "hatom_of_fatom ` ground_fatoms = UNIV" unfolding ground_fatoms_def by blast
qed

lemma fatom_of_hatom_bij: "bij_betw fatom_of_hatom UNIV ground_fatoms" 
 unfolding bij_betw_def inj_on_def
proof
  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. fatom_of_hatom x = fatom_of_hatom y \<longrightarrow> x = y" 
    using ground_fatom_of_hatom hatom_of_fatom_fatom_of_hatom by metis
next
  have "\<forall>a. ground\<^sub>t\<^sub>s (snd a) \<longrightarrow> (a = fatom_of_hatom (hatom_of_fatom a))" using hatom_of_fatom_fatom_of_hatom by auto
  then have "ground_fatoms  \<subseteq> fatom_of_hatom ` UNIV " unfolding ground_fatoms_def by blast
  moreover
  have "\<forall>l. ground\<^sub>t\<^sub>s (snd (fatom_of_hatom l))" using ground_fatom_of_hatom by auto
  ultimately show "fatom_of_hatom ` UNIV = ground_fatoms" 
    using hatom_of_fatom_fatom_of_hatom ground_fatom_of_hatom unfolding ground_fatoms_def by auto
qed


subsection {* Enumerations *}

subsubsection {* Enumerating Strings *}

definition nat_from_string:: "string \<Rightarrow> nat" where
  "nat_from_string \<equiv> (SOME f. bij f)"

definition string_from_nat:: "nat \<Rightarrow> string" where
  "string_from_nat \<equiv> inv nat_from_string"

lemma nat_from_string_bij: "bij nat_from_string"
  proof -
  have "countable (UNIV::string set)" by auto
  moreover
  have "infinite (UNIV::string set)" using infinite_UNIV_listI by auto
  ultimately
  obtain x where "bij (x:: string \<Rightarrow> nat)" using countableE_infinite[of UNIV] by blast
  then show "?thesis" unfolding nat_from_string_def using someI by metis
qed

lemma string_from_nat_bij: "bij string_from_nat" unfolding string_from_nat_def using nat_from_string_bij bij_betw_inv_into by auto

lemma nat_from_string_string_from_nat[simp]: "nat_from_string (string_from_nat n) = n" 
  unfolding string_from_nat_def 
  using nat_from_string_bij f_inv_into_f[of nat_from_string] by simp

lemma string_from_nat_nat_from_string[simp]: "string_from_nat (nat_from_string n) = n" 
  unfolding string_from_nat_def 
  using nat_from_string_bij inv_into_f_f[of nat_from_string] by simp

subsubsection {* Enumerating Herbrand Atoms *}

definition nat_from_hatom:: "hterm atom \<Rightarrow> nat" where
  "nat_from_hatom \<equiv> (SOME f. bij f)"

definition hatom_from_nat:: "nat \<Rightarrow> hterm atom" where
  "hatom_from_nat \<equiv> inv nat_from_hatom"

instantiation hterm :: countable begin
instance by countable_datatype
end

lemma infinite_hatoms: "infinite (UNIV :: (pred_sym * 't list) set)"
proof -
  let ?diago = "\<lambda>n. (string_from_nat n,[])"
  let ?undiago = "\<lambda>a. nat_from_string (fst a)"
  have "\<forall>n. ?undiago (?diago n) = n" using nat_from_string_string_from_nat by auto
  moreover
  have "\<forall>n. ?diago n \<in> UNIV" by auto
  ultimately show "infinite (UNIV :: (pred_sym * 't list) set)" using infinity[of ?undiago ?diago UNIV] by simp
qed

lemma nat_from_hatom_bij: "bij nat_from_hatom"
proof -
  let ?S = "UNIV :: (pred_sym * ('t::countable) list) set"
  have "countable ?S" by auto
  moreover
  have "infinite ?S" using infinite_hatoms by auto
  ultimately
  obtain x where "bij (x :: hterm atom \<Rightarrow> nat)" using countableE_infinite[of ?S] by blast
  then have "bij nat_from_hatom" unfolding nat_from_hatom_def using someI by metis
  then show "?thesis" unfolding bij_betw_def inj_on_def unfolding nat_from_hatom_def by simp
qed

lemma hatom_from_nat_bij: "bij hatom_from_nat " unfolding hatom_from_nat_def using nat_from_hatom_bij bij_betw_inv_into by auto

lemma nat_from_hatom_hatom_from_nat[simp]: "nat_from_hatom (hatom_from_nat n) = n" 
  unfolding hatom_from_nat_def 
  using nat_from_hatom_bij f_inv_into_f[of nat_from_hatom] by simp

lemma hatom_from_nat_nat_from_hatom[simp]: "hatom_from_nat (nat_from_hatom l) = l" 
  unfolding hatom_from_nat_def 
  using nat_from_hatom_bij inv_into_f_f[of nat_from_hatom _ UNIV] by simp


subsubsection {* Enumerating Ground Atoms *}

definition fatom_from_nat :: "nat \<Rightarrow> fterm atom" where
  "fatom_from_nat = (\<lambda>n. fatom_of_hatom (hatom_from_nat n))"

definition nat_from_fatom :: "fterm atom \<Rightarrow> nat" where
  "nat_from_fatom = (\<lambda>t. nat_from_hatom (hatom_of_fatom t))"

theorem diag_undiag_fatom[simp]: "ground\<^sub>t\<^sub>s ts \<Longrightarrow> fatom_from_nat (nat_from_fatom (p,ts)) = (p,ts)"
unfolding fatom_from_nat_def nat_from_fatom_def by auto

theorem undiag_diag_fatom[simp]: "nat_from_fatom (fatom_from_nat n) = n" unfolding fatom_from_nat_def nat_from_fatom_def by auto

lemma fatom_from_nat_bij: "bij_betw fatom_from_nat UNIV ground_fatoms" 
  using hatom_from_nat_bij bij_betw_trans fatom_of_hatom_bij hatom_from_nat_bij unfolding fatom_from_nat_def comp_def by blast


lemma ground_fatom_from_nat: "ground\<^sub>t\<^sub>s (snd (fatom_from_nat x))" unfolding fatom_from_nat_def using ground_fatom_of_hatom by auto

lemma nat_from_fatom_bij: "bij_betw nat_from_fatom ground_fatoms UNIV"
   using nat_from_hatom_bij bij_betw_trans hatom_of_fatom_bij hatom_from_nat_bij unfolding nat_from_fatom_def comp_def by blast

end
