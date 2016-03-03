theory TermsAndLiterals imports Main "~~/src/HOL/Library/Countable_Set" begin

section{* Terms and Literals *}

type_synonym var_sym  = string
type_synonym fun_sym  = string
type_synonym pred_sym = string

datatype fterm = 
  Fun fun_sym (get_sub_terms: "fterm list")
| Var var_sym

datatype hterm = HFun fun_sym "hterm list" (* Herbrand terms defined as in Berghofer's FOL-Fitting *)

datatype 't literal = 
  sign: Pos (get_pred: pred_sym) (get_terms: "'t list")
| Neg (get_pred: pred_sym) (get_terms: "'t list")

subsection {* Ground *}

fun ground :: "fterm \<Rightarrow> bool" where
  "ground (Var x) \<longleftrightarrow> False"
| "ground (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground t)"

abbreviation grounds :: "fterm list \<Rightarrow> bool" where
  "grounds ts \<equiv> (\<forall>t \<in> set ts. ground t)"

abbreviation groundl :: "fterm literal \<Rightarrow> bool" where
  "groundl l \<equiv> grounds (get_terms l)"

subsection {* Enumeration *}

lemma infinity:
  assumes inj: "\<forall>n :: nat. undiago (diago n) = n" 
  assumes all_tree: "\<forall>n :: nat. (diago n) \<in> S"
  shows "\<not>finite S"
proof -
  from inj all_tree have "\<forall>n. n = undiago (diago n) \<and> (diago n) \<in> S" by auto
  then have "\<forall>n. \<exists>ds. n = undiago ds \<and> ds \<in> S" by auto
  then have "undiago ` S = (UNIV :: nat set)" by auto
  then have "\<not>finite S"by (metis finite_imageI infinite_UNIV_nat) 
  then show ?thesis by auto
qed

lemma bij_betw_inv_into_f_f_inv_into:
  assumes "bij_betw f A B"
  shows "(\<forall>a\<in>A. (inv_into A f) (f a) = a) \<and> (\<forall>b\<in>B. f ((inv_into A f) b) = b)"
proof
  from assms have "inj_on f A" unfolding bij_betw_def by auto
  then show "\<forall>a\<in>A. inv_into A f (f a) = a" using inv_into_f_f by auto
next
  from assms have "f ` A = B" unfolding bij_betw_def by auto
  then show "\<forall>b\<in>B. f ((inv_into A f) b) = b" using f_inv_into_f by metis
qed

subsubsection {* Enumerating strings *}

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
  using nat_from_string_bij bij_betw_inv_into_f_f_inv_into[of nat_from_string] by simp

lemma string_from_nat_nat_from_string[simp]: "string_from_nat (nat_from_string n) = n" 
  unfolding string_from_nat_def 
  using nat_from_string_bij bij_betw_inv_into_f_f_inv_into[of nat_from_string] by simp

subsubsection {* Enumerating hatoms *}

abbreviation hatoms :: "hterm literal set" where
  "hatoms \<equiv> {l :: hterm literal. sign l = True}"

definition nat_from_hatom':: "hterm literal \<Rightarrow> nat" where
  "nat_from_hatom' \<equiv> (SOME f. bij_betw f hatoms UNIV)"

definition nat_from_hatom:: "hterm literal \<Rightarrow> nat" where
  "nat_from_hatom \<equiv> \<lambda>l. if sign l = True then nat_from_hatom' l else nat_from_hatom' (case l of Neg p ts \<Rightarrow> Pos p ts)"

(* FOR negative literals it should give the number of the corresponding positive literal *)

definition hatom_from_nat:: "nat \<Rightarrow> hterm literal" where
  "hatom_from_nat \<equiv> inv_into hatoms nat_from_hatom"

instantiation hterm :: countable begin
instance by countable_datatype
end

instantiation literal :: (countable) countable begin
instance by countable_datatype
end

lemma infinite_hatoms: "infinite hatoms"
proof -
  let ?S = "{l :: hterm literal. sign l = True}"
  let ?diago = "\<lambda>n. Pos (string_from_nat n) []"
  let ?undiago = "\<lambda>l. nat_from_string (get_pred l)"
  thm infinity
  have "\<forall>n. ?undiago (?diago n) = n" using nat_from_string_string_from_nat by auto
  moreover
  have "\<forall>n. ?diago n \<in> ?S" by auto
  ultimately show "infinite ?S" using infinity[of ?undiago ?diago ?S] by auto
qed

lemma nat_from_hatom_bij: "bij_betw nat_from_hatom hatoms UNIV"
proof -
  have "countable hatoms" by auto
  moreover
  have "infinite hatoms" using infinite_hatoms by auto
  ultimately
  obtain x where "bij_betw (x:: hterm literal \<Rightarrow> nat) hatoms UNIV" using Countable_Set.countableE_infinite[of hatoms] by blast
  then have "bij_betw nat_from_hatom' hatoms UNIV" unfolding nat_from_hatom'_def using someI by metis
  then show "?thesis" unfolding bij_betw_def inj_on_def unfolding nat_from_hatom_def by simp
qed

lemma hatom_from_nat_bij: "bij_betw hatom_from_nat UNIV hatoms " unfolding hatom_from_nat_def using nat_from_hatom_bij bij_betw_inv_into by auto

lemma nat_from_hatom_hatom_from_nat[simp]: "nat_from_hatom (hatom_from_nat n) = n" 
  unfolding hatom_from_nat_def 
  using nat_from_hatom_bij bij_betw_inv_into_f_f_inv_into[of nat_from_hatom] by simp

lemma hatom_from_nat_nat_from_hatom[simp]: "\<forall>l \<in> hatoms. hatom_from_nat (nat_from_hatom l) = l" 
  unfolding hatom_from_nat_def 
  using nat_from_hatom_bij bij_betw_inv_into_f_f_inv_into[of nat_from_hatom hatoms UNIV] by simp

lemma undiag_neg2: "nat_from_hatom (Neg P ts) = nat_from_hatom (Pos P ts)" unfolding nat_from_hatom_def by auto

lemma nat_from_hatom_inj_mod_sign:
  assumes "nat_from_hatom l1 = nat_from_hatom l2"
  shows "get_pred l1 = get_pred l2 \<and> get_terms l1 = get_terms l2"
proof -
  {
    fix l1 fix p1 fix ts1
    fix l2 fix p2 fix ts2
    assume asm: "l1 = Pos p1 ts1 \<and> l2 = Pos p2 ts2 \<and> nat_from_hatom l1 = nat_from_hatom l2"
    moreover
    then have "sign l1 = True \<and> sign l2 = True" by auto
    ultimately
    have "l1 = l2" using nat_from_hatom_bij unfolding bij_betw_def inj_on_def by blast
    then have "get_pred l1 = get_pred l2 \<and> get_terms l1 = get_terms l2" by auto
  }
  then show ?thesis 
    apply (cases l1)
    apply (cases l2)
    prefer 3
    apply (cases l2)
    using assms undiag_neg2 apply auto
    done
qed


(* This lemma is already expressed by hatom_from_nat_bij *)
lemma hatom_from_nat_Pos:
  assumes "hatom_from_nat n = l"
  shows "\<exists>p ts. l = Pos p ts"
proof -
  from assms have "l \<in> hatoms" using hatom_from_nat_bij unfolding bij_betw_def by auto
  then have "sign l = True" by auto
  then obtain p ts where "l = Pos p ts" by (cases l) auto
  then show ?thesis by auto
qed

(* This lemma is already expressed by hatom_from_nat_bij *)
lemma sign_hatom_from_nat: "sign (hatom_from_nat n) = True" using hatom_from_nat_bij unfolding bij_betw_def by auto

subsubsection {* Convertions terms and Herbrand term *}

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

lemma [simp]:  "hterms_of_fterms (fterms_of_hterms ts) = ts" 
  unfolding hterms_of_fterms_def fterms_of_hterms_def by (simp add: map_idI)

lemma [simp]: "ground t \<Longrightarrow> fterm_of_hterm (hterm_of_fterm t) = t" 
  by (induction t) (auto simp add: map_idI)

lemma [simp]: "grounds ts \<Longrightarrow>fterms_of_hterms (hterms_of_fterms ts) = ts" 
  unfolding fterms_of_hterms_def hterms_of_fterms_def by (simp add: map_idI)

lemma ground_fterm_of_hterm:  "ground (fterm_of_hterm t)"
  by (induction t) (auto simp add: map_idI)

lemma ground_fterms_of_hterms: "grounds (fterms_of_hterms ts)"
  unfolding fterms_of_hterms_def using ground_fterm_of_hterm by auto

subsubsection {* Converstions literals and herbrand literals *}

fun fatom_of_hatom :: "hterm literal \<Rightarrow> fterm literal" where
  "fatom_of_hatom (Pos p ts) = Pos p (fterms_of_hterms ts)"
| "fatom_of_hatom (Neg p ts) = Neg p (fterms_of_hterms ts)"

fun hatom_of_fatom :: "fterm literal \<Rightarrow> hterm literal" where
  "hatom_of_fatom (Pos p ts) = Pos p (hterms_of_fterms ts)"
| "hatom_of_fatom (Neg p ts) = Neg p (hterms_of_fterms ts)"

lemma ground_fatom_of_hatom: "groundl (fatom_of_hatom l)" 
  by  (induction l)  (simp add: ground_fterms_of_hterms)+

theorem hatom_of_fatom_fatom_of_hatom [simp]: "hatom_of_fatom (fatom_of_hatom l) =  l" by (cases l) auto

theorem fatom_of_hatom_hatom_of_fatom [simp]: "groundl l \<Longrightarrow> fatom_of_hatom (hatom_of_fatom l) = l" by (cases l) auto

lemma sign_fatom_of_hatom: "sign (fatom_of_hatom l) = sign l" by (cases l) auto

lemma hatom_of_fatom_bij: "bij_betw hatom_of_fatom {l. groundl l} UNIV"
proof -
  have "inj_on hatom_of_fatom {l. groundl l}"  unfolding inj_on_def 
    proof (rule+)
      fix x y
      assume grx: "x \<in> {l. groundl l}"
      then have "groundl x" by auto
      assume "y \<in> {l. groundl l}"
      then have gry: "groundl y" by auto
      assume "hatom_of_fatom x = hatom_of_fatom y"
      then have "fatom_of_hatom (hatom_of_fatom x) = fatom_of_hatom (hatom_of_fatom y)" by auto
      then show "x = y" using fatom_of_hatom_hatom_of_fatom grx gry by auto
    qed
   moreover
   have "hatom_of_fatom ` {l. groundl l} = UNIV"
     proof -
       {
         fix x
         have "x = hatom_of_fatom (fatom_of_hatom x)" by auto
         then have "x \<in> hatom_of_fatom ` {l. groundl l}" using ground_fatom_of_hatom by blast
       }
       then show ?thesis by auto
     qed
   ultimately show ?thesis unfolding bij_betw_def by auto
qed

subsubsection {* Enumerating ground atoms *}

definition ground_fatoms :: "fterm literal set" where
  "ground_fatoms \<equiv> {l. groundl l \<and> sign l = True}"

definition fatom_from_nat :: "nat \<Rightarrow> fterm literal" where
  "fatom_from_nat = (\<lambda>n. fatom_of_hatom (hatom_from_nat n))"

definition nat_from_fatom :: "fterm literal \<Rightarrow> nat" where
  "nat_from_fatom = (\<lambda>t. nat_from_hatom (hatom_of_fatom t))"

theorem diag_undiag_fatom[simp]: "grounds ts \<Longrightarrow> fatom_from_nat (nat_from_fatom (Pos p ts)) = Pos p ts"
unfolding fatom_from_nat_def nat_from_fatom_def by auto

theorem undiag_diag_fatom[simp]: "nat_from_fatom (fatom_from_nat n) = n" unfolding fatom_from_nat_def nat_from_fatom_def by auto

lemma undiag_neg: "nat_from_fatom (Neg P ts) = nat_from_fatom (Pos P ts)" unfolding nat_from_fatom_def using undiag_neg2 by auto

lemma fatom_from_nat_bij: "bij_betw fatom_from_nat UNIV ground_fatoms" 
proof -
  have bii: "bij_betw hatom_from_nat UNIV hatoms" using hatom_from_nat_bij by auto
  from bii have "range hatom_from_nat = hatoms" unfolding bij_betw_def by auto
  have "range fatom_from_nat = ground_fatoms"
    apply rule
    unfolding fatom_from_nat_def ground_fatoms_def  using ground_fatom_of_hatom sign_fatom_of_hatom sign_hatom_from_nat  apply auto[1]
    apply rule
    apply (subgoal_tac "x = fatom_of_hatom (hatom_from_nat (nat_from_fatom x))")
    apply simp unfolding nat_from_fatom_def
    apply auto
    apply (subgoal_tac "x = Pos (get_pred x) (get_terms x)")
    using hatom_from_nat_nat_from_hatom fatom_of_hatom_hatom_of_fatom
    apply (metis hatom_of_fatom.simps(1) literal.disc(1) mem_Collect_eq) 
    apply simp
    done
  moreover
  have "inj fatom_from_nat" unfolding inj_on_def
    proof (rule ballI; rule ballI; rule impI)
      fix x y
      assume "fatom_from_nat x = fatom_from_nat y"
      then have "nat_from_fatom (fatom_from_nat x) = nat_from_fatom (fatom_from_nat y)" by auto
      then show "x = y" by auto
    qed
  ultimately show ?thesis unfolding bij_betw_def by auto
qed

lemma ground_fatom_from_nat: "groundl (fatom_from_nat x)" unfolding fatom_from_nat_def using ground_fatom_of_hatom by auto

lemma sign_fatom_from_nat: "sign (fatom_from_nat x) = True" unfolding fatom_from_nat_def using sign_hatom_from_nat sign_fatom_of_hatom by auto

lemma nat_from_fatom_bij: "bij_betw nat_from_fatom ground_fatoms UNIV"
proof -
  have bii: "bij_betw nat_from_hatom hatoms UNIV" using nat_from_hatom_bij by auto
  from bii have "range nat_from_hatom = UNIV" unfolding bij_betw_def by auto
  {
     fix x::nat
     have "x = nat_from_fatom (fatom_from_nat x) \<and> groundl (fatom_from_nat x) \<and> sign (fatom_from_nat x)" 
       using TermsAndLiterals.undiag_diag_fatom ground_fatom_from_nat sign_fatom_from_nat by auto
     then have "\<exists>a. x = nat_from_fatom a \<and> groundl a \<and> sign a" by blast
  }
  then have "nat_from_fatom ` ground_fatoms = UNIV" unfolding ground_fatoms_def by auto
  moreover
  have "inj_on nat_from_fatom ground_fatoms" unfolding inj_on_def
    proof (rule ballI; rule ballI; rule impI)
      fix x y
      assume gr: "x \<in> ground_fatoms" "y \<in> ground_fatoms"
      then have sn: "sign x = True" "sign y = True" unfolding ground_fatoms_def by auto
      assume "nat_from_fatom x = nat_from_fatom y"
      then have "fatom_from_nat (nat_from_fatom x) = fatom_from_nat (nat_from_fatom y)" by auto
      then show "x = y" using gr sn
        apply (cases x) apply (cases y)
        apply auto unfolding ground_fatoms_def apply auto
        done
    qed
  ultimately show ?thesis unfolding bij_betw_def by auto
qed

theorem fatom_from_nat_is_nat_from_fatom:
  assumes gr: "groundl l"
  assumes si: "sign l = True"
  assumes fa: "fatom_from_nat i = l"
  shows "i = nat_from_fatom l"
using assms by auto

lemma nat_from_fatom_inj_mod_sign:
  assumes "nat_from_fatom l1 = nat_from_fatom l2"
  assumes gr1: "groundl l1"
  assumes gr2: "groundl l2"
  shows "get_pred l1 = get_pred l2 \<and> get_terms l1 = get_terms l2"
proof -
  {
    fix p1 fix ts1::"fterm list"
    fix p2 fix ts2::"fterm list"
    let ?l1 = "Pos p1 ts1" let ?l2 = "Pos p2 ts2"
    assume asm: "nat_from_fatom (Pos p1 ts1) = nat_from_fatom (Pos p2 ts2) \<and> groundl (Pos p1 ts1) \<and> groundl (Pos p2 ts2)"
    then have "nat_from_hatom (hatom_of_fatom ?l1) = nat_from_hatom (hatom_of_fatom ?l2)" unfolding nat_from_fatom_def by auto
    then have "get_pred (hatom_of_fatom ?l1) = get_pred (hatom_of_fatom ?l2) \<and> get_terms (hatom_of_fatom ?l1) = get_terms (hatom_of_fatom ?l2)" using nat_from_hatom_inj_mod_sign by blast
    then have "Pos (get_pred (hatom_of_fatom ?l1)) (get_terms (hatom_of_fatom ?l1)) = Pos (get_pred (hatom_of_fatom ?l2)) (get_terms (hatom_of_fatom ?l2))" by auto
    then have "Pos p1 (hterms_of_fterms ts1) = Pos p2 (hterms_of_fterms ts2)" using asm by auto
    then have "hatom_of_fatom (Pos p1 ts1) = hatom_of_fatom (Pos p2 ts2)" by auto
    then have "hatom_of_fatom ?l1 = hatom_of_fatom ?l2" using asm by auto
    then have "?l1 = ?l2" using hatom_of_fatom_bij asm unfolding bij_betw_def inj_on_def by blast
    then have "get_pred ?l1 = get_pred ?l2 \<and> get_terms ?l1 = get_terms ?l2" by auto
    then have "p1 = p2 \<and> ts1 = ts2" using asm by auto
  }
  then have PosPos: "!! l1 p1 ts1 l2 p2 ts2. nat_from_fatom (Pos p1 ts1) = nat_from_fatom (Pos p2 ts2) \<and> groundl (Pos p1 ts1) \<and> groundl (Pos p2 ts2) \<Longrightarrow>  p1 =  p2 \<and> ts1 = ts2" by -
  {
    fix l1 fix p1 fix ts1
    fix l2 fix p2 fix ts2
    assume asm: "nat_from_fatom (Pos p1 ts1) = nat_from_fatom (Neg p2 ts2) \<and> groundl (Pos p1 ts1) \<and> groundl (Neg p2 ts2)"
    then have "nat_from_fatom (Pos p1 ts1) = nat_from_fatom (Pos p2 ts2) \<and> groundl (Pos p1 ts1) \<and> groundl (Pos p2 ts2)" using undiag_neg by auto
    then have "p1 = p2 \<and> ts1 = ts2" using PosPos by blast
  }
  then have PosNeg: "!! l1 p1 ts1 l2 p2 ts2.  nat_from_fatom (Pos p1 ts1) = nat_from_fatom (Neg p2 ts2) \<and> groundl (Pos p1 ts1) \<and> groundl (Neg p2 ts2) \<Longrightarrow> p1 = p2 \<and> ts1 = ts2" by -
  {
    fix l1 fix p1 fix ts1
    fix l2 fix p2 fix ts2
    assume asm: "nat_from_fatom (Neg p1 ts1) = nat_from_fatom (Neg p2 ts2) \<and> groundl (Neg p1 ts1) \<and> groundl (Neg p2 ts2)"
    then have "nat_from_fatom (Pos p1 ts1) = nat_from_fatom (Pos p2 ts2) \<and> groundl (Pos p1 ts1) \<and> groundl (Pos p2 ts2)" using undiag_neg by auto
    then have "p1 = p2 \<and> ts1 = ts2" using PosPos by blast
  }
  then have NegNeg: "!! l1 p1 ts1 l2 p2 ts2. nat_from_fatom (Neg p1 ts1) = nat_from_fatom (Neg p2 ts2) \<and> groundl (Neg p1 ts1) \<and> groundl (Neg p2 ts2) \<Longrightarrow> p1 = p2 \<and> ts1 = ts2" by -
  {
    fix l1 fix p1 fix ts1
    fix l2 fix p2 fix ts2
    assume asm: "nat_from_fatom (Neg p1 ts1) = nat_from_fatom (Pos p2 ts2) \<and> groundl (Neg p1 ts1) \<and> groundl (Pos p2 ts2)"
    then have "nat_from_fatom (Pos p1 ts1) = nat_from_fatom (Pos p2 ts2) \<and> groundl (Pos p1 ts1) \<and> groundl (Pos p2 ts2)" using undiag_neg by auto
    then have "p1 = p2 \<and> ts1 = ts2" using PosPos by blast
  }
  then have NegPos: "!! l1 p1 ts1 l2 p2 ts2. nat_from_fatom (Neg p1 ts1) = nat_from_fatom (Pos p2 ts2) \<and> groundl (Neg p1 ts1) \<and> groundl (Pos p2 ts2) \<Longrightarrow> p1 = p2 \<and> ts1 = ts2" by -
  show "get_pred l1 = get_pred l2 \<and> get_terms l1 = get_terms l2" 
    using assms 
    apply (induction l1)
    apply (induction l2)
    using PosPos apply blast
    using PosNeg literal.sel apply metis
    apply (induction l2)
    using NegPos literal.sel apply metis
    using NegNeg apply metis
    done
qed




end