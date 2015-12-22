section{* Terms and Literals *}
text {* \label{termsandliterals} 
Author: Stefan Berghofer, TU Muenchen, 2003

Author: Anders Schlichtkrull, DTU, 2015

This file is a redistribution of a formalization by Stefan Berghofer with modifications. It is released under the following BSD software license:

{ \footnotesize
\begin{verbatim}
Copyright (c) 2004, Gerwin Klein, Tobias Nipkow, Lawrence C. Paulson
Copyright (c) 2004, contributing authors 
                    (see author notice in individual files)

All rights reserved.

All files in the Archive of Formal Proofs that are unmarked or marked
with 'License: BSD' are released under the following license. Files
marked with 'License: LGPL' are released under the terms detailed in
LICENSE.LGPL


Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.  Redistributions
in binary form must reproduce the above copyright notice, this list of
conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.  Neither the name of
the Archive of Formal Proofs nor the names of its contributors may be
used to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
\end{verbatim}
*}

theory TermsAndLiterals imports Main "~~/src/HOL/Library/Countable_Set" begin

type_synonym var_sym  = string
type_synonym fun_sym  = string
type_synonym pred_sym = string

datatype fterm = 
  Fun fun_sym "fterm list"
| Var var_sym

datatype hterm = HFun fun_sym "hterm list"

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

lemma (in countable) to_nat_from_nat: "infinite UNIV \<Longrightarrow> to_nat (from_nat n) = n" oops (* Could be nice to have *)

thm Hilbert_Choice.bij_betw_inv_into
thm inj_iff
thm f_inv_into_f
thm inv_into_f_f

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
  "string_from_nat \<equiv> inv_into UNIV nat_from_string"

lemma nat_from_string_bij: "bij nat_from_string"
  proof -
  have "countable (UNIV::string set)" by auto
  moreover
  have "infinite (UNIV::string set)" using List.infinite_UNIV_listI by auto
  ultimately
  obtain x where "bij (x:: string \<Rightarrow> nat)" using Countable_Set.countableE_infinite[of UNIV] by blast
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

find_theorems bij_betw infinite
find_theorems bij_betw id
find_theorems inv_into
find_theorems countable

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

lemma hatom_from_nat_Pos:
  assumes "hatom_from_nat n = l"
  shows "\<exists>p ts. l = Pos p ts"
proof -
  from assms have "l \<in> hatoms" using hatom_from_nat_bij unfolding bij_betw_def by auto
  then have "sign l = True" by auto
  then obtain p ts where "l = Pos p ts" by (cases l) auto
  then show ?thesis by auto
qed

subsubsection {* Convertions expressions and Herbrand expressions *}

primrec fterm_of_hterm :: "hterm \<Rightarrow> fterm"
and fterms_of_hterms :: "hterm list \<Rightarrow> fterm list" where
  "fterm_of_hterm (HFun p ts) = Fun p (fterms_of_hterms ts)"
| "fterms_of_hterms [] = []"
| "fterms_of_hterms (t#ts) = fterm_of_hterm t # fterms_of_hterms ts"

primrec hterm_of_fterm :: "fterm \<Rightarrow> hterm"
and hterms_of_fterms :: "fterm list \<Rightarrow> hterm list" where
  "hterm_of_fterm (Fun p ts) = HFun p (hterms_of_fterms ts)"
| "hterms_of_fterms [] = []"
| "hterms_of_fterms (t#ts) = hterm_of_fterm t # hterms_of_fterms ts"

theorem [simp]: "hterm_of_fterm (fterm_of_hterm t) = t" 
        "hterms_of_fterms (fterms_of_hterms ts) = ts" 
  by (induct t and ts rule: fterm_of_hterm.induct fterms_of_hterms.induct) auto

theorem [simp]: "ground t \<Longrightarrow> fterm_of_hterm (hterm_of_fterm t) = t" 
        "grounds ts \<Longrightarrow>fterms_of_hterms (hterms_of_fterms ts) = ts" 
  by (induct t and ts rule: hterm_of_fterm.induct hterms_of_fterms.induct) auto

subsubsection {* Enumerating ground atoms *}

fun fatom_of_hatom :: "hterm literal \<Rightarrow> fterm literal" where
  "fatom_of_hatom (Pos p ts) = Pos p (fterms_of_hterms ts)"
| "fatom_of_hatom (Neg p ts) = Neg p (fterms_of_hterms ts)"

fun hatom_of_fatom :: "fterm literal \<Rightarrow> hterm literal" where
  "hatom_of_fatom (Pos p ts) = Pos p (hterms_of_fterms ts)"
| "hatom_of_fatom (Neg p ts) = Neg p (hterms_of_fterms ts)"

theorem [simp]: "hatom_of_fatom (fatom_of_hatom (l)) =  l" by (cases l) auto

theorem [simp]: "grounds ts \<Longrightarrow> fatom_of_hatom (hatom_of_fatom (Pos p ts)) = Pos p ts"
by auto

definition fatom_from_nat :: "nat \<Rightarrow> fterm literal" where
  "fatom_from_nat n = fatom_of_hatom (hatom_from_nat n)"

definition nat_from_fatom :: "fterm literal \<Rightarrow> nat" where
  "nat_from_fatom t = nat_from_hatom (hatom_of_fatom t)"

theorem diag_undiag_fatom[simp]: "grounds ts \<Longrightarrow> fatom_from_nat (nat_from_fatom (Pos p ts)) = Pos p ts"
unfolding fatom_from_nat_def nat_from_fatom_def by auto

theorem undiag_diag_fatom: "nat_from_fatom (fatom_from_nat n) = n" unfolding fatom_from_nat_def nat_from_fatom_def by auto

lemma undiag_neg: "nat_from_fatom (Neg P ts) = nat_from_fatom (Pos P ts)" unfolding nat_from_fatom_def using undiag_neg2 by auto

end