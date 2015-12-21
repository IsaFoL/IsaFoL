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

fun ground :: "fterm \<Rightarrow> bool" where
  "ground (Var x) \<longleftrightarrow> False"
| "ground (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground t)"

abbreviation grounds :: "fterm list \<Rightarrow> bool" where
  "grounds ts \<equiv> (\<forall>t \<in> set ts. ground t)"

datatype hterm = HFun fun_sym "hterm list"

datatype 't literal = 
  sign: Pos (get_pred: pred_sym) (get_terms: "'t list")
| Neg (get_pred: pred_sym) (get_terms: "'t list")

subsection {* Enumeration *}

subsubsection {* Enumerating hterms *}

instantiation hterm :: countable begin
instance by countable_datatype
end

subsubsection {* Enumerating hatoms *}

term "to_nat (HFun '''' [])"
term "from_nat 0 = (HFun '''' [])"
term "from_nat::nat \<Rightarrow> hterm"
term "from_nat::nat \<Rightarrow> string"

instantiation literal :: (countable) countable begin
instance by countable_datatype
end

lemma Pos_count: "countable {l :: hterm literal. sign l = True}" by auto

definition undiag_hatom :: "hterm literal \<Rightarrow> nat" where
  "undiag_hatom \<equiv> (SOME f. bij_betw f {l :: hterm literal. sign l = True} (UNIV::nat set))"

lemma Pos_inf: "\<not>(finite {l :: hterm literal. sign l = True})" sorry

lemma bij_undiag_hatom: "bij_betw undiag_hatom {l :: hterm literal. sign l = True} (UNIV :: nat set)"
proof -
 from Pos_count Pos_inf obtain f where "bij_betw f {l :: hterm literal. sign l = True} (UNIV :: nat set)" 
   using countableE_infinite[of "{l :: hterm literal. sign l = True}"] by auto
 then show ?thesis unfolding undiag_hatom_def using someI_ex by metis
qed

definition diag_hatom where "diag_hatom \<equiv> inv undiag_hatom"

lemma "bij_betw f A B \<Longrightarrow> inj_on (inv f) A" unfolding bij_betw_def unfolding inj_on_def
proof (rule; rule)

lemma "bij_betw f A B \<Longrightarrow> bij_betw (inv f) B A"
unfolding bij_betw_def unfolding inj_on_def apply (rule conjI)
proof

lemma bij_diag_hatom: "bij_betw diag_hatom (UNIV :: nat set) {l :: hterm literal. sign l = True}" 
  unfolding diag_hatom_def using bij_undiag_hatom 

theorem diag_undiag_hatom[simp]: 
  assumes "sign a = True"
  shows "diag_hatom (undiag_hatom a) = a"
proof -
  have "surj
  
  show "diag_hatom (undiag_hatom a) = a" by auto
qed

subsubsection {* Enumerating ground terms *}

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

(* Only works for ground terms *)
definition diag_fterm :: "nat \<Rightarrow> fterm" where
  "diag_fterm n = fterm_of_hterm (diag_hterm n)"

(* Only works for ground terms *)
definition undiag_fterm :: "fterm \<Rightarrow> nat" where
  "undiag_fterm t = undiag_hterm (hterm_of_fterm t)"

theorem diag_undiag_fterm: "ground t \<Longrightarrow> diag_fterm (undiag_fterm t) = t"
unfolding diag_fterm_def undiag_fterm_def by auto

subsubsection {* Enumerating ground atoms *}

fun fatom_of_hatom :: "hterm literal \<Rightarrow> fterm literal" where
  "fatom_of_hatom (Pos p ts) = Pos p (fterms_of_hterms ts)"
| "fatom_of_hatom (Neg p ts) = Neg p (fterms_of_hterms ts)"

fun hatom_of_fatom :: "fterm literal \<Rightarrow> hterm literal" where
  "hatom_of_fatom (Pos p ts) = Pos p (hterms_of_fterms ts)"
| "hatom_of_fatom (Neg p ts) = Neg p (hterms_of_fterms ts)"

theorem [simp]: "hatom_of_fatom (fatom_of_hatom (Pos p ts)) = Pos p ts"
by auto

theorem [simp]: "grounds ts \<Longrightarrow> fatom_of_hatom (hatom_of_fatom (Pos p ts)) = Pos p ts"
by auto

definition undiag_fatom :: "fterm literal \<Rightarrow> nat" where
  "undiag_fatom t = undiag_hatom (hatom_of_fatom t)"

definition diag_fatom :: "nat \<Rightarrow> fterm literal" where
  "diag_fatom n = fatom_of_hatom (diag_hatom n)"

theorem diag_undiag_fatom[simp]: "grounds ts \<Longrightarrow> diag_fatom (undiag_fatom (Pos p ts)) = Pos p ts"
unfolding undiag_fatom_def diag_fatom_def by auto

lemma undiag_diag_fatom: "undiag_fatom (diag_fatom n) = n" sorry (* This lemma is WRONG *)

(* Countable.thy

prove my expressions countable, and then get what I need for free.

*)


end