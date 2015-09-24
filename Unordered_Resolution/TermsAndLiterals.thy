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

theory TermsAndLiterals imports Main begin


text_raw {*\DefineSnippet{symbols}{*}    
type_synonym var_sym  = string
type_synonym fun_sym  = string
type_synonym pred_sym = string
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{fterm}{*}
datatype fterm = 
  Fun fun_sym "fterm list"
| Var var_sym
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{ground}{*}
fun ground :: "fterm \<Rightarrow> bool" where
  "ground (Var x) \<longleftrightarrow> False"
| "ground (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground t)"

abbreviation grounds :: "fterm list \<Rightarrow> bool" where
  "grounds ts \<equiv> (\<forall>t \<in> set ts. ground t)"
text_raw {*}%EndSnippet*}
(* I could use anonymous variables in this definition *)

text_raw {*\DefineSnippet{hterm}{*}
datatype hterm = HFun fun_sym "hterm list"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{literal}{*}
datatype 't literal = 
  is_pos: Pos (get_pred: pred_sym) (get_terms: "'t list")
| Neg (get_pred: pred_sym) (get_terms: "'t list")
text_raw {*}%EndSnippet*}

(* begin Berghofer *)
subsection {* Enumerating datatypes *}

(* text {* \label{sec:enumeration} In the following section, we will show that elements of datatypes can be enumerated. This will be done by specifying functions that map natural numbers to elements of datatypes and vice versa. *}*)
subsubsection {* Enumerating Pairs of Natural Numbers *}

(*text {* \begin{figure} \begin{center} \includegraphics[scale=0.6]{diag} \end{center} \caption{Cantor's method for enumerating sets of pairs}\label{fig:diag} \end{figure} As a starting point, we show that pairs of natural numbers are enumerable. For this purpose, we use a method due to Cantor, which is illustrated in \figref{fig:diag}. The function for mapping natural numbers to pairs of natural numbers can be characterized recursively as follows: *}*)
primrec diag :: "nat \<Rightarrow> (nat \<times> nat)"
where
  "diag 0 = (0, 0)"
| "diag (Suc n) =
     (let (x, y) = diag n
      in case y of
          0 \<Rightarrow> (0, Suc x)
        | Suc y \<Rightarrow> (Suc x, y))"

theorem diag_le1: "fst (diag (Suc n)) < Suc n"
  by (induct n) (simp_all add: Let_def split_def split add: nat.split)

theorem diag_le2: "snd (diag (Suc (Suc n))) < Suc (Suc n)"
  apply (induct n)
  apply (simp_all add: Let_def split_def split add: nat.split nat.split_asm)
  apply (rule impI)
  apply (case_tac n)
  apply simp
  apply hypsubst
  apply (rule diag_le1)
  done

theorem diag_le3: "fst (diag n) = Suc x \<Longrightarrow> snd (diag n) < n"
  apply (case_tac n)
  apply simp
  apply (case_tac nat)
  apply (simp add: Let_def)
  apply hypsubst
  apply (rule diag_le2)
  done

theorem diag_le4: "fst (diag n) = Suc x \<Longrightarrow> x < n"
  apply (case_tac n)
  apply simp
  apply (case_tac nat)
  apply (simp add: Let_def)
  apply hypsubst_thin
  apply (drule sym)
  apply (drule ord_eq_less_trans)
  apply (rule diag_le1)
  apply simp
  done

function undiag :: "nat \<times> nat \<Rightarrow> nat"
where
  "undiag (0, 0) = 0"
| "undiag (0, Suc y) = Suc (undiag (y, 0))"
| "undiag (Suc x, y) = Suc (undiag (x, Suc y))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(x, y). ((x + y) * (x + y + 1)) div 2 + x)") auto

theorem diag_undiag [simp]: "diag (undiag (x, y)) = (x, y)"
  by (rule undiag.induct) (simp add: Let_def)+

subsubsection {* Enumerating Trees *}
(* text {* When writing enumeration functions for datatypes, it is useful to note that all datatypes are some kind of trees. In order to avoid re-inventing the wheel, we therefore write enumeration functions for trees once and for all. In applications, we then only have to write functions for converting between trees and concrete datatypes. *}*)

datatype btree = Leaf nat | Branch btree btree

function diag_btree :: "nat \<Rightarrow> btree"
where
  "diag_btree n = (case fst (diag n) of
       0 \<Rightarrow> Leaf (snd (diag n))
     | Suc x \<Rightarrow> Branch (diag_btree x) (diag_btree (snd (diag n))))"
  by auto

termination
  by (relation "measure (\<lambda>x. x)") (auto intro: diag_le3 diag_le4)

primrec undiag_btree :: "btree \<Rightarrow> nat"
where
  "undiag_btree (Leaf n) = undiag (0, n)"
| "undiag_btree (Branch t1 t2) =
     undiag (Suc (undiag_btree t1), undiag_btree t2)"

theorem diag_undiag_btree [simp]: "diag_btree (undiag_btree t) = t"
  by (induct t) (simp_all add: Let_def)

declare diag_btree.simps [simp del] undiag_btree.simps [simp del]

subsubsection {* Enumerating Lists *}

fun list_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a list"
where
  "list_of_btree f (Leaf x) = []"
| "list_of_btree f (Branch (Leaf n) t) = f n # list_of_btree f t"

primrec btree_of_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> btree"
where
  "btree_of_list f [] = Leaf 0"
| "btree_of_list f (x # xs) = Branch (Leaf (f x)) (btree_of_list f xs)"

definition diag_list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "diag_list f n = list_of_btree f (diag_btree n)"

definition undiag_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "undiag_list f xs = undiag_btree (btree_of_list f xs)"

theorem diag_undiag_list [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> diag_list d (undiag_list u xs) = xs"
  by (induct xs) (simp_all add: diag_list_def undiag_list_def)

subsubsection {* Enumerating hterms *}

fun term_of_btree :: "(nat \<Rightarrow> string) \<Rightarrow> btree \<Rightarrow> hterm"
and term_list_of_btree :: "(nat \<Rightarrow> string) \<Rightarrow> btree \<Rightarrow> hterm list"
where
  "term_of_btree f (Leaf m) = HFun (f m) []"
| "term_of_btree f (Branch (Leaf m) t) =
     HFun (f m) (term_list_of_btree f t)"
| "term_list_of_btree f (Leaf m) = []"
| "term_list_of_btree f (Branch t1 t2) =
     term_of_btree f t1 # term_list_of_btree f t2"

primrec btree_of_term :: "(string \<Rightarrow> nat) \<Rightarrow> hterm \<Rightarrow> btree"
    and btree_of_term_list :: "(string \<Rightarrow> nat) \<Rightarrow> hterm list \<Rightarrow> btree"
where
  "btree_of_term f (HFun m ts) = (if ts=[] then Leaf (f m) else Branch (Leaf (f m)) (btree_of_term_list f ts))"
| "btree_of_term_list f [] = Leaf 0"
| "btree_of_term_list f (t # ts) = Branch (btree_of_term f t) (btree_of_term_list f ts)"

theorem term_btree: assumes du: "\<And>x. d (u x) = x"
  shows "term_of_btree d (btree_of_term u t) = t"
  and "term_list_of_btree d (btree_of_term_list u ts) = ts"
  by (induct t and ts rule: btree_of_term.induct btree_of_term_list.induct) (simp_all add: du)

definition diag_term :: "(nat \<Rightarrow> string) \<Rightarrow> nat \<Rightarrow> hterm" where
  "diag_term f n = term_of_btree f (diag_btree n)"

definition undiag_term :: "(string \<Rightarrow> nat) \<Rightarrow> hterm \<Rightarrow> nat" where
  "undiag_term f t = undiag_btree (btree_of_term f t)"

theorem diag_undiag_term [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> diag_term d (undiag_term u t) = t"
  by (simp add: diag_term_def undiag_term_def term_btree)
(* end Berghofer *)

subsubsection {* Enumerating chars *}

definition diag_char :: "nat \<Rightarrow> char" where 
  "diag_char == char_of_nat"

definition undiag_char :: "char \<Rightarrow> nat" where 
  "undiag_char == nat_of_char"

theorem diag_undiag_char [simp]: "diag_char (undiag_char c) = c"
  unfolding diag_char_def undiag_char_def by auto

subsubsection {* Enumerating strings *}
definition diag_string :: "nat \<Rightarrow> string" where
  "diag_string \<equiv> diag_list diag_char"

definition undiag_string :: "string \<Rightarrow> nat" where
  "undiag_string \<equiv> undiag_list undiag_char"

theorem diag_undiag_string [simp]: 
  "diag_string (undiag_string s) = s"
  unfolding diag_string_def undiag_string_def by auto

subsubsection {* Really enumerating hterms *}

definition diag_hterm :: "nat \<Rightarrow> hterm" where
  "diag_hterm \<equiv> diag_term diag_string"

definition undiag_hterm :: "hterm \<Rightarrow> nat" where
  "undiag_hterm \<equiv> undiag_term undiag_string"

theorem diag_undiag_hterm[simp]: 
  "diag_hterm (undiag_hterm t) = t"
  unfolding diag_hterm_def undiag_hterm_def by auto

subsubsection {* Enumerating hatoms *}

text_raw {*\DefineSnippet{undiag_hatom}{*}
definition undiag_hatom :: "hterm literal \<Rightarrow> nat" where
  "undiag_hatom a \<equiv> undiag (undiag_string (get_pred a), undiag_list undiag_hterm (get_terms a))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{diag_hatom}{*}
definition diag_hatom :: "nat \<Rightarrow> hterm literal" where
  "diag_hatom a \<equiv> 
     (let (p,ts) = diag a in
       (Pos (diag_string p) (diag_list diag_hterm ts))
     )"
text_raw {*}%EndSnippet*}

theorem diag_undiag_hatom[simp]: 
  "is_pos a \<Longrightarrow> diag_hatom (undiag_hatom a) = a"
  unfolding diag_hatom_def undiag_hatom_def by auto

subsubsection {* Enumerating ground terms *}

text_raw {*\DefineSnippet{fterm_of_hterm}{*}
primrec fterm_of_hterm :: "hterm \<Rightarrow> fterm"
and fterms_of_hterms :: "hterm list \<Rightarrow> fterm list" where
  "fterm_of_hterm (HFun p ts) = Fun p (fterms_of_hterms ts)"
| "fterms_of_hterms [] = []"
| "fterms_of_hterms (t#ts) = fterm_of_hterm t # fterms_of_hterms ts"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{hterm_of_fterm}{*}
primrec hterm_of_fterm :: "fterm \<Rightarrow> hterm"
and hterms_of_fterms :: "fterm list \<Rightarrow> hterm list" where
  "hterm_of_fterm (Fun p ts) = HFun p (hterms_of_fterms ts)"
| "hterms_of_fterms [] = []"
| "hterms_of_fterms (t#ts) = hterm_of_fterm t # hterms_of_fterms ts"
text_raw {*}%EndSnippet*}

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

text_raw {*\DefineSnippet{undiag_fatom}{*}
definition undiag_fatom :: "fterm literal \<Rightarrow> nat" where
  "undiag_fatom t = undiag_hatom (hatom_of_fatom t)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{diag_fatom}{*}
definition diag_fatom :: "nat \<Rightarrow> fterm literal" where
  "diag_fatom n = fatom_of_hatom (diag_hatom n)"
text_raw {*}%EndSnippet*}

theorem diag_undiag_fatom[simp]: "grounds ts \<Longrightarrow> diag_fatom (undiag_fatom (Pos p ts)) = Pos p ts"
unfolding undiag_fatom_def diag_fatom_def by auto

end