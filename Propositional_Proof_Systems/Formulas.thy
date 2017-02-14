section \<open>Formulas\<close>

theory Formulas
imports Main "~~/src/HOL/Library/Countable"
begin

(* unrelated, but I need this in too many places. *)
notation insert ("_ \<cdot> _" [56,55] 55)

datatype form = 
    Atom nat
  | Bot             ("\<bottom>")  
  | Not form         ("\<^bold>\<not>")
  | And form form    (infix "\<^bold>\<and>" 68)
  | Or form form     (infix "\<^bold>\<or>" 68)
  | Imp form form     (infixr "\<^bold>\<rightarrow>" 68)

(* I'm not sure I'm happy about the definition of what is an atom.
   I'm inclined to treat nat as our atom set and call an Atom k an "atom formula",
   but this goes against anything the literature does. So, Atom k will be an atom,
   k its index. *)

primrec atoms where
"atoms (Atom k) = {k}" |
"atoms Bot = {}" |
"atoms (Not F) = atoms F" |
"atoms (And F G) = atoms F \<union> atoms G" |
"atoms (Or F G) = atoms F \<union> atoms G" |
"atoms (Imp F G) = atoms F \<union> atoms G"

lemma atoms_finite[simp,intro!]: "finite (atoms F)" by(induction F; simp)

primrec subformulae where
"subformulae \<bottom> = {\<bottom>}" |
"subformulae (Atom k) = {Atom k}" |
"subformulae (Not F) = Not F \<cdot> subformulae F" |
"subformulae (And F G) = And F G \<cdot> subformulae F \<union> subformulae G" |
"subformulae (Imp F G) = Imp F G \<cdot> subformulae F \<union> subformulae G" |
"subformulae (Or F G) = Or F G \<cdot> subformulae F \<union> subformulae G"
(* unused *)

lemma "Atom ` atoms F \<subseteq> subformulae F"
  by (induction F) auto
    
subsection\<open>Derived Connectives\<close>
    
definition Top ("\<top>") where
"\<top> \<equiv> \<bottom> \<^bold>\<rightarrow> \<bottom>"
lemma top_atoms_simp[simp]: "atoms \<top> = {}" unfolding Top_def by simp

primrec BigAnd :: "form list \<Rightarrow> form" ("\<^bold>\<And>_") where
"\<^bold>\<And>Nil = (\<^bold>\<not>\<bottom>)" -- "essentially, it doesn't matter what I use here. But since I want to use this in CNFs, implication is not a nice thing to have." |
"\<^bold>\<And>(F#Fs) = F \<^bold>\<and> \<^bold>\<And>Fs"

primrec BigOr :: "form list \<Rightarrow> form" ("\<^bold>\<Or>_") where
"\<^bold>\<Or>Nil = \<bottom>" |
"\<^bold>\<Or>(F#Fs) = F \<^bold>\<or> \<^bold>\<Or>Fs"

text\<open>Formulas are countable, and @{method countable_datatype} is really helpful with that.\<close> 
instance form :: countable by countable_datatype

end