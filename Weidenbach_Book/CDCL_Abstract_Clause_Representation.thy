theory CDCL_Abstract_Clause_Representation
imports Main Partial_Clausal_Logic
begin

type_synonym 'v clause = "'v literal multiset"
type_synonym 'v clauses = "'v clause multiset"


subsection \<open>Abstract Clause Representation\<close>

text \<open>We will abstract the representation of clause and clauses via two locales. We expect our
  representation to behave like multiset, but the internal representation can be done using list
  or whatever other representation.

  We assume the following:
  \<^item> there is an equivalent to adding and removing a literal and to taking the union of clauses.
  \<close>

locale raw_cls =
   fixes
    mset_cls :: "'cls \<Rightarrow> 'v clause"
begin
end

text \<open>The two following locales are the \<^emph>\<open>exact same\<close> locale, but we two different locales. 
  Otherwise, instantiating @{text raw_clss} would lead to duplicate constants. 
  (TODO: better idea?).\<close>
locale abstract_with_index =
  fixes
    get :: "'a \<Rightarrow> 'it \<Rightarrow> 'conc" and
    valid :: "'it \<Rightarrow> 'a  \<Rightarrow> bool" and
    convert_to_mset :: "'a \<Rightarrow> 'conc multiset"
  assumes
    in_clss_mset_cls[dest]:
      "valid a Cs \<Longrightarrow> get Cs a \<in># convert_to_mset Cs" and
    in_mset_cls_exists_preimage:
      "b \<in># convert_to_mset Cs \<Longrightarrow> \<exists>b'. valid b' Cs \<and> get Cs b' = b"

locale abstract_with_index2 =
  fixes
    get :: "'a \<Rightarrow> 'it \<Rightarrow> 'conc" and
    valid :: "'it \<Rightarrow> 'a  \<Rightarrow> bool" and
    convert_to_mset :: "'a \<Rightarrow> 'conc multiset"
  assumes
    in_clss_mset_clss[dest]:
      "valid a Cs \<Longrightarrow> get Cs a \<in># convert_to_mset Cs" and
    in_mset_clss_exists_preimage:
      "b \<in># convert_to_mset Cs \<Longrightarrow> \<exists>b'. valid b' Cs \<and> get Cs b' = b"

locale raw_clss =
  abstract_with_index cls_lit in_cls mset_cls +
  abstract_with_index2 clss_cls in_clss mset_clss
  for
    cls_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal" and
    in_cls :: "'lit \<Rightarrow> 'cls \<Rightarrow> bool" and
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    clss_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls" and
    in_clss :: "'cls_it \<Rightarrow> 'clss \<Rightarrow> bool" and
    mset_clss:: "'clss \<Rightarrow> 'cls multiset"
begin
notation in_cls (infix "\<in>\<down>" 49)
notation in_clss (infix "\<in>\<Down>" 49)

notation cls_lit (infix "\<down>" 49)
notation clss_cls (infix "\<Down>" 49)

abbreviation raw_clss where
"raw_clss S \<equiv> image_mset mset_cls (mset_clss S)"
end

experiment
begin
  interpretation abstract_with_index
    nth
    "\<lambda>L C. L < length C"
    mset
    apply unfold_locales
    by (metis in_set_conv_nth set_mset_mset)+
    
  interpretation abstract_with_index2
    nth
    "\<lambda>L C. L < length C"
    mset
    apply unfold_locales
    by (metis in_set_conv_nth set_mset_mset)+
    
  interpretation list_cls: raw_clss
    nth
    "\<lambda>L C. L < length C"
    mset

    nth
    "\<lambda>C Cs. C < length Cs"
    "\<lambda>Cs. mset Cs"
    by unfold_locales

end

end