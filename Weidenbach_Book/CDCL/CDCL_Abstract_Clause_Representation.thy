theory CDCL_Abstract_Clause_Representation
imports Entailment_Definition.Partial_Herbrand_Interpretation
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

text \<open>The two following locales are the \<^emph>\<open>exact same\<close> locale, but we need two different locales.
  Otherwise, instantiating @{text raw_clss} would lead to duplicate constants.\<close>
locale abstract_with_index =
  fixes
    get_lit :: "'a \<Rightarrow> 'it \<Rightarrow> 'conc option" and
    convert_to_mset :: "'a \<Rightarrow> 'conc multiset"
  assumes
    in_clss_mset_cls[dest]:
      "get_lit Cs a = Some e \<Longrightarrow> e \<in># convert_to_mset Cs" and
    in_mset_cls_exists_preimage:
      "b \<in># convert_to_mset Cs \<Longrightarrow> \<exists>b'. get_lit Cs b' = Some b"

locale abstract_with_index2 =
  fixes
    get_lit :: "'a \<Rightarrow> 'it \<Rightarrow> 'conc option" and
    convert_to_mset :: "'a \<Rightarrow> 'conc multiset"
  assumes
    in_clss_mset_clss[dest]:
      "get_lit Cs a = Some e \<Longrightarrow> e \<in># convert_to_mset Cs" and
    in_mset_clss_exists_preimage:
      "b \<in># convert_to_mset Cs \<Longrightarrow> \<exists>b'. get_lit Cs b' = Some b"

locale raw_clss =
  abstract_with_index get_lit mset_cls +
  abstract_with_index2 get_cls mset_clss
  for
    get_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    get_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    mset_clss:: "'clss \<Rightarrow> 'cls multiset"
begin

definition cls_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal" (infix "\<down>" 49) where
"C \<down> a \<equiv> the (get_lit C a)"

definition clss_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls" (infix "\<Down>" 49) where
"C \<Down> a \<equiv> the (get_cls C a)"

definition in_cls :: "'lit \<Rightarrow> 'cls \<Rightarrow> bool" (infix "\<in>\<down>" 49) where
"a \<in>\<down> Cs \<equiv> get_lit Cs a \<noteq> None"

definition in_clss :: "'cls_it \<Rightarrow> 'clss \<Rightarrow> bool" (infix "\<in>\<Down>" 49) where
"a \<in>\<Down> Cs \<equiv> get_cls Cs a \<noteq> None"

definition raw_clss where
"raw_clss S \<equiv> image_mset mset_cls (mset_clss S)"

end

experiment
begin
  fun safe_nth where
  "safe_nth (x # _) 0 = Some x" |
  "safe_nth (_ # xs) (Suc n) = safe_nth xs n" |
  "safe_nth [] _ = None"

  lemma safe_nth_nth: "n < length l \<Longrightarrow> safe_nth l n = Some (nth l n)"
    by (induction l n rule: safe_nth.induct) auto

  lemma safe_nth_None: "n \<ge> length l \<Longrightarrow> safe_nth l n = None"
    by (induction l n rule: safe_nth.induct) auto

  lemma safe_nth_Some_iff: "safe_nth l n = Some m \<longleftrightarrow> n < length l \<and> m = nth l n"
    apply (rule iffI)
      defer apply (auto simp: safe_nth_nth)[]
    by (induction l n rule: safe_nth.induct) auto

  lemma safe_nth_None_iff: "safe_nth l n = None \<longleftrightarrow> n \<ge> length l"
    apply (rule iffI)
      defer apply (auto simp: safe_nth_None)[]
    by (induction l n rule: safe_nth.induct) auto

  interpretation abstract_with_index
    safe_nth
    mset
    apply unfold_locales
      apply (simp add: safe_nth_Some_iff)
    by (metis in_set_conv_nth safe_nth_nth set_mset_mset)

  interpretation abstract_with_index2
    safe_nth
    mset
    apply unfold_locales
      apply (simp add: safe_nth_Some_iff)
    by (metis in_set_conv_nth safe_nth_nth set_mset_mset)

  interpretation list_cls: raw_clss
    safe_nth mset
    safe_nth mset
    by unfold_locales
end

end
