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
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls"
  assumes
    insert_cls[simp]: "mset_cls (insert_cls L C) = mset_cls C + {#L#}" and
    remove_lit[simp]: "mset_cls (remove_lit L C) = remove1_mset L (mset_cls C)"
begin
end

locale raw_ccls_union =
  fixes
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    union_cls :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls"
  assumes
    insert_ccls[simp]: "mset_cls (insert_cls L C) = mset_cls C + {#L#}" and
    mset_ccls_union_cls[simp]: "mset_cls (union_cls C D) = mset_cls C #\<union> mset_cls D" and
    remove_clit[simp]: "mset_cls (remove_lit L C) = remove1_mset L (mset_cls C)"
begin
end

text \<open>Instantiation of the previous locale, in an unnamed context to avoid polluating with simp
  rules\<close>
context
begin
  interpretation list_cls: raw_cls mset
    "op #" remove1
    by unfold_locales (auto simp: union_mset_list ex_mset)

  interpretation cls_cls: raw_cls id
    "\<lambda>L C. C + {#L#}" remove1_mset
    by unfold_locales (auto simp: union_mset_list)
    
  interpretation list_cls: raw_ccls_union mset
    union_mset_list
    "op #" remove1
    by unfold_locales (auto simp: union_mset_list ex_mset)

  interpretation cls_cls: raw_ccls_union id
    "op #\<union>" "\<lambda>L C. C + {#L#}" remove1_mset
    by unfold_locales (auto simp: union_mset_list)
end

text \<open>Over the abstract clauses, we have the following properties:
   \<^item> We can insert a clause
   \<^item> We can take the union (used only in proofs for the definition of @{term clauses})
   \<^item> there is an operator indicating whether the abstract clause is contained or not
   \<^item> if a concrete clause is contained the abstract clauses, then there is an abstract clause
  \<close>
locale raw_clss =
  raw_cls mset_cls insert_cls remove_lit
  for
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" +
  fixes
    mset_clss:: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss"
  assumes
    insert_clss[simp]: "mset_clss (insert_clss L C) = mset_clss C + {#mset_cls L#}" and
    union_clss[simp]: "mset_clss (union_clss C D) = mset_clss C + mset_clss D" and
    mset_clss_union_clss[simp]: "mset_clss (insert_clss C' D) = {#mset_cls C'#} + mset_clss D" and
    in_clss_mset_clss[dest]: "in_clss a C \<Longrightarrow> mset_cls a \<in># mset_clss C" and
    in_mset_clss_exists_preimage: "b \<in># mset_clss C \<Longrightarrow> \<exists>b'. in_clss b' C \<and> mset_cls b' = b" and
    remove_from_clss_mset_clss[simp]:
      "mset_clss (remove_from_clss a C) = mset_clss C - {#mset_cls a#}" and
    in_clss_union_clss[simp]:
      "in_clss a (union_clss C D) \<longleftrightarrow> in_clss a C \<or> in_clss a D"
begin

end

experiment
begin
  fun remove_first where
  "remove_first _ [] = []" |
  "remove_first C (C' # L) = (if mset C = mset C' then L else C' # remove_first C L)"

  lemma mset_map_mset_remove_first:
    "mset (map mset (remove_first a C)) = remove1_mset (mset a) (mset (map mset C))"
    by (induction C) (auto simp: ac_simps remove1_mset_single_add)

  interpretation clss_clss: raw_clss id "\<lambda>L C. C + {#L#}" remove1_mset
    id "op +" "op \<in>#" "\<lambda>L C. C + {#L#}" remove1_mset
    by unfold_locales (auto simp: ac_simps)

  interpretation list_clss: raw_clss mset
    "op #" remove1 "\<lambda>L. mset (map mset L)" "op @" "\<lambda>L C. L \<in> set C" "op #"
    remove_first
    by unfold_locales (auto simp: ac_simps union_mset_list mset_map_mset_remove_first ex_mset)
end

end