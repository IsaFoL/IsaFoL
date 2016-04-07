theory CDCL_Abstract_Clause_Representation
imports Main Partial_Clausal_Logic "~~/src/HOL/Library/RBT"
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

text \<open>Instantiation of the previous locale, in an unnamed context to avoid polluating with simp
  rules\<close>
context
begin
  interpretation list_cls: raw_cls mset
    by unfold_locales

  interpretation cls_cls: raw_cls id
    by unfold_locales

end

text \<open>Over the abstract clauses, we have the following properties:
   \<^item> We can insert a clause
   \<^item> We can take the union (used only in proofs for the definition of @{term clauses})
   \<^item> there is an operator indicating whether the abstract clause is contained or not
   \<^item> if a concrete clause is contained the abstract clauses, then there is an abstract clause
  \<close>
locale raw_clss =
   fixes mset_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'v clause" and
    mset_clss:: "'clss \<Rightarrow> 'v clauses" and
    valid_in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool"
  assumes
    valid_in_clss_mset_clss[dest]: "valid_in_clss a C \<Longrightarrow> mset_cls C a \<in># mset_clss C" and
    in_mset_clss_exists_preimage: "b \<in># mset_clss C \<Longrightarrow> \<exists>b'. valid_in_clss b' C \<and> mset_cls C b' = b"
begin

end

experiment
begin

  interpretation clss_clss: raw_clss "\<lambda>_. id"
    id "op \<in>#"
    by unfold_locales (auto simp: ac_simps)

  datatype LI =
    Learned nat | Init nat

  interpretation list_clss: raw_clss "\<lambda>_. mset"
    "\<lambda>L. mset (map mset L)" "\<lambda>L C. L \<in> set C"
    by unfold_locales (auto simp: ac_simps union_mset_list ex_mset)


  interpretation list_clss_nth: raw_clss "\<lambda>L i. mset (L ! i)"
    "\<lambda>L. mset (map mset L)"
    "\<lambda>i  C. C!i \<in> set C" 
    (* "\<lambda>i  C. C!i \<in> set C" "op #" "\<lambda>i C. remove_first (C!i) C" "op @"  *)
    apply unfold_locales
    apply (auto simp: ac_simps union_mset_list  ex_mset)[2]
    apply (metis in_set_conv_nth)
    done

  lemma distinct_entries_rbt[simp]: "distinct (RBT.entries C)"
    using distinct_entries[of C] by (metis distinct_zipI1 zip_map_fst_snd)

  lemma mset_entries_delete:
    assumes
      ab: "RBT.lookup C a = Some b"
    shows "mset (RBT.entries (RBT.delete a C)) = remove1_mset (a, b) (mset (RBT.entries C))"
  proof -
    { fix x y
      have "(x, y) \<in> set (RBT.entries (RBT.delete a C)) \<longleftrightarrow>
      (x, y) \<in> set (RBT.entries C) - {(a, b)}"
        using rbt_delete_in_tree[of "RBT.impl_of C" "x" "y" a] ab
        unfolding lookup_in_tree[symmetric]
        apply (auto split: if_splits simp: lookup_in_tree[symmetric])
        done
    }
    then show ?thesis
      by (auto simp: distinct_mset_remove1_All distinct_removeAll
        set_eq_iff_mset_eq_distinct[symmetric])
  qed
  abbreviation rbt_values where
  "rbt_values C \<equiv> snd ` set (RBT.entries C)"

  lemma subseteq_image_mset_minus:
    assumes NM: "N \<subseteq># M"
    shows "image_mset f (M - N) = image_mset f M - image_mset f N"
    using NM
  proof (induct N arbitrary: M)
    case empty
    then show ?case by simp
  next
    case (add N x) note IH = this(1) and NxM = this(2)
    have xM: "x \<in># M"
      using NxM by auto
    then obtain M' where M': "M = M' + {#x#}"
      by (meson mset_add)
    have MNx: "M - (N + {#x#}) = (M - {#x#}) - N"
      using xM by (auto simp: multiset_eq_iff)
    have NM: "N \<subseteq># M'"
      using M' NxM by auto
    show ?case
      unfolding multiset_eq_iff MNx
      apply (intro allI)
      by (auto simp: IH[OF NM] M')
  qed

  lemma image_mset_mset_removeAll: "a \<in># B \<Longrightarrow>
    {#f x. x \<in># remove1_mset a B#} =
      remove1_mset (f a) {#f x. x \<in># B#}"
    unfolding mset_remove1
    by (subst subseteq_image_mset_minus) (auto simp: subseteq_mset_def)

  interpretation list_clss_nth: raw_clss
    "\<lambda>L i. mset (the (RBT.lookup L i))"
    "\<lambda>L. mset (map (\<lambda>L. mset (snd L)) (RBT.entries L))"
    "\<lambda>i L. RBT.lookup L i \<noteq> None"
    apply unfold_locales
      apply auto[]
      apply (force simp add: lookup_in_tree)[]
     apply (fastforce simp: lookup_in_tree[symmetric])[]
    done
end

end