theory Array_Array_List
imports WB_More_IICF_SML
begin

subsection \<open>Array of Array Lists\<close>

text \<open>
  We define here array of array lists. We need arrays owning there elements. Therefore most of the
  rules introduced by \<open>sep_auto\<close> cannot lead to proofs.
\<close>

fun heap_list_all :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>heap_list_all R [] [] = emp\<close>
| \<open>heap_list_all R (x # xs) (y # ys) = R x y * heap_list_all R xs ys\<close>
| \<open>heap_list_all R _ _ = false\<close>

text \<open>It is often useful to speak about arrays except at one index (e.g., because it is updated).\<close>
definition heap_list_all_nth:: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> nat list \<Rightarrow>  'a list \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>heap_list_all_nth R is xs ys = foldr ((*)) (map (\<lambda>i. R (xs ! i) (ys ! i)) is) emp\<close>

lemma heap_list_all_nth_emty[simp]: \<open>heap_list_all_nth R [] xs ys = emp\<close>
  unfolding heap_list_all_nth_def by auto

lemma heap_list_all_nth_Cons:
  \<open>heap_list_all_nth R (a # is') xs ys = R (xs ! a) (ys ! a) * heap_list_all_nth R is' xs ys\<close>
  unfolding heap_list_all_nth_def by auto

lemma heap_list_all_heap_list_all_nth:
  \<open>length xs = length ys \<Longrightarrow> heap_list_all R xs ys = heap_list_all_nth R [0..< length xs] xs ys\<close>
proof (induction R xs ys rule: heap_list_all.induct)
  case (2 R x xs y ys) note IH = this
  then have IH: \<open>heap_list_all R xs ys = heap_list_all_nth R [0..<length xs] xs ys\<close>
    by auto
  have upt: \<open>[0..<length (x # xs)] = 0 # [1..<Suc (length xs)]\<close>
    by (simp add: upt_rec)
  have upt_map_Suc: \<open>[1..<Suc (length xs)] = map Suc [0..<length xs]\<close>
    by (induction xs) auto
  have map: \<open>(map (\<lambda>i. R ((x # xs) ! i) ((y # ys) ! i)) [1..<Suc (length xs)]) =
    (map (\<lambda>i. R (xs ! i) (ys ! i)) [0..< (length xs)])\<close>
    unfolding upt_map_Suc map_map by auto
  have 1: \<open>heap_list_all_nth R [0..<length (x # xs)] (x # xs) (y # ys) =
    R x y * heap_list_all_nth R [0..<length xs] xs ys\<close>
    unfolding heap_list_all_nth_def upt
    by (simp only: list.map foldr.simps map) auto
  show ?case
    using IH unfolding 1 by auto
qed auto

lemma heap_list_all_nth_single: \<open>heap_list_all_nth R [a] xs ys = R (xs ! a) (ys ! a)\<close>
  by (auto simp: heap_list_all_nth_def)

lemma heap_list_all_nth_mset_eq:
  assumes \<open>mset is = mset is'\<close>
  shows \<open>heap_list_all_nth R is xs ys = heap_list_all_nth R is' xs ys\<close>
  using assms
proof (induction "is'" arbitrary: "is")
  case Nil
  then show ?case by auto
next
  case (Cons a is') note IH = this(1) and eq_is = this(2)
  from eq_is have \<open>a \<in> set is\<close>
    by (fastforce dest: mset_eq_setD)
  then obtain ixs iys where
    "is": \<open>is = ixs @ a # iys\<close>
    using eq_is by (meson split_list)
  then have H: \<open>heap_list_all_nth R (ixs @ iys) xs ys = heap_list_all_nth R is' xs ys\<close>
    using IH[of \<open>ixs @ iys\<close>] eq_is by auto
  have H': \<open>heap_list_all_nth R (ixs @ a # iys) xs ys = heap_list_all_nth R (a # ixs @ iys) xs ys\<close>
    for xs ys
    by (induction ixs)(auto simp: heap_list_all_nth_Cons star_aci(3))
  show ?case
    using H[symmetric] by (auto simp: heap_list_all_nth_Cons "is" H')
qed

lemma heap_list_add_same_length:
  \<open>h \<Turnstile> heap_list_all R' xs p \<Longrightarrow> length p = length xs\<close>
  by (induction R' xs p arbitrary: h rule: heap_list_all.induct) (auto elim!: mod_starE)

lemma heap_list_all_nth_Suc:
  assumes a: \<open>a > 1\<close>
  shows \<open>heap_list_all_nth R [Suc 0..<a] (x # xs) (y # ys) =
    heap_list_all_nth R [0..<a-1] xs ys\<close>
proof -
  have upt: \<open>[0..< a] = 0 # [1..< a]\<close>
    using a by (simp add: upt_rec)
  have upt_map_Suc: \<open>[Suc 0..<a] = map Suc [0..< a-1]\<close>
    using a by (auto simp: map_Suc_upt)
  have map: \<open>(map (\<lambda>i. R ((x # xs) ! i) ((y # ys) ! i)) [Suc 0..<a]) =
    (map (\<lambda>i. R (xs ! i) (ys ! i)) [0..<a-1])\<close>
    unfolding upt_map_Suc map_map by auto
  show ?thesis
    unfolding heap_list_all_nth_def unfolding map ..
qed

lemma heap_list_all_nth_append:
  \<open>heap_list_all_nth R (is @ is') xs ys = heap_list_all_nth R is xs ys * heap_list_all_nth R is' xs ys\<close>
  by (induction "is") (auto simp: heap_list_all_nth_Cons star_aci)

lemma heap_list_all_heap_list_all_nth_eq:
  \<open>heap_list_all R xs ys = heap_list_all_nth R [0..< length xs] xs ys * \<up>(length xs = length ys)\<close>
  by (induction R xs ys rule: heap_list_all.induct)
    (auto simp del: upt_Suc upt_Suc_append
      simp: upt_rec[of 0] heap_list_all_nth_single star_aci(3)
      heap_list_all_nth_Cons heap_list_all_nth_Suc)

lemma heap_list_all_nth_remove1: \<open>i \<in> set is \<Longrightarrow>
  heap_list_all_nth R is xs ys = R (xs ! i) (ys ! i) * heap_list_all_nth R (remove1 i is) xs ys\<close>
  using heap_list_all_nth_mset_eq[of \<open>is\<close> \<open>i # remove1 i is\<close>]
  by (auto simp: heap_list_all_nth_Cons)

definition arrayO_assn :: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b array \<Rightarrow> assn\<close> where
  \<open>arrayO_assn R' xs axs \<equiv> \<exists>\<^sub>A p. array_assn id_assn p axs * heap_list_all R' xs p\<close>

definition arrayO_except_assn:: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'b array \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>arrayO_except_assn R' is xs axs f \<equiv>
     \<exists>\<^sub>A p. array_assn id_assn p axs * heap_list_all_nth R' (fold remove1 is [0..<length xs]) xs p *
    \<up> (length xs = length p) * f p\<close>

lemma arrayO_except_assn_array0: \<open>arrayO_except_assn R [] xs asx (\<lambda>_. emp) = arrayO_assn R xs asx\<close>
proof -
  have \<open>(h \<Turnstile> array_assn id_assn p asx * heap_list_all_nth R [0..<length xs] xs p \<and> length xs = length p) =
    (h \<Turnstile> array_assn id_assn p asx * heap_list_all R xs p)\<close> (is \<open>?a = ?b\<close>) for h p
  proof (rule iffI)
    assume ?a
    then show ?b
      by (auto simp: heap_list_all_heap_list_all_nth)
  next
    assume ?b
    then have \<open>length xs = length p\<close>
      by (auto simp: heap_list_add_same_length mod_star_conv)
    then show ?a
      using \<open>?b\<close>
        by (auto simp: heap_list_all_heap_list_all_nth)
    qed
  then show ?thesis
    unfolding arrayO_except_assn_def arrayO_assn_def by (auto simp: ex_assn_def)
qed

lemma arrayO_except_assn_array0_index:
  \<open>i < length xs \<Longrightarrow> arrayO_except_assn R [i] xs asx (\<lambda>p. R (xs ! i) (p ! i)) = arrayO_assn R xs asx\<close>
  unfolding arrayO_except_assn_array0[symmetric] arrayO_except_assn_def
  using heap_list_all_nth_remove1[of i \<open>[0..<length xs]\<close> R xs] by (auto simp: star_aci(2,3))

lemma arrayO_nth_rule[sep_heap_rules]:
  assumes i: \<open>i < length a\<close>
  shows \<open> <arrayO_assn (arl_assn R) a ai> Array.nth ai i <\<lambda>r. arrayO_except_assn (arl_assn R) [i] a ai
   (\<lambda>r'. arl_assn R (a ! i) r * \<up>(r = r' ! i))>\<close>
proof -
  have i_le: \<open>i < Array.length h ai\<close> if \<open>(h, as) \<Turnstile> arrayO_assn (arl_assn R) a ai\<close> for h as
    using that i unfolding arrayO_assn_def array_assn_def is_array_def
    by (auto simp: run.simps tap_def arrayO_assn_def
        mod_star_conv array_assn_def is_array_def
        Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
  have A: \<open>Array.get h ai ! i = p ! i\<close> if \<open>(h, as) \<Turnstile>
       array_assn id_assn p ai *
       heap_list_all_nth (arl_assn R) (remove1 i [0..<length p]) a p *
       arl_assn R (a ! i) (p ! i)\<close>
    for as p h
    using that
    by (auto simp: mod_star_conv array_assn_def is_array_def Array.get_def snga_assn_def
        Abs_assn_inverse)
  show ?thesis
    unfolding hoare_triple_def Let_def
    apply (clarify, intro allI impI conjI)
    using assms A
       apply (auto simp: hoare_triple_def Let_def i_le execute_simps relH_def in_range.simps
        arrayO_except_assn_array0_index[of i, symmetric]
        elim!: run_elims
        intro!: norm_pre_ex_rule)
    apply (auto simp: arrayO_except_assn_def)
    done
qed

definition length_a :: \<open>'a::heap array \<Rightarrow> nat Heap\<close> where
  \<open>length_a xs = Array.len xs\<close>

lemma length_a_rule[sep_heap_rules]:
   \<open><arrayO_assn R x xi> length_a xi <\<lambda>r. arrayO_assn R x xi * \<up>(r = length x)>\<^sub>t\<close>
  by (sep_auto simp: arrayO_assn_def length_a_def array_assn_def is_array_def mod_star_conv
      dest: heap_list_add_same_length)

lemma length_a_hnr[sepref_fr_rules]:
  \<open>(length_a, RETURN o op_list_length) \<in> (arrayO_assn R)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

definition length_ll :: \<open>'a list list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>length_ll l i = length (l!i)\<close>

lemma le_length_ll_nemptyD: \<open>b < length_ll a ba \<Longrightarrow> a ! ba \<noteq> []\<close>
  by (auto simp: length_ll_def)

definition length_aa :: \<open>('a::heap array_list) array \<Rightarrow> nat \<Rightarrow> nat Heap\<close> where
  \<open>length_aa xs i = do {
     x \<leftarrow> Array.nth xs i;
    arl_length x}\<close>

lemma length_aa_rule[sep_heap_rules]:
  \<open>b < length xs \<Longrightarrow> <arrayO_assn (arl_assn R) xs a> length_aa a b
   <\<lambda>r. arrayO_assn (arl_assn R) xs a * \<up> (r = length_ll xs b)>\<^sub>t\<close>
  unfolding length_aa_def
  apply sep_auto
  apply (sep_auto simp: arrayO_except_assn_def arl_length_def arl_assn_def
      eq_commute[of \<open>(_, _)\<close>] hr_comp_def length_ll_def)
   apply (sep_auto simp: arrayO_except_assn_def arl_length_def arl_assn_def
      eq_commute[of \<open>(_, _)\<close>] is_array_list_def hr_comp_def length_ll_def list_rel_def
      dest: list_all2_lengthD)[]
  unfolding arrayO_assn_def[symmetric] arl_assn_def[symmetric]
  apply (subst arrayO_except_assn_array0_index[symmetric, of b])
   apply simp
  unfolding arrayO_except_assn_def arl_assn_def hr_comp_def
  apply sep_auto
  done

lemma length_aa_hnr[sepref_fr_rules]: \<open>(uncurry length_aa, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare sep_auto

definition nth_aa where
  \<open>nth_aa xs i j = do {
      x \<leftarrow> Array.nth xs i;
      y \<leftarrow> arl_get x j;
      return y}\<close>

lemma models_heap_list_all_models_nth:
  \<open>(h, as) \<Turnstile> heap_list_all R a b \<Longrightarrow> i < length a \<Longrightarrow> \<exists>as'. (h, as') \<Turnstile> R (a!i) (b!i)\<close>
  by (induction R a b arbitrary: as i rule: heap_list_all.induct)
    (auto simp: mod_star_conv nth_Cons elim!: less_SucE split: nat.splits)

definition nth_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  \<open>nth_ll l i j = l ! i ! j\<close>

lemma nth_aa_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_ll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_ll l i]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow>
       b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
  apply sepref_to_hoare
  apply (subst (2) arrayO_except_assn_array0_index[symmetric])
    apply (solves \<open>auto\<close>)[]
  apply (sep_auto simp: nth_aa_def nth_ll_def length_ll_def)
    apply (sep_auto simp: arrayO_except_assn_def arrayO_assn_def arl_assn_def hr_comp_def list_rel_def
        list_all2_lengthD
      star_aci(3) R R' pure_def H)
    done
qed

definition append_el_aa :: "('a::{default,heap} array_list) array \<Rightarrow>
  nat \<Rightarrow> 'a \<Rightarrow> ('a array_list) array Heap"where
"append_el_aa \<equiv> \<lambda>a i x. do {
  j \<leftarrow> Array.nth a i;
  a' \<leftarrow> arl_append j x;
  Array.upd i a' a
  }"

definition append_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  \<open>append_ll xs i x = list_update xs i (xs ! i @ [x])\<close>

lemma sep_auto_is_stupid:
  fixes R :: \<open>'a \<Rightarrow> 'b::{heap,default} \<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close>
  shows
    \<open><\<exists>\<^sub>Ap. R1 p * R2 p * arl_assn R l' aa * R x x' * R4 p>
       arl_append aa x' <\<lambda>r. (\<exists>\<^sub>Ap. arl_assn R (l' @ [x]) r * R1 p * R2 p * R x x' * R4 p * true) >\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have bbi: \<open>(x', x) \<in> the_pure R\<close> if
    \<open>(aa, bb) \<Turnstile> is_array_list (ba @ [x']) (a, baa) * R1 p * R2 p * pure R' x x' * R4 p * true\<close>
    for aa bb a ba baa p
    using that by (auto simp: mod_star_conv R R')
  show ?thesis
    unfolding arl_assn_def hr_comp_def
    by (sep_auto simp: list_rel_def R R' intro!: list_all2_appendI dest!: bbi)
qed

declare arrayO_nth_rule[sep_heap_rules]

lemma heap_list_all_nth_cong:
  assumes
    \<open>\<forall>i \<in> set is. xs ! i = xs' ! i\<close> and
    \<open>\<forall>i \<in> set is. ys ! i = ys' ! i\<close>
  shows \<open>heap_list_all_nth R is xs ys = heap_list_all_nth R is xs' ys'\<close>
  using assms by (induction \<open>is\<close>) (auto simp: heap_list_all_nth_Cons)

lemma append_aa_hnr[sepref_fr_rules]:
  fixes R ::  \<open>'a \<Rightarrow> 'b :: {heap, default} \<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 append_el_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> append_ll)) \<in>
     [\<lambda>((l,i),x). i < length l]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_assn (arl_assn R))\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(\<exists>\<^sub>Ax. arrayO_assn (arl_assn R) a ai * R x r * true * \<up> (x = a ! ba ! b)) =
     (arrayO_assn (arl_assn R) a ai * R (a ! ba ! b) r * true)\<close> for a ai ba b r
    by (auto simp: ex_assn_def)
  show ?thesis \<comment> \<open>TODO tune proof\<close>
    apply sepref_to_hoare
    apply (sep_auto simp: append_el_aa_def)
     apply (simp add: arrayO_except_assn_def)
     apply (rule sep_auto_is_stupid[OF p])
    apply (sep_auto simp: array_assn_def is_array_def append_ll_def)
    apply (simp add: arrayO_except_assn_array0[symmetric] arrayO_except_assn_def)
    apply (subst_tac (2) i = ba in heap_list_all_nth_remove1)
     apply (solves \<open>simp\<close>)
    apply (simp add: array_assn_def is_array_def)
    apply (rule_tac x=\<open>p[ba := (ab, bc)]\<close> in ent_ex_postI)
    apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
      apply (solves \<open>auto\<close>)[2]
    apply (auto simp: star_aci)
    done
qed

definition update_aa :: "('a::{heap} array_list) array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a array_list) array Heap" where
  \<open>update_aa a i j y = do {
      x \<leftarrow> Array.nth a i;
      a' \<leftarrow> arl_set x j y;
      Array.upd i a' a
    }\<close> \<comment> \<open>is the Array.upd really needed?\<close>

definition update_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  \<open>update_ll xs i j y = xs[i:= (xs ! i)[j := y]]\<close>

declare nth_rule[sep_heap_rules del]
declare arrayO_nth_rule[sep_heap_rules]

text \<open>TODO: is it possible to be more precise and not drop the \<^term>\<open>\<up> ((aa, bc) = r' ! bb)\<close>\<close>
lemma arrayO_except_assn_arl_set[sep_heap_rules]:
  fixes R :: \<open>'a \<Rightarrow> 'b :: {heap}\<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and
    \<open>ba < length_ll a bb\<close>
  shows \<open>
       <arrayO_except_assn (arl_assn R) [bb] a ai (\<lambda>r'. arl_assn R (a ! bb) (aa, bc) *
         \<up> ((aa, bc) = r' ! bb)) * R b bi>
       arl_set (aa, bc) ba bi
      <\<lambda>(aa, bc). arrayO_except_assn (arl_assn R) [bb] a ai
        (\<lambda>r'. arl_assn R ((a ! bb)[ba := b]) (aa, bc)) * R b bi * true>\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
    using assms
    apply (sep_auto simp: arrayO_except_assn_def arl_assn_def hr_comp_def list_rel_imp_same_length
        list_rel_update length_ll_def)
    done
qed

lemma update_aa_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and \<open>ba < length_ll a bb\<close>
  shows \<open><R b bi * arrayO_assn (arl_assn R) a ai> update_aa ai bb ba bi
      <\<lambda>r. R b bi * (\<exists>\<^sub>Ax. arrayO_assn (arl_assn R) x r * \<up> (x = update_ll a bb ba b))>\<^sub>t\<close>
    using assms
  apply (sep_auto simp add: update_aa_def update_ll_def p)
  apply (sep_auto simp add: update_aa_def arrayO_except_assn_def array_assn_def is_array_def hr_comp_def)
  apply (subst_tac i=bb in arrayO_except_assn_array0_index[symmetric])
   apply (solves \<open>simp\<close>)
  apply (subst arrayO_except_assn_def)
  apply (auto simp add: update_aa_def arrayO_except_assn_def array_assn_def is_array_def hr_comp_def)

  apply (rule_tac x=\<open>p[bb := (aa, bc)]\<close> in ent_ex_postI)
  apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
    apply (solves \<open>auto\<close>)
   apply (solves \<open>auto\<close>)
  apply (auto simp: star_aci)
  done

lemma update_aa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 update_aa, uncurry3 (RETURN oooo update_ll)) \<in>
     [\<lambda>(((l,i), j), x). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  by sepref_to_hoare (sep_auto simp: assms)

definition set_butlast_ll where
  \<open>set_butlast_ll xs i = xs[i := butlast (xs ! i)]\<close>

definition set_butlast_aa :: "('a::{heap} array_list) array \<Rightarrow> nat \<Rightarrow> ('a array_list) array Heap" where
  \<open>set_butlast_aa a i = do {
      x \<leftarrow> Array.nth a i;
      a' \<leftarrow> arl_butlast x;
      Array.upd i a' a
    }\<close> \<comment> \<open>Replace the \<^term>\<open>i\<close>-th element by the itself except the last element.\<close>

lemma list_rel_butlast:
  assumes rel: \<open>(xs, ys) \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(butlast xs, butlast ys) \<in> \<langle>R\<rangle>list_rel\<close>
proof -
  have \<open>length xs = length ys\<close>
    using assms list_rel_imp_same_length by blast
  then show ?thesis
    using rel
    by (induction xs ys rule: list_induct2) (auto split: nat.splits)
qed

lemma arrayO_except_assn_arl_butlast:
  assumes \<open>b < length a\<close> and
    \<open>a ! b \<noteq> []\<close>
  shows
    \<open><arrayO_except_assn (arl_assn R) [b] a ai (\<lambda>r'. arl_assn R (a ! b) (aa, ba) *
         \<up> ((aa, ba) = r' ! b))>
       arl_butlast (aa, ba)
     <\<lambda>(aa, ba). arrayO_except_assn (arl_assn R) [b] a ai (\<lambda>r'. arl_assn R (butlast (a ! b)) (aa, ba)* true)>\<close>
proof -
  show ?thesis
    using assms
    apply (subst (1) arrayO_except_assn_def)
    apply (sep_auto simp: arl_assn_def hr_comp_def list_rel_imp_same_length
        list_rel_update
        intro: list_rel_butlast)
    apply (subst (1) arrayO_except_assn_def)
    apply (rule_tac x=\<open>p\<close> in ent_ex_postI)
    apply (sep_auto intro: list_rel_butlast)
    done
qed

lemma set_butlast_aa_rule[sep_heap_rules]:
  assumes \<open>is_pure R\<close> and
    \<open>b < length a\<close> and
    \<open>a ! b \<noteq> []\<close>
  shows \<open><arrayO_assn (arl_assn R) a ai> set_butlast_aa ai b
       <\<lambda>r. (\<exists>\<^sub>Ax. arrayO_assn (arl_assn R) x r * \<up> (x = set_butlast_ll a b))>\<^sub>t\<close>
proof -
  note arrayO_except_assn_arl_butlast[sep_heap_rules]
  note arl_butlast_rule[sep_heap_rules del]
  have \<open>\<And>b bi.
       b < length a \<Longrightarrow>
       a ! b \<noteq> [] \<Longrightarrow>
       a ::\<^sub>i TYPE('a list list) \<Longrightarrow>
       b ::\<^sub>i TYPE(nat) \<Longrightarrow>
       nofail (RETURN (set_butlast_ll a b)) \<Longrightarrow>
       <\<up> ((bi, b) \<in> nat_rel) *
        arrayO_assn (arl_assn R) a
         ai> set_butlast_aa ai
              bi <\<lambda>r. \<up> ((bi, b) \<in> nat_rel) *
                       true *
                       (\<exists>\<^sub>Ax.
  arrayO_assn (arl_assn R) x r *
  \<up> (RETURN x \<le> RETURN (set_butlast_ll a b)))>\<^sub>t\<close>
    apply (sep_auto simp add: set_butlast_aa_def set_butlast_ll_def assms)

    apply (sep_auto simp add: set_butlast_aa_def arrayO_except_assn_def array_assn_def is_array_def
        hr_comp_def)
    apply (subst_tac i=b in arrayO_except_assn_array0_index[symmetric])
     apply (solves \<open>simp\<close>)
    apply (subst arrayO_except_assn_def)
    apply (auto simp add: set_butlast_aa_def arrayO_except_assn_def array_assn_def is_array_def hr_comp_def)

    apply (rule_tac x=\<open>p[b := (aa, ba)]\<close> in ent_ex_postI)
    apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
      apply (solves \<open>auto\<close>)
     apply (solves \<open>auto\<close>)
    apply (solves \<open>auto\<close>)
    done
  then show ?thesis
    using assms by sep_auto
qed

lemma set_butlast_aa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry set_butlast_aa, uncurry (RETURN oo set_butlast_ll)) \<in>
     [\<lambda>(l,i). i < length l \<and> l ! i \<noteq> []]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  using assms by sepref_to_hoare sep_auto

definition last_aa :: "('a::heap array_list) array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  \<open>last_aa xs i = do {
     x \<leftarrow> Array.nth xs i;
     arl_last x
  }\<close>

definition last_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> 'a" where
  \<open>last_ll xs i = last (xs ! i)\<close>

lemma last_aa_rule[sep_heap_rules]:
  assumes
    p: \<open>is_pure R\<close> and
   \<open>b < length a\<close> and
   \<open>a ! b \<noteq> []\<close>
   shows \<open>
       <arrayO_assn (arl_assn R) a ai>
         last_aa ai b
       <\<lambda>r. arrayO_assn (arl_assn R) a ai * (\<exists>\<^sub>Ax. R x r * \<up> (x = last_ll a b))>\<^sub>t\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  note arrayO_except_assn_arl_butlast[sep_heap_rules]
  note arl_butlast_rule[sep_heap_rules del]
  have \<open>\<And>b.
       b < length a \<Longrightarrow>
       a ! b \<noteq> [] \<Longrightarrow>
       <arrayO_assn (arl_assn R) a ai>
         last_aa ai b
       <\<lambda>r. arrayO_assn (arl_assn R) a ai * (\<exists>\<^sub>Ax. R x r * \<up> (x = last_ll a b))>\<^sub>t\<close>
    apply (sep_auto simp add: last_aa_def last_ll_def assms)

    apply (sep_auto simp add: last_aa_def arrayO_except_assn_def array_assn_def is_array_def
        hr_comp_def arl_assn_def)
    apply (subst_tac i=b in arrayO_except_assn_array0_index[symmetric])
     apply (solves \<open>simp\<close>)
    apply (subst arrayO_except_assn_def)
    apply (auto simp add: last_aa_def arrayO_except_assn_def array_assn_def is_array_def hr_comp_def)

    apply (rule_tac x=\<open>p\<close> in ent_ex_postI)
    apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
      apply (solves \<open>auto\<close>)
     apply (solves \<open>auto\<close>)

    apply (rule_tac x=\<open>bb\<close> in ent_ex_postI)
    unfolding R unfolding R'
    apply (sep_auto simp: pure_def param_last)
    done
  from this[of b] show ?thesis
    using assms unfolding R' by blast
qed

lemma last_aa_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows \<open>(uncurry last_aa, uncurry (RETURN oo last_ll)) \<in>
     [\<lambda>(l,i). i < length l \<and> l ! i \<noteq> []]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  note arrayO_except_assn_arl_butlast[sep_heap_rules]
  note arl_butlast_rule[sep_heap_rules del]
  show ?thesis
    using assms by sepref_to_hoare sep_auto
qed

definition nth_a :: \<open>('a::heap array_list) array \<Rightarrow> nat \<Rightarrow> ('a array_list) Heap\<close> where
 \<open>nth_a xs i = do {
     x \<leftarrow> Array.nth xs i;
     arl_copy x}\<close>

lemma nth_a_hnr[sepref_fr_rules]:
  \<open>(uncurry nth_a, uncurry (RETURN oo op_list_get)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> arl_assn R\<close>
  unfolding nth_a_def
  apply sepref_to_hoare
  subgoal for b b' xs a \<comment> \<open>TODO proof\<close>
    apply sep_auto
    apply (subst arrayO_except_assn_array0_index[symmetric, of b])
     apply simp
    apply (sep_auto simp: arrayO_except_assn_def arl_length_def arl_assn_def
        eq_commute[of \<open>(_, _)\<close>] hr_comp_def length_ll_def)
    done
  done

 definition swap_aa :: "('a::heap array_list) array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a array_list) array Heap" where
  \<open>swap_aa xs k i j = do {
    xi \<leftarrow> nth_aa xs k i;
    xj \<leftarrow> nth_aa xs k j;
    xs \<leftarrow> update_aa xs k i xj;
    xs \<leftarrow> update_aa xs k j xi;
    return xs
  }\<close>

definition swap_ll where
  \<open>swap_ll xs k i j = list_update xs k (swap (xs!k) i j)\<close>

lemma nth_aa_heap[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>b < length aa\<close> and \<open>ba < length_ll aa b\<close>
  shows \<open>
   <arrayO_assn (arl_assn R) aa a>
   nth_aa a b ba
   <\<lambda>r. \<exists>\<^sub>Ax. arrayO_assn (arl_assn R) aa a *
               (R x r *
                \<up> (x = nth_ll aa b ba)) *
               true>\<close>
proof -
  have \<open><arrayO_assn (arl_assn R) aa a *
        nat_assn b b *
        nat_assn ba ba>
       nth_aa a b ba
       <\<lambda>r. \<exists>\<^sub>Ax. arrayO_assn (arl_assn R) aa a *
                   nat_assn b b *
                   nat_assn ba ba *
                   R x r *
                   true *
                   \<up> (x = nth_ll aa b ba)>\<close>
    using p assms nth_aa_hnr[of R] unfolding hfref_def hn_refine_def
    by auto
  then show ?thesis
    unfolding hoare_triple_def
    by (auto simp: Let_def pure_def)
qed

lemma update_aa_rule_pure:
  assumes p: \<open>is_pure R\<close> and \<open>b < length aa\<close> and \<open>ba < length_ll aa b\<close> and
    b: \<open>(bb, be) \<in> the_pure R\<close>
  shows \<open>
   <arrayO_assn (arl_assn R) aa a>
           update_aa a b ba bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arrayO_assn (arl_assn R)) aa a * arrayO_assn (arl_assn R) x r *
                       true *
                       \<up> (x = update_ll aa b ba be)>\<close>
proof -
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using p by fastforce
  have bb: \<open>pure R' be bb = \<up>((bb, be) \<in> R')\<close>
    by (auto simp: pure_def)
  have \<open> <arrayO_assn (arl_assn R) aa a * nat_assn b b * nat_assn ba ba * R be bb>
           update_aa a b ba bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arrayO_assn (arl_assn R)) aa a * nat_assn b b * nat_assn ba ba *
                       R be bb *
                       arrayO_assn (arl_assn R) x r *
                       true *
                       \<up> (x = update_ll aa b ba be)>\<close>
    using p assms update_aa_hnr[of R] unfolding hfref_def hn_refine_def
    by auto
  then show ?thesis
    using b unfolding R'[symmetric] unfolding hoare_triple_def RR' bb
    by (auto simp: Let_def pure_def)
qed

lemma length_update_ll[simp]: \<open>length (update_ll a bb b c) = length a\<close>
  unfolding update_ll_def by auto

lemma length_ll_update_ll:
  \<open>bb < length a \<Longrightarrow> length_ll (update_ll a bb b c) bb = length_ll a bb\<close>
  unfolding length_ll_def update_ll_def by auto

lemma swap_aa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 swap_aa, uncurry3 (RETURN oooo swap_ll)) \<in>
   [\<lambda>(((xs, k), i), j). k < length xs \<and> i < length_ll xs k \<and> j < length_ll xs k]\<^sub>a
  (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> (arrayO_assn (arl_assn R))\<close>
proof -
  note update_aa_rule_pure[sep_heap_rules]
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using assms by fastforce
  have [simp]: \<open>the_pure (\<lambda>a b. \<up> ((b, a) \<in> R')) = R'\<close>
    unfolding pure_def[symmetric] by auto
  show ?thesis
    using assms unfolding R'[symmetric] unfolding RR'
    apply sepref_to_hoare
    apply (sep_auto simp: swap_aa_def swap_ll_def arrayO_except_assn_def
        length_ll_update_ll)
    by (sep_auto simp: update_ll_def swap_def nth_ll_def list_update_swap)
qed

text \<open>It is not possible to do a direct initialisation: there is no element that can be put
  everywhere.\<close>
definition arrayO_ara_empty_sz where
  \<open>arrayO_ara_empty_sz n =
   (let xs = fold (\<lambda>_ xs. [] # xs) [0..<n] [] in
    op_list_copy xs)
   \<close>

lemma heap_list_all_list_assn: \<open>heap_list_all R x y = list_assn R x y\<close>
  by (induction R x y rule: heap_list_all.induct) auto

lemma of_list_op_list_copy_arrayO[sepref_fr_rules]:
   \<open>(Array.of_list, RETURN \<circ> op_list_copy) \<in> (list_assn (arl_assn R))\<^sup>d \<rightarrow>\<^sub>a arrayO_assn (arl_assn R)\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: arrayO_assn_def array_assn_def)
  apply (rule_tac ?psi=\<open>xa \<mapsto>\<^sub>a xi * list_assn (arl_assn R) x xi \<Longrightarrow>\<^sub>A
       is_array xi xa * heap_list_all (arl_assn R) x xi * true\<close> in asm_rl)
  by (sep_auto simp: heap_list_all_list_assn is_array_def)

sepref_definition
  arrayO_ara_empty_sz_code
  is "RETURN o arrayO_ara_empty_sz"
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a arrayO_assn (arl_assn (R::'a \<Rightarrow> 'b::{heap, default} \<Rightarrow> assn))\<close>
  unfolding arrayO_ara_empty_sz_def op_list_empty_def[symmetric]
  apply (rewrite at \<open>(#) \<hole>\<close> op_arl_empty_def[symmetric])
  apply (rewrite at \<open>fold _ _ \<hole>\<close> op_HOL_list_empty_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref


definition init_lrl :: \<open>nat \<Rightarrow> 'a list list\<close> where
  \<open>init_lrl n = replicate n []\<close>

lemma arrayO_ara_empty_sz_init_lrl: \<open>arrayO_ara_empty_sz n = init_lrl n\<close>
  by (induction n) (auto simp: arrayO_ara_empty_sz_def init_lrl_def)

lemma arrayO_raa_empty_sz_init_lrl[sepref_fr_rules]:
  \<open>(arrayO_ara_empty_sz_code, RETURN o init_lrl) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a arrayO_assn (arl_assn R)\<close>
  using arrayO_ara_empty_sz_code.refine unfolding arrayO_ara_empty_sz_init_lrl .


definition (in -) shorten_take_ll where
  \<open>shorten_take_ll L j W = W[L := take j (W ! L)]\<close>

definition (in -) shorten_take_aa where
  \<open>shorten_take_aa L j W =  do {
      (a, n) \<leftarrow> Array.nth W L;
      Array.upd L (a, j) W
    }\<close>


lemma Array_upd_arrayO_except_assn[sep_heap_rules]:
  assumes
    \<open>ba \<le> length (b ! a)\<close> and
    \<open>a < length b\<close>
  shows \<open><arrayO_except_assn (arl_assn R) [a] b bi
           (\<lambda>r'. arl_assn R (b ! a) (aaa, n) * \<up> ((aaa, n) = r' ! a))>
         Array.upd a (aaa, ba) bi
         <\<lambda>r. \<exists>\<^sub>Ax. arrayO_assn (arl_assn R) x r * true *
                    \<up> (x = b[a := take ba (b ! a)])>\<close>
proof -
  have [simp]: \<open>ba \<le> length l'\<close>
    if
      \<open>ba \<le> length (b ! a)\<close> and
      aa: \<open>(take n l', b ! a) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    for l' :: \<open>'b list\<close>
  proof -
    show ?thesis
      using list_rel_imp_same_length[OF aa] that
      by auto
  qed
  have [simp]: \<open>(take ba l', take ba (b ! a)) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    if
      \<open>ba \<le> length (b ! a)\<close> and
      \<open>n \<le> length l'\<close> and
      take: \<open>(take n l', b ! a) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    for l' :: \<open>'b list\<close>
  proof -
    have [simp]: \<open>n = length (b ! a)\<close>
      using list_rel_imp_same_length[OF take] that by auto
    have 1: \<open>take ba l' = take ba (take n l')\<close>
      using that by (auto simp: min_def)
    show ?thesis
      using take
      unfolding 1
      by (rule list_rel_take)
  qed

  have [simp]: \<open>heap_list_all_nth (arl_assn R) (remove1 a [0..<length p])
           (b[a := take ba (b ! a)]) (p[a := (aaa, ba)]) =
        heap_list_all_nth (arl_assn R) (remove1 a [0..<length p]) b p\<close>
    for p :: \<open>('b array \<times> nat) list\<close> and l' :: \<open>'b list\<close>
  proof -
    show ?thesis
      by (rule heap_list_all_nth_cong) auto
  qed

  show ?thesis
    using assms
    unfolding arrayO_except_assn_def
    apply (subst (2) arl_assn_def)
    apply (subst is_array_list_def[abs_def])
    apply (subst hr_comp_def[abs_def])
    apply (subst array_assn_def)
    apply (subst is_array_def[abs_def])
    apply (subst hr_comp_def[abs_def])
    apply sep_auto
    apply (subst arrayO_except_assn_array0_index[symmetric, of a])
    apply (solves simp)
    unfolding arrayO_except_assn_def array_assn_def is_array_def
    apply (subst (3) arl_assn_def)
    apply (subst is_array_list_def[abs_def])
    apply (subst (2) hr_comp_def[abs_def])
    apply (subst ex_assn_move_out)+
    apply (rule_tac x=\<open>p[a := (aaa, ba)]\<close> in ent_ex_postI)
    apply (rule_tac x=\<open>take ba l'\<close> in ent_ex_postI)
    by (sep_auto simp: )
qed

lemma shorten_take_aa_hnr[sepref_fr_rules]:
  \<open>(uncurry2 shorten_take_aa, uncurry2 (RETURN ooo shorten_take_ll)) \<in>
     [\<lambda>((L, j), W). j \<le> length (W ! L) \<and> L < length W]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d \<rightarrow> arrayO_assn (arl_assn R)\<close>
  unfolding shorten_take_aa_def shorten_take_ll_def
  by sepref_to_hoare sep_auto

end
