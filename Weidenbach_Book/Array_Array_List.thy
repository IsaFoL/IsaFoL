theory Array_Array_List
imports IICF
begin

fun heap_list_all :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>heap_list_all R [] [] = emp\<close>
| \<open>heap_list_all R (x # xs) (y # ys) = R x y * heap_list_all R xs ys\<close>
| \<open>heap_list_all R _ _ = false\<close>

definition heap_list_all_nth:: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> nat list \<Rightarrow>  'a list \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>heap_list_all_nth R is xs ys = foldr (op *) (map (\<lambda>i. R (xs ! i) (ys ! i)) is) emp\<close>

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
    using eq_is  by (meson split_list)
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
    (auto simp del: upt_Suc simp: upt_rec[of 0] heap_list_all_nth_single star_aci(3)
      heap_list_all_nth_Cons heap_list_all_nth_Suc)

lemma heap_list_all_nth_remove1: \<open>i \<in> set is \<Longrightarrow>
  heap_list_all_nth R is xs ys = R (xs ! i) (ys ! i) * heap_list_all_nth R (remove1 i is) xs ys\<close>
  using heap_list_all_nth_mset_eq[of \<open>is\<close> \<open>i # remove1 i is\<close>]
  by (auto simp: heap_list_all_nth_Cons)

definition arrayO:: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b array \<Rightarrow> assn\<close> where
  \<open>arrayO R' xs axs \<equiv> \<exists>\<^sub>A p. array_assn id_assn p axs * heap_list_all R' xs p\<close>

definition arrayO_except:: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'b array \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>arrayO_except R' is xs axs f \<equiv>
     \<exists>\<^sub>A p. array_assn id_assn p axs * heap_list_all_nth R' (fold remove1 is [0..<length xs]) xs p *
    \<up> (length xs = length p) * f p\<close>

lemma arrayO_except_array0: \<open>arrayO_except R [] xs asx (\<lambda>_. emp) = arrayO R xs asx\<close>
proof -
  have \<open>(h \<Turnstile> array_assn id_assn p asx * heap_list_all_nth R [0..<length xs] xs p \<and> length xs = length p) =
    (h \<Turnstile> array_assn id_assn p asx * heap_list_all R xs p)\<close> (is \<open>?a = ?b\<close>) for h p
  proof (rule iffI)
    assume ?a
    then show ?b
      by (auto simp: (* heap_list_add_same_length *) heap_list_all_heap_list_all_nth)
  next
    assume ?b
    then have \<open>length xs = length p\<close>
      by (auto simp: heap_list_add_same_length mod_star_conv)
    then show ?a
      using \<open>?b\<close>
        by (auto simp: heap_list_all_heap_list_all_nth)
    qed
  then show ?thesis
    unfolding arrayO_except_def arrayO_def by (auto simp: ex_assn_def)
qed

lemma arrayO_except_array0_index: \<open>i < length xs \<Longrightarrow> arrayO_except R [i] xs asx (\<lambda>p. R (xs ! i) (p ! i)) = arrayO R xs asx\<close>
  unfolding arrayO_except_array0[symmetric] arrayO_except_def
  using heap_list_all_nth_remove1[of i \<open>[0..<length xs]\<close> R xs] by (auto simp: star_aci(2,3))

lemma arrayO_nth_rule:
  assumes i: \<open>i < length a\<close>
  shows \<open> <arrayO (arl_assn R) a ai> Array.nth ai i <\<lambda>r. arrayO_except (arl_assn R) [i] a ai
   (\<lambda>r'. arl_assn R (a ! i) r * \<up>(r = r' ! i))>\<close>
proof -
  have i_le: \<open>i < Array.length h ai\<close> if \<open>(h, as) \<Turnstile> arrayO (arl_assn R) a ai\<close> for h as
    using  that i unfolding arrayO_def array_assn_def is_array_def
    by (auto simp: run.simps tap_def arrayO_def
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
        arrayO_except_array0_index[of i, symmetric]
        elim!: run_elims
        intro!: norm_pre_ex_rule)
    apply (auto simp: arrayO_except_def)
    done
qed

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
     [\<lambda>((l,i),j). i < length l \<and> j < length (l ! i)]\<^sub>a (arrayO (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow> b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
  apply sepref_to_hoare
  apply (subst (2) arrayO_except_array0_index[symmetric])
    apply (solves \<open>auto\<close>)[]
  apply (sep_auto simp: nth_aa_def nth_ll_def intro!: arrayO_nth_rule)
  apply (sep_auto simp: arrayO_except_def arrayO_def arl_assn_def hr_comp_def list_rel_def list_all2_lengthD
      star_aci(3) R R' pure_def H)
    done
qed

definition update_aa where
  \<open>update_aa a i x = Array.upd a i x\<close>

term \<open> Array.upd h a\<close>
term Array.update
term \<open>Array.set a (list_update (Array.get h a) i x) h\<close>
term arl_assn
term arl_append

definition append_el_aa :: "('a::{default,heap} array_list) array \<Rightarrow>
  nat \<Rightarrow> 'a \<Rightarrow> ('a array_list) array Heap"where
"append_el_aa \<equiv> \<lambda>a i x. do {
  j \<leftarrow> Array.nth a i;
  a' \<leftarrow> arl_append j x;
  Array.upd i a' a
  }"
definition append_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  \<open>append_ll xs i x = list_update xs i (xs ! i @ [x])\<close>
(* src si dst di (Suc l) *)
lemma
  \<open>i < Array.length h aa \<Longrightarrow> execute (blit aa i dst i l) h \<noteq> None\<close>
  apply (induction l)
   apply (auto simp: execute_simps execute_bind_case Array.nth_def
      Array.upd_def
      split: option.splits)
  oops
declare arrayO_nth_rule[sep_heap_rules]
lemma nth_aa_hnr[sepref_fr_rules]:
  fixes R ::  \<open>'a \<Rightarrow> 'b :: {heap, default}\<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 append_el_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> append_ll)) \<in>
     [\<lambda>((l,i),x). i < length l]\<^sub>a (arrayO (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO (arl_assn R))\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(\<exists>\<^sub>Ax. arrayO (arl_assn R) a ai * R x r * true * \<up> (x = a ! ba ! b)) =
     (arrayO (arl_assn R) a ai * R (a ! ba ! b) r * true)\<close> for a ai ba b r
    by (auto simp: ex_assn_def)
  have ?thesis
    apply sepref_to_hoare
    apply (sep_auto simp: append_el_aa_def)
     apply (sep_auto simp:  arrayO_except_def arl_append_def arl_assn_def (* is_array_list_def *)
        (* arrayO_def *) (* arl_assn_def *) (* is_array_def *)
        hr_comp_def eq_commute[of \<open>(_, _)\<close>])
      
     apply (sep_auto simp: arrayO_except_def arrayO_def arl_assn_def (* is_array_def *)
        hr_comp_def eq_commute[of \<open>(_, _)\<close>])
      thm upd_rule
      thm arl_append_rule
    apply (rule bind_rule)
      -- \<open>some work on ArrayO missing\<close>
      sorry
    show ?thesis
  proof (sepref_to_hoare, clarsimp simp only: hoare_triple_def Let_def, intro allI impI conjI)
    fix a :: \<open>'a list list\<close> and ai :: \<open>('b array_list) array\<close> and
      h :: Heap.heap and as:: \<open>nat set\<close> and \<sigma> :: \<open>Heap.heap option\<close> and r :: \<open>('b array_list) array\<close> and
      i i' :: nat and x' :: 'a and x :: 'b
    assume
      i: \<open>i < length a\<close> and
      h: \<open>(h, as) \<Turnstile> R x' x * \<up> ((i', i) \<in> nat_rel) * arrayO (arl_assn R) a ai\<close> and
      run: \<open>run (append_el_aa ai i' x) (Some h) \<sigma> r\<close>
    have i'_i[simp]: \<open>i' = i\<close>
      using h by auto
    have i_le: \<open>i < Array.length h ai\<close>
      using h i unfolding arrayO_def array_assn_def is_array_def
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    have xs_i: \<open>\<exists>as'. (h, as') \<Turnstile> (arl_assn R) (a ! i) (Array.get h ai ! i)\<close>
      using h i unfolding arrayO_def array_assn_def is_array_def
      using models_heap_list_all_models_nth[of _ _ _ _ _ i]
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    have ex_arl: \<open>execute (arl_append (Array.get h ai ! i) x) h \<noteq> None\<close>
      using run h assms i_le i xs_i
      using arl_append_rule[of _ \<open>Array.get h ai ! i\<close> x, unfolded hoare_triple_def]
      unfolding arl_assn_def hr_comp_def
(*       apply (cases \<open>Array.get h ai ! i\<close>)
      apply (auto simp: run.simps tap_def arrayO_def execute_simps arl_append_def
          mod_star_conv array_assn_def is_array_def append_el_aa_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          array_grow_def Let_def split_beta
          execute_bind_case split: option.splits if_splits) *)





    have ex: \<open>execute (append_el_aa ai i x) h = Some x'''\<close>
      using run h assms i_le
      apply (auto simp: run.simps tap_def arrayO_def execute_simps
          mod_star_conv array_assn_def is_array_def append_el_aa_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          execute_bind_case split: option.splits)
        oops
    show \<open>\<not> is_exn \<sigma>\<close>
      using run h assms
      by (auto simp: run.simps tap_def arrayO_def execute_simps
          mod_star_conv array_assn_def is_array_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)



definition append_aa :: "'a::heap array_list array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  [code del]: "append_aa a i x = Heap_Monad.guard (\<lambda>h::Heap.heap. i < Array.length h a \<and> j < snd (Array.get h a ! i))
    (\<lambda>h. (arl_append (Array.get h a ! i) x))"

end