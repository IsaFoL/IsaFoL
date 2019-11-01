theory PAC_Polynoms_Term
  imports PAC_Polynoms
    Refine_Imperative_HOL.IICF
begin
typ \<open>('a, 'b) fmap\<close>
(*Taken from WB_More_Refinement*)
lemma fref_to_Down_curry_left:
  fixes f:: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c nres\<close> and
    A::\<open>(('a \<times> 'b) \<times> 'd) set\<close>
  shows
    \<open>(uncurry f, g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
      (\<And>a b x'. P x' \<Longrightarrow> ((a, b), x') \<in> A \<Longrightarrow> f a b \<le> \<Down> B (g x'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma fref_to_Down_curry_right:
  fixes g :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c nres\<close> and f :: \<open>'d \<Rightarrow> _ nres\<close> and
    A::\<open>('d \<times> ('a \<times> 'b)) set\<close>
  shows
    \<open>(f, uncurry g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
      (\<And>a b x'. P (a,b) \<Longrightarrow> (x', (a, b)) \<in> A \<Longrightarrow> f x' \<le> \<Down> B (g a b))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

type_synonym term_poly_list = \<open>string list\<close>
type_synonym llist_polynom = \<open>(term_poly_list \<times> int) list\<close>


text \<open>We instantiate the characters with typeclass linorder to be able to talk abourt sorted and
  so on.\<close>

definition less_than_char :: \<open>(char \<times> char) set\<close> where
  \<open>less_than_char = {(a, b). of_char a < (of_char b :: nat) }\<close>

lemma trans_less_than_char[simp]:
    \<open>trans less_than_char\<close> and
  irrefl_less_than_char:
    \<open>irrefl less_than_char\<close> and
  antisym_less_than_char:
    \<open>antisym less_than_char\<close>
  by (auto simp: less_than_char_def trans_def irrefl_def antisym_def)

abbreviation var_order_rel :: \<open>(string \<times> string) set\<close> where
  \<open>var_order_rel \<equiv> lexord less_than_char\<close>

abbreviation var_order :: \<open>string \<Rightarrow> string \<Rightarrow> bool\<close> where
  \<open>var_order \<equiv> rel2p var_order_rel\<close>

abbreviation term_order_rel :: \<open>(term_poly_list \<times> term_poly_list) set\<close> where
  \<open>term_order_rel \<equiv> lexord (lexord less_than_char)\<close>

abbreviation term_order :: \<open>term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> bool\<close> where
  \<open>term_order \<equiv> rel2p term_order_rel\<close>

definition term_poly_list_rel :: \<open>(term_poly_list \<times> term_poly) set\<close> where
  \<open>term_poly_list_rel = {(xs, ys).
     ys = mset xs \<and>
     distinct xs \<and>
     sorted_wrt (rel2p (lexord less_than_char)) xs}\<close>

definition poly_list_rel :: \<open>_ \<Rightarrow> (('a \<times> int) list \<times> mset_polynom) set\<close> where
  \<open>poly_list_rel R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     0 \<notin># snd `# ys}\<close>

definition sorted_poly_list_rel_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool)
     \<Rightarrow> ('a \<times> string multiset) set \<Rightarrow> (('a \<times> int) list \<times> mset_polynom) set\<close> where
  \<open>sorted_poly_list_rel_wrt S R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     sorted_wrt S (map fst xs) \<and>
     0 \<notin># snd `# ys}\<close>

abbreviation sorted_poly_list_rel where
  \<open>sorted_poly_list_rel R \<equiv> sorted_poly_list_rel_wrt R term_poly_list_rel\<close>

abbreviation sorted_poly_rel where
  \<open>sorted_poly_rel \<equiv> sorted_poly_list_rel (rel2p (lexord (lexord less_than_char)))\<close>

abbreviation unsorted_poly_rel where
  \<open>unsorted_poly_rel \<equiv> poly_list_rel term_poly_list_rel\<close>

lemma sorted_poly_list_rel_empty_l[simp]:
  \<open>([], s') \<in> sorted_poly_list_rel_wrt S T \<longleftrightarrow> s' = {#}\<close>
  by (cases s')
    (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def)


end