theory Tuple4
  imports
    More_Sepref.WB_More_Refinement IsaSAT_Literals
begin

text \<open>
This is the setup for accessing and modifying the state as an abstract tuple of 4 elements.
 The construction is kept generic 
(even if still targetting only our state). There is a lot of copy-paste that would be nice to automate
at some point.


We define 3 sort of operations:

  \<^enum> extracting an element, replacing it by an default element. Modifies the state. The name starts 
with \<^text>\<open>exctr\<close>

  \<^enum> reinserting an element, freeing the current one. Modifies the state. The name starts with
 \<^text>\<open>update\<close>

  \<^enum> in-place reading a value, possibly with pure parameters. Does not modify the state. The name
starts with \<^text>\<open>read\<close>

\<close>

datatype ('a, 'b, 'c, 'd) tuple4 = Tuple4
  (Tuple4_a: 'a)
  (Tuple4_b: 'b)
  (Tuple4_c: 'c)
  (Tuple4_d: 'd)

context
begin

qualified fun set_a :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> _\<close> where
  \<open>set_a M (Tuple4 _ N D i) = (Tuple4 M N D i)\<close>

qualified fun set_b :: \<open>'b \<Rightarrow> _ \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>set_b N (Tuple4 M _ D i) = (Tuple4 M N D i)\<close>

qualified fun set_c :: \<open>'c \<Rightarrow> ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>set_c D (Tuple4 M N _ i) = (Tuple4 M N D i)\<close>

qualified fun set_d :: \<open>'d \<Rightarrow> ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>set_d i (Tuple4 M N D _) = (Tuple4 M N D i)\<close>

end

lemma lambda_comp_true: \<open>(\<lambda>S. True) \<circ> f = (\<lambda>_. True)\<close> \<open>uncurry (\<lambda>a b. True) = (\<lambda>_. True)\<close>  \<open>uncurry2 (\<lambda>a b c. True) = (\<lambda>_. True)\<close>
  \<open>case_tuple4 (\<lambda>M _ _ _. True) = (\<lambda>_. True)\<close>
  by (auto intro!: ext split: Tuple4.tuple4.splits)

named_theorems Tuple4_state_simp \<open>Simplify the state setter and extractors\<close>
lemma [Tuple4_state_simp]:
  \<open>Tuple4_a (Tuple4.set_a a S) = a\<close>
  \<open>Tuple4_b (Tuple4.set_a b S) = Tuple4_b S\<close>
  \<open>Tuple4_c (Tuple4.set_a b S) = Tuple4_c S\<close>
  \<open>Tuple4_d (Tuple4.set_a b S) = Tuple4_d S\<close>
  by (cases S; auto; fail)+

lemma [Tuple4_state_simp]:
  \<open>Tuple4_a (Tuple4.set_b b S) = Tuple4_a S\<close>
  \<open>Tuple4_b (Tuple4.set_b b S) = b\<close>
  \<open>Tuple4_c (Tuple4.set_b b S) = Tuple4_c S\<close>
  \<open>Tuple4_d (Tuple4.set_b b S) = Tuple4_d S\<close>
  by (cases S; auto; fail)+

lemma [Tuple4_state_simp]:
  \<open>Tuple4_a (Tuple4.set_c b S) = Tuple4_a S\<close>
  \<open>Tuple4_b (Tuple4.set_c b S) = Tuple4_b S\<close>
  \<open>Tuple4_c (Tuple4.set_c b S) = b\<close>
  \<open>Tuple4_d (Tuple4.set_c b S) = Tuple4_d S\<close>
  by (cases S; auto; fail)+

lemma [Tuple4_state_simp]:
  \<open>Tuple4_a (Tuple4.set_d b S) = Tuple4_a S\<close>
  \<open>Tuple4_b (Tuple4.set_d b S) = Tuple4_b S\<close>
  \<open>Tuple4_c (Tuple4.set_d b S) = Tuple4_c S\<close>
  \<open>Tuple4_d (Tuple4.set_d b S) = b\<close>
  by (cases S; auto; fail)+

declare Tuple4_state_simp[simp]
end
