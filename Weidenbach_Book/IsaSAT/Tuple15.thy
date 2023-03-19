theory Tuple15
  imports
    More_Sepref.WB_More_Refinement IsaSAT_Literals
begin

text \<open>
This is the setup for accessing and modifying the state as an abstract tuple of 15 elements.
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

datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 = Tuple15
  (Tuple15_a: 'a)
  (Tuple15_b: 'b)
  (Tuple15_c: 'c)
  (Tuple15_d: 'd)
  (Tuple15_e: 'e)
  (Tuple15_f: 'f)
  (Tuple15_g: 'g)
  (Tuple15_h: 'h)
  (Tuple15_i: 'i)
  (Tuple15_j: 'j)
  (Tuple15_k: 'k)
  (Tuple15_l: 'l)
  (Tuple15_m: 'm)
  (Tuple15_n: 'n)
  (Tuple15_o: 'o)

context
begin

qualified fun set_a :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> _\<close> where
  \<open>set_a M (Tuple15 _ N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_b :: \<open>'b \<Rightarrow> _ \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_b N (Tuple15 M _ D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_c :: \<open>'c \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_c D (Tuple15 M N _ i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_d :: \<open>'d \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_d i (Tuple15 M N D _ W ivmtf icount ccach lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_e :: \<open>'e \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_e W (Tuple15 M N D i _ ivmtf icount ccach lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_f :: \<open>'f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_f ivmtf (Tuple15 M N D i W _ icount ccach lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_g :: \<open>'g \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_g icount (Tuple15 M N D i W ivmtf _ ccach lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_h :: \<open>'h \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_h ccach (Tuple15 M N D i W ivmtf icount _ lbd outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_i :: \<open>'i \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_i lbd (Tuple15 M N D i W ivmtf icount ccach _ outl heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_j :: \<open>'j \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_j outl (Tuple15 M N D i W ivmtf icount ccach lbd _ heur stats aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_l :: \<open>'l \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_l heur (Tuple15 M N D i W ivmtf icount ccach lbd outl stats _ aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts)\<close>

qualified fun set_k :: \<open>'k \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_k stats (Tuple15 M N D i W ivmtf icount ccach lbd outl _ heur aivdom clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts)\<close>

qualified fun set_m :: \<open>'m \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_m aivdom (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats _ clss opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_n :: \<open>'n \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_n clss (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom _ opts) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

qualified fun set_o :: \<open>'o \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>set_o opts (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss _) = (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)\<close>

end

lemma lambda_comp_true: \<open>(\<lambda>S. True) \<circ> f = (\<lambda>_. True)\<close> \<open>uncurry (\<lambda>a b. True) = (\<lambda>_. True)\<close>  \<open>uncurry2 (\<lambda>a b c. True) = (\<lambda>_. True)\<close>
  \<open>case_tuple15 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _. True) = (\<lambda>_. True)\<close>
  by (auto intro!: ext split: Tuple15.tuple15.splits)

named_theorems Tuple15_state_simp \<open>Simplify the state setter and extractors\<close>
lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_a a S) = a\<close>
  \<open>Tuple15_b (Tuple15.set_a b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_a b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_a b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_a b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_a b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_a b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_a b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_a b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_a b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_a b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_a b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_a b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_a b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_a b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_b b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_b b S) = b\<close>
  \<open>Tuple15_c (Tuple15.set_b b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_b b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_b b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_b b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_b b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_b b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_b b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_b b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_b b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_b b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_b b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_b b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_b b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_c b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_c b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_c b S) = b\<close>
  \<open>Tuple15_d (Tuple15.set_c b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_c b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_c b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_c b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_c b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_c b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_c b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_c b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_c b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_c b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_c b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_c b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_d b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_d b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_d b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_d b S) = b\<close>
  \<open>Tuple15_e (Tuple15.set_d b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_d b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_d b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_d b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_d b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_d b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_d b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_d b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_d b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_d b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_d b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_e b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_e b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_e b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_e b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_e b S) = b\<close>
  \<open>Tuple15_f (Tuple15.set_e b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_e b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_e b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_e b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_e b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_e b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_e b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_e b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_e b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_e b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_f b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_f b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_f b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_f b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_f b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_f b S) = b\<close>
  \<open>Tuple15_g (Tuple15.set_f b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_f b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_f b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_f b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_f b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_f b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_f b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_f b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_f b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_g b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_g b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_g b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_g b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_g b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_g b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_g b S) = b\<close>
  \<open>Tuple15_h (Tuple15.set_g b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_g b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_g b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_g b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_g b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_g b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_g b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_g b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_h b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_h b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_h b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_h b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_h b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_h b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_h b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_h b S) = b\<close>
  \<open>Tuple15_i (Tuple15.set_h b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_h b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_h b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_h b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_h b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_h b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_h b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_i b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_i b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_i b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_i b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_i b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_i b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_i b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_i b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_i b S) = b\<close>
  \<open>Tuple15_j (Tuple15.set_i b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_i b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_i b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_i b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_i b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_i b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_j b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_j b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_j b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_j b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_j b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_j b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_j b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_j b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_j b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_j b S) = b\<close>
  \<open>Tuple15_k (Tuple15.set_j b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_j b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_j b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_j b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_j b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_k b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_k b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_k b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_k b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_k b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_k b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_k b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_k b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_k b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_k b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_k b S) = b\<close>
  \<open>Tuple15_l (Tuple15.set_k b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_k b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_k b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_k b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+
 
lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_l b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_l b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_l b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_l b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_l b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_l b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_l b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_l b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_l b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_l b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_l b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_l b S) = b\<close>
  \<open>Tuple15_m (Tuple15.set_l b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_l b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_l b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+


lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_m b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_m b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_m b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_m b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_m b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_m b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_m b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_m b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_m b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_m b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_m b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_m b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_m b S) = b\<close>
  \<open>Tuple15_n (Tuple15.set_m b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_m b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_n b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_n b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_n b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_n b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_n b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_n b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_n b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_n b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_n b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_n b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_n b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_n b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_n b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_n b S) = b\<close>
  \<open>Tuple15_o (Tuple15.set_n b S) = Tuple15_o S\<close>
  by (cases S; auto; fail)+

lemma [Tuple15_state_simp]:
  \<open>Tuple15_a (Tuple15.set_o b S) = Tuple15_a S\<close>
  \<open>Tuple15_b (Tuple15.set_o b S) = Tuple15_b S\<close>
  \<open>Tuple15_c (Tuple15.set_o b S) = Tuple15_c S\<close>
  \<open>Tuple15_d (Tuple15.set_o b S) = Tuple15_d S\<close>
  \<open>Tuple15_e (Tuple15.set_o b S) = Tuple15_e S\<close>
  \<open>Tuple15_f (Tuple15.set_o b S) = Tuple15_f S\<close>
  \<open>Tuple15_g (Tuple15.set_o b S) = Tuple15_g S\<close>
  \<open>Tuple15_h (Tuple15.set_o b S) = Tuple15_h S\<close>
  \<open>Tuple15_i (Tuple15.set_o b S) = Tuple15_i S\<close>
  \<open>Tuple15_j (Tuple15.set_o b S) = Tuple15_j S\<close>
  \<open>Tuple15_k (Tuple15.set_o b S) = Tuple15_k S\<close>
  \<open>Tuple15_l (Tuple15.set_o b S) = Tuple15_l S\<close>
  \<open>Tuple15_m (Tuple15.set_o b S) = Tuple15_m S\<close>
  \<open>Tuple15_n (Tuple15.set_o b S) = Tuple15_n S\<close>
  \<open>Tuple15_o (Tuple15.set_o b S) = b\<close>
  by (cases S; auto; fail)+

declare Tuple15_state_simp[simp]
end
