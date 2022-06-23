theory Tuple17
  imports More_Sepref.WB_More_Refinement IsaSAT_Literals
begin


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 = Tuple17
  (Tuple17_get_a: 'a)
  (Tuple17_get_b: 'b)
  (Tuple17_get_c: 'c)
  (Tuple17_get_d: 'd)
  (Tuple17_get_e: 'e)
  (Tuple17_get_f: 'f)
  (Tuple17_get_g: 'g)
  (Tuple17_get_h: 'h)
  (Tuple17_get_i: 'i)
  (Tuple17_get_j: 'j)
  (Tuple17_get_k: 'k)
  (Tuple17_get_l: 'l)
  (Tuple17_get_m: 'm)
  (Tuple17_get_n: 'n)
  (Tuple17_get_o: 'o)
  (Tuple17_get_p: 'p)
  (Tuple17_get_q: 'q)

paragraph \<open>Accessors\<close>

context
begin
qualified fun set_a :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_a M (Tuple17 _ N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_b :: \<open>'b \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_b N (Tuple17 M _ D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_c :: \<open>'c \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_c D (Tuple17 M N _ i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_d :: \<open>'d \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_d i (Tuple17 M N D _ W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_e :: \<open>'e \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_e W (Tuple17 M N D i _ ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_f :: \<open>'f \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_f ivmtf (Tuple17 M N D i W _ icount ccach lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_g :: \<open>'g \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_g icount (Tuple17 M N D i W ivmtf _ ccach lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_h :: \<open>'h \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_h ccach (Tuple17 M N D i W ivmtf icount _ lbd outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_i :: \<open>'i \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_i lbd (Tuple17 M N D i W ivmtf icount ccach _ outl heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_j :: \<open>'j \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_j outl (Tuple17 M N D i W ivmtf icount ccach lbd _ heur stats aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_k :: \<open>'k \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_k stats (Tuple17 M N D i W ivmtf icount ccach lbd outl _ heur aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)\<close>

fun set_l :: \<open>'l \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_l heur (Tuple17 M N D i W ivmtf icount ccach lbd outl stats _ aivdom clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)\<close>

fun set_m :: \<open>'m \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_m aivdom (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats _ clss opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_n :: \<open>'n \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_n clss (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom _ opts arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_o :: \<open>'o \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_o opts (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss _ arena occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_p :: \<open>'p \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_p arena (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts _ occs) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>

fun set_q :: \<open>'q \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>set_q occs (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena _) = (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)\<close>
end

named_theorems tuple17_state_simp
lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_a M S) = M\<close>
  \<open>Tuple17_get_b (Tuple17.set_a M S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_a M S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_a M S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_a M S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_a M S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_a M S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_a M S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_a M S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_a M S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_a M S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_a M S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_a M S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_a M S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_a M S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_a M S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_a M S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_b N S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_b N S) = N\<close>
  \<open>Tuple17_get_c(Tuple17.set_b N S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_b N S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_b N S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_b N S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_b N S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_b N S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_b N S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_b N S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_b N S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_b N S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_b N S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_b N S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_b N S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_b N S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_b N S) = Tuple17_get_q S\<close>

  \<open>Tuple17_get_a (Tuple17.set_c D S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_c D S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_c D S) = D\<close>
  \<open>Tuple17_get_d (Tuple17.set_c D S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_c D S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_c D S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_c D S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_c D S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_c D S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_c D S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_c D S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_c D S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_c D S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_c D S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_c D S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_c D S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_c D S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_d j S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_d j S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_d j S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_d j S) = j\<close>
  \<open>Tuple17_get_e (Tuple17.set_d j S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_d j S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_d j S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_d j S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_d j S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_d j S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_d j S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_d j S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_d j S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_d j S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_d j S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_d j S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_d j S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_e W S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_e W S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_e W S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_e W S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_e W S) = W\<close>
  \<open>Tuple17_get_f (Tuple17.set_e W S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_e W S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_e W S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_e W S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_e W S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_e W S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_e W S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_e W S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_e W S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_e W S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_e W S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_e W S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_f vmtf' S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_f vmtf' S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_f vmtf' S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_f vmtf' S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_f vmtf' S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_f vmtf' S) = vmtf'\<close>
  \<open>Tuple17_get_g (Tuple17.set_f vmtf' S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_f vmtf' S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_f vmtf' S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_f vmtf' S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_f vmtf' S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_f vmtf' S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_f vmtf' S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_f vmtf' S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_f vmtf' S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_f vmtf' S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_f vmtf' S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_g count' S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_g count' S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_g count' S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_g count' S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_g count' S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_g count' S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_g count' S) = count'\<close>
  \<open>Tuple17_get_h (Tuple17.set_g count' S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_g count' S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_g count' S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_g count' S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_g count' S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_g count' S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_g count' S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_g count' S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_g count' S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_g count' S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp: \<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_h ccach S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_h ccach S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_h ccach S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_h ccach S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_h ccach S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_h ccach S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_h ccach S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_h ccach S) = ccach\<close>
  \<open>Tuple17_get_i (Tuple17.set_h ccach S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_h ccach S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_h ccach S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_h ccach S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_h ccach S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_h ccach S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_h ccach S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_h ccach S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_h ccach S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_i lbd S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_i lbd S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_i lbd S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_i lbd S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_i lbd S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_i lbd S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_i lbd S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_i lbd S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_i lbd S) = lbd\<close>
  \<open>Tuple17_get_j (Tuple17.set_i lbd S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_i lbd S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_i lbd S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_i lbd S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_i lbd S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_i lbd S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_i lbd S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_i lbd S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_j outl S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_j outl S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_j outl S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_j outl S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_j outl S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_j outl S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_j outl S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_j outl S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_j outl S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_j outl S) = outl\<close>
  \<open>Tuple17_get_k (Tuple17.set_j outl S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_j outl S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_j outl S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_j outl S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_j outl S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_j outl S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_j outl S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_k stats S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_k stats S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_k stats S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_k stats S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_k stats S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_k stats S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_k stats S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_k stats S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_k stats S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_k stats S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_k stats S) = stats\<close>
  \<open>Tuple17_get_l (Tuple17.set_k stats S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_k stats S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_k stats S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_k stats S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_k stats S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_k stats S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_l heur S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_l heur S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_l heur S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_l heur S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_l heur S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_l heur S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_l heur S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_l heur S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_l heur S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_l heur S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_l heur S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_l heur S) = heur\<close>
  \<open>Tuple17_get_m (Tuple17.set_l heur S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (Tuple17.set_l heur S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_l heur S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_l heur S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_l heur S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_m aivdom S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_m aivdom S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_m aivdom S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_m aivdom S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_m aivdom S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_m aivdom S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_m aivdom S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_m aivdom S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_m aivdom S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_m aivdom S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_m aivdom S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_m aivdom S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_m aivdom S) = aivdom\<close>
  \<open>Tuple17_get_n (Tuple17.set_m aivdom S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (Tuple17.set_m aivdom S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_m aivdom S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_m aivdom S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (Tuple17.set_n lcount S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (Tuple17.set_n lcount S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(Tuple17.set_n lcount S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (Tuple17.set_n lcount S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (Tuple17.set_n lcount S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (Tuple17.set_n lcount S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (Tuple17.set_n lcount S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (Tuple17.set_n lcount S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (Tuple17.set_n lcount S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (Tuple17.set_n lcount S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (Tuple17.set_n lcount S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (Tuple17.set_n lcount S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (Tuple17.set_n lcount S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_o (Tuple17.set_n lcount S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_n lcount S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_n lcount S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (set_o lcount S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (set_o lcount S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(set_o lcount S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (set_o lcount S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (set_o lcount S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (set_o lcount S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (set_o lcount S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (set_o lcount S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (set_o lcount S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (set_o lcount S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (set_o lcount S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (set_o lcount S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (set_o lcount S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (set_o lcount S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (set_o lcount S) = lcount\<close>
  \<open>Tuple17_get_p (set_o lcount S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (Tuple17.set_o lcount S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (set_p old_arena S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (set_p old_arena S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(set_p old_arena S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (set_p old_arena S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (set_p old_arena S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (set_p old_arena S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (set_p old_arena S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (set_p old_arena S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (set_p old_arena S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (set_p old_arena S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (set_p old_arena S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (set_p old_arena S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (set_p old_arena S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (set_p old_arena S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (set_p old_arena S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (set_p old_arena S) = old_arena\<close>
  \<open>Tuple17_get_q (Tuple17.set_p old_arena S) = Tuple17_get_q S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple17_state_simp]:
  \<open>Tuple17_get_a (set_q old_arena S) = Tuple17_get_a S\<close>
  \<open>Tuple17_get_b (set_q old_arena S) = Tuple17_get_b S\<close>
  \<open>Tuple17_get_c(set_q old_arena S) = Tuple17_get_c S\<close>
  \<open>Tuple17_get_d (set_q old_arena S) = Tuple17_get_d S\<close>
  \<open>Tuple17_get_e (set_q old_arena S) = Tuple17_get_e S\<close>
  \<open>Tuple17_get_f (set_q old_arena S) = Tuple17_get_f S\<close>
  \<open>Tuple17_get_g (set_q old_arena S) = Tuple17_get_g S\<close>
  \<open>Tuple17_get_h (set_q old_arena S) = Tuple17_get_h S\<close>
  \<open>Tuple17_get_i (set_q old_arena S) = Tuple17_get_i S\<close>
  \<open>Tuple17_get_j (set_q old_arena S) = Tuple17_get_j S\<close>
  \<open>Tuple17_get_k (set_q old_arena S) = Tuple17_get_k S\<close>
  \<open>Tuple17_get_l (set_q old_arena S) = Tuple17_get_l S\<close>
  \<open>Tuple17_get_m (set_q old_arena S) = Tuple17_get_m S\<close>
  \<open>Tuple17_get_n (set_q old_arena S) = Tuple17_get_n S\<close>
  \<open>Tuple17_get_o (set_q old_arena S) = Tuple17_get_o S\<close>
  \<open>Tuple17_get_p (Tuple17.set_q old_arena S) = Tuple17_get_p S\<close>
  \<open>Tuple17_get_q (set_q old_arena S) = old_arena\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemmas [simp] = tuple17_state_simp

named_theorems tuple17_getters_setters \<open>Definition of getters and setters\<close>

end
