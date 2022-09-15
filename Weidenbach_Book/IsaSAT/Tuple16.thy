theory Tuple16
  imports More_Sepref.WB_More_Refinement IsaSAT_Literals
begin


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 = Tuple16
  (Tuple16_get_a: 'a)
  (Tuple16_get_b: 'b)
  (Tuple16_get_c: 'c)
  (Tuple16_get_d: 'd)
  (Tuple16_get_e: 'e)
  (Tuple16_get_f: 'f)
  (Tuple16_get_g: 'g)
  (Tuple16_get_h: 'h)
  (Tuple16_get_i: 'i)
  (Tuple16_get_j: 'j)
  (Tuple16_get_k: 'k)
  (Tuple16_get_l: 'l)
  (Tuple16_get_m: 'm)
  (Tuple16_get_n: 'n)
  (Tuple16_get_o: 'o)
  (Tuple16_get_p: 'p)

paragraph \<open>Accessors\<close>

context
begin
qualified fun set_a :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_a M (Tuple16 _ N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_b :: \<open>'b \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_b N (Tuple16 M _ D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_c :: \<open>'c \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_c D (Tuple16 M N _ i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_d :: \<open>'d \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_d i (Tuple16 M N D _ W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_e :: \<open>'e \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_e W (Tuple16 M N D i _ ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_f :: \<open>'f \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_f ivmtf (Tuple16 M N D i W _ icount ccach lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_g :: \<open>'g \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_g icount (Tuple16 M N D i W ivmtf _ ccach lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_h :: \<open>'h \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_h ccach (Tuple16 M N D i W ivmtf icount _ lbd outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_i :: \<open>'i \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_i lbd (Tuple16 M N D i W ivmtf icount ccach _ outl heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_j :: \<open>'j \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_j outl (Tuple16 M N D i W ivmtf icount ccach lbd _ heur stats aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_k :: \<open>'k \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_k stats (Tuple16 M N D i W ivmtf icount ccach lbd outl _ heur aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena)\<close>

fun set_l :: \<open>'l \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_l heur (Tuple16 M N D i W ivmtf icount ccach lbd outl stats _ aivdom clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena)\<close>

fun set_m :: \<open>'m \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_m aivdom (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats _ clss opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_n :: \<open>'n \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_n clss (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom _ opts arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_o :: \<open>'o \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_o opts (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss _ arena) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

fun set_p :: \<open>'p \<Rightarrow>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> _\<close> where
  \<open>set_p arena (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts _) = (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)\<close>

end

named_theorems tuple16_state_simp
lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_a M S) = M\<close>
  \<open>Tuple16_get_b (Tuple16.set_a M S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_a M S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_a M S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_a M S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_a M S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_a M S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_a M S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_a M S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_a M S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_a M S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_a M S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_a M S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_a M S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_a M S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_a M S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_b N S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_b N S) = N\<close>
  \<open>Tuple16_get_c(Tuple16.set_b N S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_b N S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_b N S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_b N S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_b N S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_b N S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_b N S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_b N S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_b N S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_b N S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_b N S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_b N S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_b N S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_b N S) = Tuple16_get_p S\<close>

  \<open>Tuple16_get_a (Tuple16.set_c D S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_c D S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_c D S) = D\<close>
  \<open>Tuple16_get_d (Tuple16.set_c D S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_c D S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_c D S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_c D S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_c D S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_c D S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_c D S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_c D S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_c D S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_c D S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_c D S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_c D S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_c D S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_d j S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_d j S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_d j S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_d j S) = j\<close>
  \<open>Tuple16_get_e (Tuple16.set_d j S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_d j S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_d j S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_d j S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_d j S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_d j S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_d j S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_d j S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_d j S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_d j S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_d j S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_d j S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_e W S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_e W S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_e W S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_e W S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_e W S) = W\<close>
  \<open>Tuple16_get_f (Tuple16.set_e W S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_e W S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_e W S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_e W S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_e W S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_e W S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_e W S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_e W S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_e W S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_e W S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_e W S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_f vmtf' S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_f vmtf' S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_f vmtf' S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_f vmtf' S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_f vmtf' S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_f vmtf' S) = vmtf'\<close>
  \<open>Tuple16_get_g (Tuple16.set_f vmtf' S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_f vmtf' S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_f vmtf' S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_f vmtf' S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_f vmtf' S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_f vmtf' S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_f vmtf' S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_f vmtf' S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_f vmtf' S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_f vmtf' S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_g count' S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_g count' S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_g count' S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_g count' S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_g count' S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_g count' S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_g count' S) = count'\<close>
  \<open>Tuple16_get_h (Tuple16.set_g count' S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_g count' S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_g count' S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_g count' S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_g count' S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_g count' S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_g count' S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_g count' S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_g count' S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp: \<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_h ccach S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_h ccach S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_h ccach S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_h ccach S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_h ccach S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_h ccach S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_h ccach S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_h ccach S) = ccach\<close>
  \<open>Tuple16_get_i (Tuple16.set_h ccach S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_h ccach S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_h ccach S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_h ccach S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_h ccach S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_h ccach S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_h ccach S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_h ccach S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_i lbd S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_i lbd S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_i lbd S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_i lbd S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_i lbd S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_i lbd S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_i lbd S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_i lbd S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_i lbd S) = lbd\<close>
  \<open>Tuple16_get_j (Tuple16.set_i lbd S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_i lbd S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_i lbd S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_i lbd S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_i lbd S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_i lbd S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_i lbd S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_j outl S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_j outl S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_j outl S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_j outl S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_j outl S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_j outl S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_j outl S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_j outl S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_j outl S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_j outl S) = outl\<close>
  \<open>Tuple16_get_k (Tuple16.set_j outl S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_j outl S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_j outl S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_j outl S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_j outl S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_j outl S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_k stats S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_k stats S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_k stats S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_k stats S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_k stats S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_k stats S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_k stats S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_k stats S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_k stats S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_k stats S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_k stats S) = stats\<close>
  \<open>Tuple16_get_l (Tuple16.set_k stats S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_k stats S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_k stats S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_k stats S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_k stats S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_l heur S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_l heur S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_l heur S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_l heur S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_l heur S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_l heur S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_l heur S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_l heur S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_l heur S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_l heur S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_l heur S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_l heur S) = heur\<close>
  \<open>Tuple16_get_m (Tuple16.set_l heur S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (Tuple16.set_l heur S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_l heur S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_l heur S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_m aivdom S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_m aivdom S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_m aivdom S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_m aivdom S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_m aivdom S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_m aivdom S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_m aivdom S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_m aivdom S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_m aivdom S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_m aivdom S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_m aivdom S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_m aivdom S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_m aivdom S) = aivdom\<close>
  \<open>Tuple16_get_n (Tuple16.set_m aivdom S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (Tuple16.set_m aivdom S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_m aivdom S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (Tuple16.set_n lcount S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (Tuple16.set_n lcount S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(Tuple16.set_n lcount S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (Tuple16.set_n lcount S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (Tuple16.set_n lcount S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (Tuple16.set_n lcount S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (Tuple16.set_n lcount S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (Tuple16.set_n lcount S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (Tuple16.set_n lcount S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (Tuple16.set_n lcount S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (Tuple16.set_n lcount S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (Tuple16.set_n lcount S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (Tuple16.set_n lcount S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_o (Tuple16.set_n lcount S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (Tuple16.set_n lcount S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (set_o lcount S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (set_o lcount S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(set_o lcount S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (set_o lcount S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (set_o lcount S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (set_o lcount S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (set_o lcount S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (set_o lcount S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (set_o lcount S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (set_o lcount S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (set_o lcount S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (set_o lcount S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (set_o lcount S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (set_o lcount S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (set_o lcount S) = lcount\<close>
  \<open>Tuple16_get_p (set_o lcount S) = Tuple16_get_p S\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemma [tuple16_state_simp]:
  \<open>Tuple16_get_a (set_p old_arena S) = Tuple16_get_a S\<close>
  \<open>Tuple16_get_b (set_p old_arena S) = Tuple16_get_b S\<close>
  \<open>Tuple16_get_c(set_p old_arena S) = Tuple16_get_c S\<close>
  \<open>Tuple16_get_d (set_p old_arena S) = Tuple16_get_d S\<close>
  \<open>Tuple16_get_e (set_p old_arena S) = Tuple16_get_e S\<close>
  \<open>Tuple16_get_f (set_p old_arena S) = Tuple16_get_f S\<close>
  \<open>Tuple16_get_g (set_p old_arena S) = Tuple16_get_g S\<close>
  \<open>Tuple16_get_h (set_p old_arena S) = Tuple16_get_h S\<close>
  \<open>Tuple16_get_i (set_p old_arena S) = Tuple16_get_i S\<close>
  \<open>Tuple16_get_j (set_p old_arena S) = Tuple16_get_j S\<close>
  \<open>Tuple16_get_k (set_p old_arena S) = Tuple16_get_k S\<close>
  \<open>Tuple16_get_l (set_p old_arena S) = Tuple16_get_l S\<close>
  \<open>Tuple16_get_m (set_p old_arena S) = Tuple16_get_m S\<close>
  \<open>Tuple16_get_n (set_p old_arena S) = Tuple16_get_n S\<close>
  \<open>Tuple16_get_o (set_p old_arena S) = Tuple16_get_o S\<close>
  \<open>Tuple16_get_p (set_p old_arena S) = old_arena\<close>
  by (solves \<open>cases S; auto simp:\<close>)+

lemmas [simp] = tuple16_state_simp

named_theorems tuple16_getters_setters \<open>Definition of getters and setters\<close>

end
