theory WB_Tuples
  imports WB_More_Refinement
begin

text \<open>
After enough benchmarking, it turns out that \<^typ>\<open>'a \<times> ('b \<times> 'c)\<close> is translated to an
inefficent reprentation in SML:
  \<^item> \<^typ>\<open>'a \<times> ('b \<times> 'c)\<close> means that an additional pointer is used;
  \<^item> \<^typ>\<open>'a \<times> ('b \<times> 'c)\<close> means that an additional pointer is allocated.

The allocation are highly critical in the SAT solver: The function that allocates most memory is the
propagation function (depending on the problem, also the binary propagation function).

We here define generic constructors that will make the
translation to a datatype with parameter \<^text>\<open>a * b * c\<close>. The single constructor will be
optimised away (at least by MLton).

Tuples are less efficient than C structures: every element is aligned on a 64 bit. This
is why compressing a \<^typ>\<open>uint32\<close> and a \<^typ>\<open>bool\<close> can be worth it (e.g., critical loop).
This means that reducing the size is better.

The functions below are meant to replace (more-or-less) transparently tuples during code generation.
Therefore, the refinement relation relates them to the tuple version.
\<close>

datatype ('a, 'b, 'c) tuple3 = Tuple3 'a 'b 'c

fun to_tuple3 where
  \<open>to_tuple3 a b c = Tuple3 a b c\<close>

fun to_tuple3_id where
  \<open>to_tuple3_id a b c = (a, b, c)\<close>

definition of_tuple3 where
  \<open>of_tuple3 x = (case x of Tuple3 a b c \<Rightarrow> (a, b, c))\<close>

definition of_tuple3_id :: \<open>'a \<times> 'b \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c\<close> where
 [simp]: \<open>of_tuple3_id x = x\<close>

instance tuple3 :: (heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple3)\<close>
    by (auto simp: inj_on_def of_tuple3_def split: tuple3.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c) tuple3 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple3 :: (default, default, default) default
begin
  definition default_tuple3  :: \<open>('a, 'b, 'c) tuple3\<close> where
  \<open>default_tuple3 = Tuple3 default default default\<close>

instance
  ..
end

sepref_register to_tuple3 to_tuple3_id

fun tuple3_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple3_assn R1 R2 R3 (a, b, c) x = (case x of Tuple3 a' b' c' \<Rightarrow>  R1 a a' * R2 b b' * R3 c c')\<close>

lemma to_tuple3_id_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo to_tuple3), uncurry2 (RETURN ooo to_tuple3_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d \<rightarrow>\<^sub>a tuple3_assn R1 R2 R3\<close>
  by sepref_to_hoare sep_auto

lemma of_tuple3_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple3, RETURN o of_tuple3_id) \<in>
     (tuple3_assn R1 R2 R3)\<^sup>d \<rightarrow>\<^sub>a R1 *a R2 *a R3\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple3_def split: tuple3.splits)


datatype ('a, 'b, 'c, 'd) tuple4 = Tuple4 'a 'b 'c 'd

fun to_tuple4 where
  \<open>to_tuple4 a b c d = Tuple4 a b c d\<close>

abbreviation to_tuple4' where
  \<open>to_tuple4' \<equiv> (\<lambda>(a, b, c, d). to_tuple4 a b c d)\<close>
fun to_tuple4_id where
  \<open>to_tuple4_id a b c d = (a, b, c, d)\<close>

definition of_tuple4 where
  \<open>of_tuple4 x = (case x of Tuple4 a b c d \<Rightarrow> (a, b, c, d))\<close>

definition of_tuple4_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd\<close> where
 [simp]: \<open>of_tuple4_id x = x\<close>

instance tuple4 :: (heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple4)\<close>
    by (auto simp: inj_on_def of_tuple4_def split: tuple4.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple4 :: (default, default, default, default) default
begin
  definition default_tuple4  :: \<open>('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>default_tuple4 = Tuple4 default default default default\<close>

instance
  ..
end

sepref_register to_tuple4 to_tuple4_id

fun tuple4_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple4_assn R1 R2 R3 R4 (a, b, c, d) x =
    (case x of Tuple4 a' b' c' d' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d')\<close>

lemma to_tuple4_id_hnr[sepref_fr_rules]:
  \<open>(uncurry3 (return oooo to_tuple4), uncurry3 (RETURN oooo to_tuple4_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d \<rightarrow>\<^sub>a tuple4_assn R1 R2 R3 R4\<close>
  by sepref_to_hoare sep_auto

lemma of_tuple4_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple4, RETURN o of_tuple4_id) \<in>
     (tuple4_assn R1 R2 R3 R4)\<^sup>d \<rightarrow>\<^sub>a R1 *a R2 *a R3 *a R4\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple4_def split: tuple4.splits)



datatype ('a, 'b, 'c, 'd, 'e) tuple5 = Tuple5 'a 'b 'c 'd 'e

fun to_tuple5 where
  \<open>to_tuple5 a b c d e = Tuple5 a b c d e\<close>

fun to_tuple5_id where
  \<open>to_tuple5_id a b c d e = (a, b, c, d, e)\<close>

definition of_tuple5 where
  \<open>of_tuple5 x = (case x of Tuple5 a b c d e \<Rightarrow> (a, b, c, d, e))\<close>

definition of_tuple5_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e\<close> where
 [simp]: \<open>of_tuple5_id x = x\<close>

instance tuple5 :: (heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple5)\<close>
    by (auto simp: inj_on_def of_tuple5_def split: tuple5.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e) tuple5 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple5 :: (default, default, default, default, default) default
begin
  definition default_tuple5  :: \<open>('a, 'b, 'c, 'd, 'e) tuple5\<close> where
  \<open>default_tuple5 = Tuple5 default default default default default\<close>

instance
  ..
end

sepref_register to_tuple5 to_tuple5_id

fun tuple5_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple5_assn R1 R2 R3 R4 R5 (a, b, c, d, e) x =
    (case x of Tuple5 a' b' c' d' e' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e')\<close>

lemma to_tuple5_id_hnr[sepref_fr_rules]:
  \<open>(uncurry4 (return ooooo to_tuple5), uncurry4 (RETURN ooooo to_tuple5_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d \<rightarrow>\<^sub>a tuple5_assn R1 R2 R3 R4 R5\<close>
  by sepref_to_hoare sep_auto

lemma of_tuple5_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple5, RETURN o of_tuple5_id) \<in>
     (tuple5_assn R1 R2 R3 R4 R5)\<^sup>d \<rightarrow>\<^sub>a R1 *a R2 *a R3 *a R4 *a R5\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple5_def split: tuple5.splits)



datatype ('a, 'b, 'c, 'd, 'e, 'f) tuple6 = Tuple6 'a 'b 'c 'd 'e 'f

fun to_tuple6 where
  \<open>to_tuple6 a b c d e f = Tuple6 a b c d e f\<close>

definition of_tuple6 where
  \<open>of_tuple6 x = (case x of Tuple6 a b c d e f \<Rightarrow> (a, b, c, d, e, f))\<close>

fun to_tuple6_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f"  where
  \<open>to_tuple6_id a b c d e f = (a, b, c, d, e, f)\<close>


definition of_tuple6_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<close> where
 [simp]: \<open>of_tuple6_id x = x\<close>

instance tuple6 :: (heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple6)\<close>
    by (auto simp: inj_on_def of_tuple6_def split: tuple6.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f) tuple6 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple6 :: (default, default, default, default, default, default) default
begin
  definition default_tuple6  :: \<open>('a, 'b, 'c, 'd, 'e, 'f) tuple6\<close> where
  \<open>default_tuple6 = Tuple6 default default default default default default\<close>

instance
  ..
end


sepref_register to_tuple6 to_tuple6_id

fun tuple6_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple6_assn R1 R2 R3 R4 R5 R6 (a, b, c, d, e, f) x =
    (case x of Tuple6 a' b' c' d' e' f' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' * R6 f f')\<close>

lemma to_tuple6_id_hnr:
  \<open>(uncurry5 (comp6 return to_tuple6), uncurry5 (RETURN oooooo to_tuple6_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d \<rightarrow>\<^sub>a tuple6_assn R1 R2 R3 R4 R5 R6\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple6_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple6, RETURN o of_tuple6_id) \<in>
     (tuple6_assn R1 R2 R3 R4 R5 R6)\<^sup>d \<rightarrow>\<^sub>a R1 *a R2 *a R3 *a R4 *a R5 *a R6\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple6_def split: tuple6.splits)



datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7 = Tuple7 'a 'b 'c 'd 'e 'f 'g

fun to_tuple7 where
  \<open>to_tuple7 a b c d e f g = Tuple7 a b c d e f g\<close>

definition of_tuple7 where
  \<open>of_tuple7 x = (case x of Tuple7 a b c d e f g \<Rightarrow> (a, b, c, d, e, f, g))\<close>

fun to_tuple7_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g"  where
  \<open>to_tuple7_id a b c d e f g = (a, b, c, d, e, f, g)\<close>


definition of_tuple7_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<close> where
 [simp]: \<open>of_tuple7_id x = x\<close>

instance tuple7 :: (heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple7)\<close>
    by (auto simp: inj_on_def of_tuple7_def split: tuple7.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple7 :: (default, default, default, default, default, default, default) default
begin
  definition default_tuple7  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7\<close> where
  \<open>default_tuple7 = Tuple7 default default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple7_id of_tuple7_id

fun tuple7_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple7_assn R1 R2 R3 R4 R5 R6 R7 (a, b, c, d, e, f, g) x =
    (case x of Tuple7 a' b' c' d' e' f' g' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g')\<close>

lemma to_tuple7_id_hnr[sepref_fr_rules]:
  \<open>(uncurry6 (return ooooooo to_tuple7), uncurry6 (RETURN ooooooo to_tuple7_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d \<rightarrow>\<^sub>a tuple7_assn R1 R2 R3 R4 R5 R6 R7\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple7_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple7, RETURN o of_tuple7_id) \<in>
     (tuple7_assn R1 R2 R3 R4 R5 R6 R7)\<^sup>d \<rightarrow>\<^sub>a R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple7_def split: tuple7.splits)



datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8 = Tuple8 'a 'b 'c 'd 'e 'f 'g 'h

fun to_tuple8 where
  \<open>to_tuple8 a b c d e f g h = Tuple8 a b c d e f g h\<close>

definition of_tuple8 where
  \<open>of_tuple8 x = (case x of Tuple8 a b c d e f g h \<Rightarrow> (a, b, c, d, e, f, g, h))\<close>

fun to_tuple8_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i"  where
  \<open>to_tuple8_id a b c d e f g h = (a, b, c, d, e, f, g, h)\<close>


definition of_tuple8_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i\<close> where
 [simp]: \<open>of_tuple8_id x = x\<close>

instance tuple8 :: (heap, heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple8)\<close>
    by (auto simp: inj_on_def of_tuple8_def split: tuple8.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple8 :: (default, default, default, default, default, default, default, default) default
begin
  definition default_tuple8  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8\<close> where
  \<open>default_tuple8 = Tuple8 default default default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple8_id of_tuple8_id

fun tuple8_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple8_assn R1 R2 R3 R4 R5 R6 R7 R8 (a, b, c, d, e, f, g, h) x =
    (case x of Tuple8 a' b' c' d' e' f' g' h' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h')\<close>

lemma to_tuple8_id_hnr[sepref_fr_rules]:
  \<open>(uncurry7 (return oooooooo to_tuple8), uncurry7 (RETURN oooooooo to_tuple8_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d \<rightarrow>\<^sub>a tuple8_assn R1 R2 R3 R4 R5 R6 R7 R8\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple8_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple8, RETURN o of_tuple8_id) \<in>
     (tuple8_assn R1 R2 R3 R4 R5 R6 R7 R8)\<^sup>d \<rightarrow>\<^sub>a R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple8_def split: tuple8.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9 = Tuple9 'a 'b 'c 'd 'e 'f 'g 'h 'i

fun to_tuple9 where
  \<open>to_tuple9 a b c d e f g h i = Tuple9 a b c d e f g h i\<close>

definition of_tuple9 where
  \<open>of_tuple9 x = (case x of Tuple9 a b c d e f g h i \<Rightarrow> (a, b, c, d, e, f, g, h, i))\<close>

fun to_tuple9_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow>
    'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i \<times> 'j"  where
  \<open>to_tuple9_id a b c d e f g h i = (a, b, c, d, e, f, g, h, i)\<close>


definition of_tuple9_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j\<close> where
 [simp]: \<open>of_tuple9_id x = x\<close>

instance tuple9 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple9)\<close>
    by (auto simp: inj_on_def of_tuple9_def split: tuple9.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple9 :: (default, default, default, default, default, default, default, default,
  default) default
begin
  definition default_tuple9  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9\<close> where
  \<open>default_tuple9 = Tuple9 default default default default default default default default
    default\<close>

instance
  ..
end

sepref_register to_tuple9_id of_tuple9_id
fun tuple9_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple9_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 (a, b, c, d, e, f, g, h, i) x =
    (case x of Tuple9 a' b' c' d' e' f' g' h' i' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i')\<close>

lemma to_tuple9_id_hnr[sepref_fr_rules]:
  \<open>(uncurry8 (return ooooooooo to_tuple9), uncurry8 (RETURN ooooooooo to_tuple9_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d \<rightarrow>\<^sub>a tuple9_assn R1 R2 R3 R4 R5 R6 R7 R8 R9\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple9_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple9, RETURN o of_tuple9_id) \<in>
     (tuple9_assn R1 R2 R3 R4 R5 R6 R7 R8 R9)\<^sup>d \<rightarrow>\<^sub>a R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple9_def split: tuple9.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10 = Tuple10 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j

fun to_tuple10 where
  \<open>to_tuple10 a b c d e f g h i j = Tuple10 a b c d e f g h i j\<close>

definition of_tuple10 where
  \<open>of_tuple10 x = (case x of Tuple10 a b c d e f g h i j \<Rightarrow> (a, b, c, d, e, f, g, h, i, j))\<close>

fun to_tuple10_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow>
    'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i \<times> 'j \<times> 'k"  where
  \<open>to_tuple10_id a b c d e f g h i j = (a, b, c, d, e, f, g, h, i, j)\<close>


definition of_tuple10_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k\<close> where
 [simp]: \<open>of_tuple10_id x = x\<close>

instance tuple10 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple10)\<close>
    by (auto simp: inj_on_def of_tuple10_def split: tuple10.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple10 :: (default, default, default, default, default, default, default, default,
  default, default) default
begin
  definition default_tuple10  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10\<close> where
  \<open>default_tuple10 = Tuple10 default default default default default default default default
    default default\<close>

instance
  ..
end

sepref_register to_tuple10_id of_tuple10_id
fun tuple10_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple10_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 (a, b, c, d, e, f, g, h, i, j) x =
    (case x of Tuple10 a' b' c' d' e' f' g' h' i' j' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j')\<close>

lemma to_tuple10_id_hnr[sepref_fr_rules]:
  \<open>(uncurry9 (return oooooooooo to_tuple10), uncurry9 (RETURN oooooooooo to_tuple10_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d \<rightarrow>\<^sub>a
       tuple10_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple10_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple10, RETURN o of_tuple10_id) \<in>
     (tuple10_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple10_def split: tuple10.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11 =
  Tuple11 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k

fun to_tuple11 where
  \<open>to_tuple11 a b c d e f g h i j k = Tuple11 a b c d e f g h i j k\<close>

definition of_tuple11 where
  \<open>of_tuple11 x = (case x of Tuple11 a b c d e f g h i j k \<Rightarrow> (a, b, c, d, e, f, g, h, i, j, k))\<close>

fun to_tuple11_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow>
    'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l"  where
  \<open>to_tuple11_id a b c d e f g h i j l = (a, b, c, d, e, f, g, h, i, j, l)\<close>


definition of_tuple11_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l\<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l\<close> where
 [simp]: \<open>of_tuple11_id x = x\<close>

instance tuple11 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple11)\<close>
    by (auto simp: inj_on_def of_tuple11_def split: tuple11.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple11 :: (default, default, default, default, default, default, default, default,
  default, default, default) default
begin
  definition default_tuple11  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11\<close> where
  \<open>default_tuple11 = Tuple11 default default default default default default default default
    default default default\<close>

instance
  ..
end

sepref_register to_tuple11_id of_tuple11_id
fun tuple11_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple11_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 (a, b, c, d, e, f, g, h, i, j, k) x =
    (case x of Tuple11 a' b' c' d' e' f' g' h' i' j' k' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k')\<close>

lemma to_tuple11_id_hnr[sepref_fr_rules]:
  \<open>(uncurry10 (return o\<^sub>1\<^sub>1 to_tuple11), uncurry10 (RETURN  o\<^sub>1\<^sub>1 to_tuple11_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d \<rightarrow>\<^sub>a
       tuple11_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple11_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple11, RETURN o of_tuple11_id) \<in>
     (tuple11_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple11_def split: tuple11.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12 =
  Tuple12 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l

fun to_tuple12 where
  \<open>to_tuple12 a b c d e f g h i j k l = Tuple12 a b c d e f g h i j k l\<close>

definition of_tuple12 where
  \<open>of_tuple12 x = (case x of Tuple12 a b c d e f g h i j k l \<Rightarrow> (a, b, c, d, e, f, g, h, i, j, k, l))\<close>

fun to_tuple12_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow>
    'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm"  where
  \<open>to_tuple12_id a b c d e f g h i j l m = (a, b, c, d, e, f, g, h, i, j, l, m)\<close>


definition of_tuple12_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm\<close> where
 [simp]: \<open>of_tuple12_id x = x\<close>

instance tuple12 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple12)\<close>
    by (auto simp: inj_on_def of_tuple12_def split: tuple12.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple12 :: (default, default, default, default, default, default, default, default,
  default, default, default, default) default
begin
  definition default_tuple12  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12\<close> where
  \<open>default_tuple12 = Tuple12 default default default default default default default default
    default default default default\<close>

instance
  ..
end

sepref_register to_tuple12_id of_tuple12_id
fun tuple12_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple12_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 (a, b, c, d, e, f, g, h, i, j, k, l) x =
    (case x of Tuple12 a' b' c' d' e' f' g' h' i' j' k' l' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l')\<close>

lemma to_tuple12_id_hnr[sepref_fr_rules]:
  \<open>(uncurry11 (return o\<^sub>1\<^sub>2 to_tuple12), uncurry11 (RETURN  o\<^sub>1\<^sub>2 to_tuple12_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d  *\<^sub>a R12\<^sup>d \<rightarrow>\<^sub>a
       tuple12_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple12_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple12, RETURN o of_tuple12_id) \<in>
     (tuple12_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple12_def split: tuple12.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13 =
  Tuple13 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm

fun to_tuple13 where
  \<open>to_tuple13 a b c d e f g h i j k l m = Tuple13 a b c d e f g h i j k l m\<close>

definition of_tuple13 where
  \<open>of_tuple13 x = (case x of
    Tuple13 a b c d e f g h i j k l m \<Rightarrow> (a, b, c, d, e, f, g, h, i, j, k, l, m))\<close>

fun to_tuple13_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
    'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n"  where
  \<open>to_tuple13_id a b c d e f g h i j l m n = (a, b, c, d, e, f, g, h, i, j, l, m, n)\<close>


definition of_tuple13_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n\<close> where
 [simp]: \<open>of_tuple13_id x = x\<close>

instance tuple13 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple13)\<close>
    by (auto simp: inj_on_def of_tuple13_def split: tuple13.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple13 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default) default
begin
  definition default_tuple13  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13\<close> where
  \<open>default_tuple13 = Tuple13 default default default default default default default default
    default default default default default\<close>

instance
  ..
end

sepref_register to_tuple13_id of_tuple13_id
fun tuple13_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple13_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 (a, b, c, d, e, f, g, h, i, j, k, l, m) x =
    (case x of Tuple13 a' b' c' d' e' f' g' h' i' j' k' l' m' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m')\<close>

lemma to_tuple13_id_hnr[sepref_fr_rules]:
  \<open>(uncurry12 (return o\<^sub>1\<^sub>3 to_tuple13), uncurry12 (RETURN  o\<^sub>1\<^sub>3 to_tuple13_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d \<rightarrow>\<^sub>a
       tuple13_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple13_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple13, RETURN o of_tuple13_id) \<in>
     (tuple13_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple13_def split: tuple13.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14 =
  Tuple14 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n

fun to_tuple14 where
  \<open>to_tuple14 a b c d e f g h i j k l m n = Tuple14 a b c d e f g h i j k l m n\<close>

definition of_tuple14 where
  \<open>of_tuple14 x = (case x of
    Tuple14 a b c d e f g h i j k l m n \<Rightarrow> (a, b, c, d, e, f, g, h, i, j, k, l, m, n))\<close>

fun to_tuple14_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
   'o \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o"  where
  \<open>to_tuple14_id a b c d e f g h i j l m n o' = (a, b, c, d, e, f, g, h, i, j, l, m, n, o')\<close>


definition of_tuple14_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times>
  'o \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o\<close> where
 [simp]: \<open>of_tuple14_id x = x\<close>

instance tuple14 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap,
  heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple14)\<close>
    by (auto simp: inj_on_def of_tuple14_def split: tuple14.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple14 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default, default) default
begin
  definition default_tuple14  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14\<close> where
  \<open>default_tuple14 = Tuple14 default default default default default default default default
    default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple14_id of_tuple14_id
fun tuple14_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple14_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n) x =
    (case x of Tuple14 a' b' c' d' e' f' g' h' i' j' k' l' m' n' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m' * R14 n n')\<close>

lemma to_tuple14_id_hnr[sepref_fr_rules]:
  \<open>(uncurry13 (return o\<^sub>1\<^sub>4 to_tuple14), uncurry13 (RETURN  o\<^sub>1\<^sub>4 to_tuple14_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d *\<^sub>a R14\<^sup>d \<rightarrow>\<^sub>a
       tuple14_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple14_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple14, RETURN o of_tuple14_id) \<in>
     (tuple14_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13 *a R14\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple14_def split: tuple14.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 =
  Tuple15 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n 'o

fun to_tuple15 where
  \<open>to_tuple15 a b c d e f g h i j k l m n o' = Tuple15 a b c d e f g h i j k l m n o'\<close>

definition of_tuple15 where
  \<open>of_tuple15 x = (case x of
    Tuple15 a b c d e f g h i j k l m n o' \<Rightarrow> (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o'))\<close>

fun to_tuple15_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
   'o \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o"  where
  \<open>to_tuple15_id a b c d e f g h i j l m n o' p = (a, b, c, d, e, f, g, h, i, j, l, m, n, o', p)\<close>


definition of_tuple15_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times>
  'o \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o\<close> where
 [simp]: \<open>of_tuple15_id x = x\<close>

instance tuple15 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap,
  heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<Rightarrow>
      nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple15)\<close>
    by (auto simp: inj_on_def of_tuple15_def split: tuple15.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple15 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default, default, default) default
begin
  definition default_tuple15  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>default_tuple15 = Tuple15 default default default default default default default default
    default default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple15_id of_tuple15_id
fun tuple15_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple15_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o2) x =
    (case x of Tuple15 a' b' c' d' e' f' g' h' i' j' k' l' m' n' o2' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m' * R14 n n' *
      R15 o2 o2')\<close>

lemma to_tuple15_id_hnr[sepref_fr_rules]:
  \<open>(uncurry14 (return o\<^sub>1\<^sub>5 to_tuple15), uncurry14 (RETURN  o\<^sub>1\<^sub>5 to_tuple15_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d *\<^sub>a
      R14\<^sup>d *\<^sub>a R15\<^sup>d \<rightarrow>\<^sub>a
       tuple15_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple15_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple15, RETURN o of_tuple15_id) \<in>
     (tuple15_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13 *a R14 *a R15\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple15_def split: tuple15.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 =
  Tuple16 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n 'o 'p

fun to_tuple16 where
  \<open>to_tuple16 a b c d e f g h i j k l m n o' p = Tuple16 a b c d e f g h i j k l m n o' p\<close>

definition of_tuple16 where
  \<open>of_tuple16 x = (case x of
    Tuple16 a b c d e f g h i j k l m n o' p \<Rightarrow> (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p))\<close>

fun to_tuple16_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
   'o \<Rightarrow> 'p \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p"  where
  \<open>to_tuple16_id a b c d e f g h i j k l m n o' p = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p)\<close>


definition of_tuple16_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times>
  'o \<times> 'p \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p\<close> where
 [simp]: \<open>of_tuple16_id x = x\<close>

instance tuple16 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap,
  heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times>
    'p \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple16)\<close>
    by (auto simp: inj_on_def of_tuple16_def split: tuple16.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple16 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default, default, default, default) default
begin
  definition default_tuple16  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o,
    'p) tuple16\<close> where
  \<open>default_tuple16 = Tuple16 default default default default default default default default
    default default default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple16_id of_tuple16_id
fun tuple16_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple16_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o2, p) x =
    (case x of Tuple16 a' b' c' d' e' f' g' h' i' j' k' l' m' n' o2' p' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m' * R14 n n' *
      R15 o2 o2' * R16 p p')\<close>

lemma to_tuple16_id_hnr[sepref_fr_rules]:
  \<open>(uncurry15 (return o\<^sub>1\<^sub>6 to_tuple16), uncurry15 (RETURN  o\<^sub>1\<^sub>6 to_tuple16_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d *\<^sub>a
      R14\<^sup>d *\<^sub>a R15\<^sup>d *\<^sub>a R16\<^sup>d \<rightarrow>\<^sub>a
       tuple16_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple16_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple16, RETURN o of_tuple16_id) \<in>
     (tuple16_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13 *a R14 *a R15
         *a R16\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple16_def split: tuple16.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 =
  Tuple17 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n 'o 'p 'q

fun to_tuple17 where
  \<open>to_tuple17 a b c d e f g h i j k l m n o' p q = Tuple17 a b c d e f g h i j k l m n o' p q\<close>

definition of_tuple17 where
  \<open>of_tuple17 x = (case x of
    Tuple17 a b c d e f g h i j k l m n o' p q \<Rightarrow>
      (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q))\<close>

fun to_tuple17_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
   'o \<Rightarrow> 'p \<Rightarrow>  'q \<Rightarrow>
   'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p
    \<times> 'q"  where
  \<open>to_tuple17_id a b c d e f g h i j k l m n o' p q =
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q)\<close>


definition of_tuple17_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times>
  'o \<times> 'p \<times> 'q \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p \<times> 'q\<close> where
 [simp]: \<open>of_tuple17_id x = x\<close>

instance tuple17 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap,
  heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times>
    'p \<times> 'q \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple17)\<close>
    by (auto simp: inj_on_def of_tuple17_def split: tuple17.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p,
    'q) tuple17 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple17 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default, default, default, default, default) default
begin
  definition default_tuple17  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o,
    'p, 'q) tuple17\<close> where
  \<open>default_tuple17 = Tuple17 default default default default default default default default
    default default default default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple17_id of_tuple17_id
fun tuple17_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple17_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o2, p, q) x =
    (case x of Tuple17 a' b' c' d' e' f' g' h' i' j' k' l' m' n' o2' p' q' \<Rightarrow> R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m' * R14 n n' *
      R15 o2 o2' * R16 p p' * R17 q q')\<close>

lemma to_tuple17_id_hnr[sepref_fr_rules]:
  \<open>(uncurry16 (return o\<^sub>1\<^sub>7 to_tuple17), uncurry16 (RETURN  o\<^sub>1\<^sub>7 to_tuple17_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d *\<^sub>a
      R14\<^sup>d *\<^sub>a R15\<^sup>d *\<^sub>a R16\<^sup>d *\<^sub>a R17\<^sup>d \<rightarrow>\<^sub>a
       tuple17_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple17_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple17, RETURN o of_tuple17_id) \<in>
     (tuple17_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13 *a R14 *a R15
         *a R16 *a  R17\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple17_def split: tuple17.splits)



datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q, 'r) tuple18 =
  Tuple18 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n 'o 'p 'q 'r

fun to_tuple18 where
  \<open>to_tuple18 a b c d e f g h i j k l m n o' p q r =
    Tuple18 a b c d e f g h i j k l m n o' p q r\<close>

definition of_tuple18 where
  \<open>of_tuple18 x = (case x of
    Tuple18 a b c d e f g h i j k l m n o' p q r \<Rightarrow>
      (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q, r))\<close>

fun to_tuple18_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
   'o \<Rightarrow> 'p \<Rightarrow>  'q \<Rightarrow> 'r \<Rightarrow>
   'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p
      \<times> 'q \<times> 'r"  where
  \<open>to_tuple18_id a b c d e f g h i j k l m n o' p q r =
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q, r)\<close>


definition of_tuple18_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times>
  'o \<times> 'p \<times> 'q \<times> 'r \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p \<times> 'q \<times> 'r\<close> where
 [simp]: \<open>of_tuple18_id x = x\<close>

instance tuple18 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap,
  heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times>
    'p \<times> 'q \<times> 'r \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple18)\<close>
    by (auto simp: inj_on_def of_tuple18_def split: tuple18.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p,
    'q, 'r) tuple18 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple18 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default, default, default, default, default, default) default
begin
  definition default_tuple18  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o,
    'p, 'q, 'r) tuple18\<close> where
  \<open>default_tuple18 = Tuple18 default default default default default default default default
    default default default default default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple18_id of_tuple18_id
fun tuple18_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple18_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o2, p, q, r) x =
    (case x of Tuple18 a' b' c' d' e' f' g' h' i' j' k' l' m' n' o2' p' q' r' \<Rightarrow>
      R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m' * R14 n n' *
      R15 o2 o2' * R16 p p' * R17 q q' * R18 r r')\<close>

lemma to_tuple18_id_hnr[sepref_fr_rules]:
  \<open>(uncurry17 (return o\<^sub>1\<^sub>8 to_tuple18), uncurry17 (RETURN  o\<^sub>1\<^sub>8 to_tuple18_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d *\<^sub>a
      R14\<^sup>d *\<^sub>a R15\<^sup>d *\<^sub>a R16\<^sup>d *\<^sub>a R17\<^sup>d  *\<^sub>a R18\<^sup>d \<rightarrow>\<^sub>a
       tuple18_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple18_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple18, RETURN o of_tuple18_id) \<in>
     (tuple18_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13 *a R14 *a R15
         *a R16 *a R17 *a R18\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple18_def split: tuple18.splits)



datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q, 'r, 's) tuple19 =
  Tuple19 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n 'o 'p 'q 'r 's

fun to_tuple19 where
  \<open>to_tuple19 a b c d e f g h i j k l m n o' p q r s =
    Tuple19 a b c d e f g h i j k l m n o' p q r s\<close>

definition of_tuple19 where
  \<open>of_tuple19 x = (case x of
    Tuple19 a b c d e f g h i j k l m n o' p q r s \<Rightarrow>
      (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q, r, s))\<close>

fun to_tuple19_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
   'o \<Rightarrow> 'p \<Rightarrow>  'q \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow>
   'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p
      \<times> 'q \<times> 'r \<times> 's"  where
  \<open>to_tuple19_id a b c d e f g h i j k l m n o' p q r s =
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q, r, s)\<close>


definition of_tuple19_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times>
  'o \<times> 'p \<times> 'q \<times> 'r \<times> 's \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p \<times> 'q \<times> 'r \<times>
    's\<close> where
 [simp]: \<open>of_tuple19_id x = x\<close>

instance tuple19 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap,
  heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times>
    'p \<times> 'q \<times> 'r \<times> 's \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple19)\<close>
    by (auto simp: inj_on_def of_tuple19_def split: tuple19.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p,
    'q, 'r, 's) tuple19 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple19 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default, default, default, default, default, default,
  default) default
begin
  definition default_tuple19  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o,
    'p, 'q, 'r, 's) tuple19\<close> where
  \<open>default_tuple19 = Tuple19 default default default default default default default default
    default default default default default default default default default default default\<close>

instance
  ..
end

sepref_register to_tuple19_id of_tuple19_id
fun tuple19_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple19_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o2, p, q, r, s) x =
    (case x of Tuple19 a' b' c' d' e' f' g' h' i' j' k' l' m' n' o2' p' q' r' s' \<Rightarrow>
      R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m' * R14 n n' *
      R15 o2 o2' * R16 p p' * R17 q q' * R18 r r' * R19 s s')\<close>

lemma to_tuple19_id_hnr[sepref_fr_rules]:
  \<open>(uncurry18 (return o\<^sub>1\<^sub>9 to_tuple19), uncurry18 (RETURN  o\<^sub>1\<^sub>9 to_tuple19_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d *\<^sub>a
      R14\<^sup>d *\<^sub>a R15\<^sup>d *\<^sub>a R16\<^sup>d *\<^sub>a R17\<^sup>d  *\<^sub>a R18\<^sup>d *\<^sub>a R19\<^sup>d \<rightarrow>\<^sub>a
       tuple19_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple19_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple19, RETURN o of_tuple19_id) \<in>
     (tuple19_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13 *a R14 *a R15
         *a R16 *a R17 *a R18 *a R19\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple19_def split: tuple19.splits)


datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q, 'r, 's, 't) tuple20 =
  Tuple20 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n 'o 'p 'q 'r 's 't

fun to_tuple20 where
  \<open>to_tuple20 a b c d e f g h i j k l m n o' p q r s t =
    Tuple20 a b c d e f g h i j k l m n o' p q r s t\<close>

definition of_tuple20 where
  \<open>of_tuple20 x = (case x of
    Tuple20 a b c d e f g h i j k l m n o' p q r s t \<Rightarrow>
      (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q, r, s, t))\<close>

fun to_tuple20_id :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow>
   'o \<Rightarrow> 'p \<Rightarrow>  'q \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow>
   'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p
      \<times> 'q \<times> 'r \<times> 's \<times> 't"  where
  \<open>to_tuple20_id a b c d e f g h i j k l m n o' p q r s t =
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o', p, q, r, s, t)\<close>


definition of_tuple20_id :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f  \<times> 'g \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times>
  'o \<times> 'p \<times> 'q \<times> 'r \<times> 's \<times> 't \<Rightarrow>
  'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'i  \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times> 'p \<times> 'q \<times> 'r \<times>
    's \<times> 't\<close> where
 [simp]: \<open>of_tuple20_id x = x\<close>

instance tuple20 :: (heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap, heap,
  heap, heap, heap, heap, heap, heap, heap, heap) heap
proof
  obtain to_nat :: \<open>'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> 'n \<times> 'o \<times>
    'p \<times> 'q \<times> 'r \<times> 's \<times> 't \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o of_tuple20)\<close>
    by (auto simp: inj_on_def of_tuple20_def split: tuple20.splits)
  then show \<open>\<exists>to_nat :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p,
    'q, 'r, 's, 't) tuple20 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation tuple20 :: (default, default, default, default, default, default, default, default,
  default, default, default, default, default, default, default, default, default, default,
  default, default) default
begin
  definition default_tuple20  :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o,
    'p, 'q, 'r, 's, 't) tuple20\<close> where
  \<open>default_tuple20 = Tuple20 default default default default default default default default
    default default default default default default default default default default default
    default\<close>

instance
  ..
end

sepref_register to_tuple20_id of_tuple20_id
fun tuple20_assn :: \<open>('a \<Rightarrow> 'a2 \<Rightarrow> assn) \<Rightarrow> _\<close> where
  \<open>tuple20_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o2, p, q, r, s, t) x =
    (case x of Tuple20 a' b' c' d' e' f' g' h' i' j' k' l' m' n' o2' p' q' r' s' t' \<Rightarrow>
      R1 a a' * R2 b b' * R3 c c' * R4 d d' * R5 e e' *
      R6 f f' * R7 g g' * R8 h h' * R9 i i' * R10 j j' * R11 k k' * R12 l l' * R13 m m' * R14 n n' *
      R15 o2 o2' * R16 p p' * R17 q q' * R18 r r' * R19 s s' * R20 t t')\<close>

lemma to_tuple20_id_hnr[sepref_fr_rules]:
  \<open>(uncurry19 (return o\<^sub>2\<^sub>0 to_tuple20), uncurry19 (RETURN  o\<^sub>2\<^sub>0 to_tuple20_id)) \<in>
     R1\<^sup>d *\<^sub>a R2\<^sup>d *\<^sub>a R3\<^sup>d *\<^sub>a R4\<^sup>d *\<^sub>a R5\<^sup>d *\<^sub>a R6\<^sup>d *\<^sub>a R7\<^sup>d *\<^sub>a R8\<^sup>d *\<^sub>a R9\<^sup>d *\<^sub>a R10\<^sup>d *\<^sub>a R11\<^sup>d *\<^sub>a R12\<^sup>d *\<^sub>a R13\<^sup>d *\<^sub>a
      R14\<^sup>d *\<^sub>a R15\<^sup>d *\<^sub>a R16\<^sup>d *\<^sub>a R17\<^sup>d  *\<^sub>a R18\<^sup>d *\<^sub>a R19\<^sup>d *\<^sub>a R20\<^sup>d \<rightarrow>\<^sub>a
       tuple20_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20\<close>
  apply sepref_to_hoare
  apply sep_auto
  done

lemma of_tuple20_id_hnr[sepref_fr_rules]:
  \<open>(return o of_tuple20, RETURN o of_tuple20_id) \<in>
     (tuple20_assn R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20)\<^sup>d \<rightarrow>\<^sub>a
       R1 *a R2 *a R3 *a R4 *a R5 *a R6 *a R7 *a R8 *a R9 *a R10 *a R11 *a R12 *a R13 *a R14 *a R15
         *a R16 *a R17 *a R18 *a R19 *a R20\<close>
  by sepref_to_hoare (sep_auto simp: of_tuple20_def split: tuple20.splits)

end
