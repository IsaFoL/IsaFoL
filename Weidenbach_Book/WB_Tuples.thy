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

NB: tuples are less efficient than C structures: every element is aligned on a 64-bit pointer. This
is why compressing a \<^typ>\<open>uint32\<close> and a \<^typ>\<open>bool\<close> can be worth it (e.g., critical loop).

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




end
