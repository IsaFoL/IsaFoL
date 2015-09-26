theory CW_Sudoku
imports Main Partial_Annotated_Clausal_Logic

begin

type_synonym digit = int

definition valid :: "digit => digit => digit => digit => digit => digit => digit => digit => digit => bool" where

  "valid x1 x2 x3 x4 x5 x6 x7 x8 x9 ==
    (x1 \<noteq> x2) \<and> (x1 \<noteq> x3) \<and> (x1 \<noteq> x4) \<and> (x1 \<noteq> x5) \<and> (x1 \<noteq> x6) \<and> (x1 \<noteq> x7) \<and> (x1 \<noteq> x8) \<and> (x1 \<noteq> x9)
    \<and> (x2 \<noteq> x3) \<and> (x2 \<noteq> x4) \<and> (x2 \<noteq> x5) \<and> (x2 \<noteq> x6) \<and> (x2 \<noteq> x7) \<and> (x2 \<noteq> x8) \<and> (x2 \<noteq> x9)
    \<and> (x3 \<noteq> x4) \<and> (x3 \<noteq> x5) \<and> (x3 \<noteq> x6) \<and> (x3 \<noteq> x7) \<and> (x3 \<noteq> x8) \<and> (x3 \<noteq> x9)
    \<and> (x4 \<noteq> x5) \<and> (x4 \<noteq> x6) \<and> (x4 \<noteq> x7) \<and> (x4 \<noteq> x8) \<and> (x4 \<noteq> x9)
    \<and> (x5 \<noteq> x6) \<and> (x5 \<noteq> x7) \<and> (x5 \<noteq> x8) \<and> (x5 \<noteq> x9)
    \<and> (x6 \<noteq> x7) \<and> (x6 \<noteq> x8) \<and> (x6 \<noteq> x9)
    \<and> (x7 \<noteq> x8) \<and> (x7 \<noteq> x9)
    \<and> (x8 \<noteq> x9)
    \<and> x1 \<in> set [1..9]
    \<and> x2 \<in> set [1..9]
    \<and> x3 \<in> set [1..9]
    \<and> x4 \<in> set [1..9]
    \<and> x5 \<in> set [1..9]
    \<and> x6 \<in> set [1..9]
    \<and> x7 \<in> set [1..9]
    \<and> x8 \<in> set [1..9]
    \<and> x9 \<in> set [1..9]"

definition sudoku :: "digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit => bool" where

  "sudoku x11 x12 x13 x14 x15 x16 x17 x18 x19
          x21 x22 x23 x24 x25 x26 x27 x28 x29
          x31 x32 x33 x34 x35 x36 x37 x38 x39
          x41 x42 x43 x44 x45 x46 x47 x48 x49
          x51 x52 x53 x54 x55 x56 x57 x58 x59
          x61 x62 x63 x64 x65 x66 x67 x68 x69
          x71 x72 x73 x74 x75 x76 x77 x78 x79
          x81 x82 x83 x84 x85 x86 x87 x88 x89
          x91 x92 x93 x94 x95 x96 x97 x98 x99 ==

       valid x11 x12 x13 x14 x15 x16 x17 x18 x19
     \<and> valid x21 x22 x23 x24 x25 x26 x27 x28 x29
     \<and> valid x31 x32 x33 x34 x35 x36 x37 x38 x39
     \<and> valid x41 x42 x43 x44 x45 x46 x47 x48 x49
     \<and> valid x51 x52 x53 x54 x55 x56 x57 x58 x59
     \<and> valid x61 x62 x63 x64 x65 x66 x67 x68 x69
     \<and> valid x71 x72 x73 x74 x75 x76 x77 x78 x79
     \<and> valid x81 x82 x83 x84 x85 x86 x87 x88 x89
     \<and> valid x91 x92 x93 x94 x95 x96 x97 x98 x99

     \<and> valid x11 x21 x31 x41 x51 x61 x71 x81 x91
     \<and> valid x12 x22 x32 x42 x52 x62 x72 x82 x92
     \<and> valid x13 x23 x33 x43 x53 x63 x73 x83 x93
     \<and> valid x14 x24 x34 x44 x54 x64 x74 x84 x94
     \<and> valid x15 x25 x35 x45 x55 x65 x75 x85 x95
     \<and> valid x16 x26 x36 x46 x56 x66 x76 x86 x96
     \<and> valid x17 x27 x37 x47 x57 x67 x77 x87 x97
     \<and> valid x18 x28 x38 x48 x58 x68 x78 x88 x98
     \<and> valid x19 x29 x39 x49 x59 x69 x79 x89 x99

     \<and> valid x11 x12 x13 x21 x22 x23 x31 x32 x33
     \<and> valid x14 x15 x16 x24 x25 x26 x34 x35 x36
     \<and> valid x17 x18 x19 x27 x28 x29 x37 x38 x39
     \<and> valid x41 x42 x43 x51 x52 x53 x61 x62 x63
     \<and> valid x44 x45 x46 x54 x55 x56 x64 x65 x66
     \<and> valid x47 x48 x49 x57 x58 x59 x67 x68 x69
     \<and> valid x71 x72 x73 x81 x82 x83 x91 x92 x93
     \<and> valid x74 x75 x76 x84 x85 x86 x94 x95 x96
     \<and> valid x77 x78 x79 x87 x88 x89 x97 x98 x99"


consts Q :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
definition P :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"P i j k \<longleftrightarrow> Q i j k"

text \<open>Naming convention:
  * i j means that d is the value at position (i, j)\<close>

definition at_least_one_value_per_cell where
  "at_least_one_value_per_cell i j = map (\<lambda>d. Pos (P i j d)) [1..9]"

value "at_least_one_value_per_cell i j"

definition no_more_than_one_value where
"no_more_than_one_value i j =
   (concat (map (\<lambda>k. map (\<lambda>k'. [Neg (P i j k'), Neg (P i j k)]) [k+1..9]) [1..9 -1]))"

value "no_more_than_one_value i j"

definition no_more_than_one_value_everywhere where
"no_more_than_one_value_everywhere =
  concat (map (\<lambda>(i, j). no_more_than_one_value i j)
    (List.product [1..9] [1..9]))"

value "no_more_than_one_value_everywhere"

definition value_at_least_once_in_line where
"value_at_least_once_in_line j d = map (\<lambda>i. Pos (P i j d)) [1..9]"

abbreviation values_at_least_once_in_line where
"values_at_least_once_in_line j \<equiv> map (value_at_least_once_in_line j) [1..9]"

value "values_at_least_once_in_line j"

definition values_at_least_once_all_lines where
"values_at_least_once_all_lines = concat (map values_at_least_once_in_line [1..9])"

value "values_at_least_once_all_lines"


definition value_at_least_once_in_col where
"value_at_least_once_in_col i d = map (\<lambda>j. Pos (P i j d)) [1..9]"

value "value_at_least_once_in_col i d"

definition values_at_least_once_in_col where
"values_at_least_once_in_col i = map (value_at_least_once_in_col i) [1..9]"


definition values_at_least_once_in_cols where
"values_at_least_once_in_cols = concat (map values_at_least_once_in_col [1..9])"

value "values_at_least_once_in_cols"

abbreviation value_at_least_once_in_box where
"value_at_least_once_in_box i j d \<equiv> map (\<lambda>(i, j). Pos (P i j d))
  [(i, j),   (i+1, j),   (i+2, j),
   (i, j+1), (i+1, j+1), (i+2, j+1),
   (i, j+2), (i+1, j+2), (i+2, j+2)
]"

value "value_at_least_once_in_box i j d"
value "List.product (map (\<lambda>i. i *3+1) [0..3-1]) (map (\<lambda>i. i *3+1) [0..3-1])"
abbreviation values_at_least_once_in_box where
"values_at_least_once_in_box d \<equiv>
  map (\<lambda>(i, j). value_at_least_once_in_box i j d)
    (List.product (map (\<lambda>i. i *3+1) [0..3-1]) (map (\<lambda>i. i *3+1) [0..3-1]))"

definition values_at_least_once_in_boxes where
"values_at_least_once_in_boxes = concat (map values_at_least_once_in_box [1..9])"

value "values_at_least_once_in_boxes"

value "values_at_least_once_in_box 2"
lemma
   aset19:"a \<in> set [1..9] \<longleftrightarrow> a =1 \<or> a = 2 \<or> a = 3 \<or> a = 4 \<or> a = 5 \<or> a = 6 \<or> a = 7 \<or> a = 8 \<or> a = 9"
by auto


lemma map19: "map f [1::int..9] = [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9]"
unfolding upt.simps sorry
(*)
value " values_at_least_once_in_boxes @
     values_at_least_once_in_cols @
     values_at_least_once_all_lines @
    no_more_than_one_value_everywhere"
definition "tall ls \<equiv> fold (op \<and>) (map (\<lambda>l. fold (op \<or>) l False) ls) True"
*)

end