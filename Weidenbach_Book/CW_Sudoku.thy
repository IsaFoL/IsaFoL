theory CW_Sudoku
imports Main (*"~~/src/HOL/ex/Sudoku"*)
begin
consts Q :: "int \<Rightarrow> int \<Rightarrow> int"
definition P :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"P i j k \<longleftrightarrow> Q i j = k "

text \<open>Naming convention:
  * n is the sizeof a box: the full grid has size n*n (i.e. for normal sudoku we have n=3)
  * i j d means that d is the value at position (i, j)\<close>
definition at_least_one_value_per_cell where
  "at_least_one_value_per_cell i j n = map ((P i j)) [1..n]"
  
value "at_least_one_value_per_cell i j 4" 
  
definition no_more_than_one_value where
  "no_more_than_one_value i j n = map (\<lambda>k. map (\<lambda>k'. [~P i j k', \<not>P i j k]) [k+1..n*n]) [1..n*n-1]"
  
value "no_more_than_one_value i j 2" 
  
definition value_at_least_once_in_line where
"value_at_least_once_in_line j n d = map (\<lambda>i. P i j d) [1..n*n]"

value "value_at_least_once_in_line j 2 d" 

definition values_at_least_once_in_line where
"values_at_least_once_in_line j n = map (value_at_least_once_in_line j n) [1..n*n]"

value "values_at_least_once_in_line j 2" 


definition value_at_least_once_in_col where
"value_at_least_once_in_col i n d = map (\<lambda>j. P i j d) [1..n*n]"

value "value_at_least_once_in_col i 2 d" 

definition values_at_least_once_in_col where
"values_at_least_once_in_col i n = map (value_at_least_once_in_col i n) [1..n*n]"

value "values_at_least_once_in_col i 2"



end