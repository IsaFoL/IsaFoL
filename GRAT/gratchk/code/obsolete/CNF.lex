type lexresult = int


val linenum = ref 1
val error = fn x => (print("Error in line " ^ IntInf.toString(!linenum) ^ ": " ^ x ^ "\n"); raise (Fail "Error"))

exception EOF

val eof = fn () => raise EOF

%%
%structure CNF_lex
digit=[0-9];
ws=([\ \t]+);
%%
\n => (linenum := !linenum + 1; lex());
{ws} => (lex());
"c".* => (lex());
"p".* => (lex());
"s".* => (lex());
"v" => (lex ());
"GRAT".* => (lex());
"-"?{digit}+ => (valOf (Int.fromString yytext));
. => (error ("bad character " ^ yytext));
