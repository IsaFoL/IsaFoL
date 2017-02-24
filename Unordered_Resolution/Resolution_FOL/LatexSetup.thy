theory LatexSetup imports 
    TermsAndLiterals
    Tree
    Resolution
    Completeness
    Examples
begin
    
(*\newcommand{\subls}{\,\, \raisebox{-0.1ex}{\scalebox{1.35}{$\cdot$}}{\raisebox{-0.3ex}{$_{\hspace{-0.4ex}\mathrm{ls}}\,$}}} *)

(* \newcommand{\subl}{\,\, \raisebox{-0.1ex}{\scalebox{1.35}{$\cdot$}}{\raisebox{-0.3ex}{$_{\hspace{-0.4ex}\mathrm{l}}\,$}}} *)
    
(* \newcommand{\varsls}{vars_{\mathrm{ls}}} *)
    
(* \newcommand{\unifierls}{unifier_{\hspace{0.15ex}\mathrm{ls}}} *)
    
(* \newcommand{\mguls}{mgu_{\mathrm{ls}}} *)
notation (latex) "mgu\<^sub>l\<^sub>s" ("_\<^latex>\<open>$\\mathit{\\mguls}$\<close>")
    
(* \newcommand{\groundl}{ground_{\mathrm{l}}} *)
notation (latex) "ground\<^sub>l" ("_\<^latex>\<open>$\\mathit{\\groundl}$\<close>")
    
(* \newcommand{\groundls}{ground_{\mathrm{ls}}} *)
notation (latex) "ground\<^sub>l\<^sub>s" ("_\<^latex>\<open>$\\mathit{\\groundls}$\<close>")
    
(* \newcommand{\instanceofls}{instance\dash of_{\mathrm{ls}}} *)
notation (latex) "instance_of\<^sub>l\<^sub>s" ("_\<^latex>\<open>$\\mathit{\\instanceofls}$\<close>")
    
(* \newcommand{\evalt}{eval_{\hspace{0.15ex}\mathrm{t}}} *)
notation (latex) "eval\<^sub>t" ("_\<^latex>\<open>$\\mathit{\\evalt}$\<close>")
    
(* \newcommand{\evalts}{eval_{\mathrm{ts}}} *)
notation (latex) "eval\<^sub>t\<^sub>s" ("_\<^latex>\<open>$\\mathit{\\evalts}$\<close>")
  
(* \newcommand{\evall}{eval_{\mathrm{l}}} *)
notation (latex) "eval\<^sub>l" ("_\<^latex>\<open>$\\mathit{\\evall}$\<close>")
    
(* \newcommand{\evalc}{eval_{\mathrm{c}}} *)
notation (latex) "eval\<^sub>c" ("_\<^latex>\<open>$\\mathit{\\evalc}$\<close>")
    
(* \newcommand{\evalcs}{eval_{\mathrm{cs}}} *)
notation (latex) "eval\<^sub>c\<^sub>s" ("_\<^latex>\<open>$\\mathit{\\evalcs}$\<close>")
    
(* \newcommand{\falsifiesl}{falsifies_{\mathrm{l}}} *)
notation (latex) "falsifies\<^sub>l" ("_\<^latex>\<open>$\\mathit{\\falsifiesl}$\<close>")
    
(* \newcommand{\falsifiesg}{falsifies_{\mathrm{g}}} *)
notation (latex) "falsifies\<^sub>g" ("_\<^latex>\<open>$\\mathit{\\falsifiesg}$\<close>")
    
(* \newcommand{\falsifiesc}{falsifies_{\mathrm{c}}} *)
notation (latex) "falsifies\<^sub>c" ("_\<^latex>\<open>$\\mathit{\\falsifiesc}$\<close>")
    
(* \newcommand{\compl}{{\mathrm{c}}} *)
    
(* \newcommand{\compls}{{\mathrm{C}}} *)
    
(* \newcommand{\Cone}{C_\mathrm{1}} *)
    
(* \newcommand{\Ctwo}{C_\mathrm{2}} *)
    
(* \newcommand{\Bone}{B_\mathrm{1}} *)
    
(* \newcommand{\Btwo}{B_\mathrm{2}} *)
    
(* \newcommand{\Lone}{L_\mathrm{1}} *)
    
(* \newcommand{\Ltwo}{L_\mathrm{2}} *)
    
(* \newcommand{\stdone}{std_\mathrm{1}} *)
notation (latex) "std\<^sub>1" ("_\<^latex>\<open>$\\mathit{\\stdone}$\<close>")
    
(* \newcommand{\stdtwo}{std_\mathrm{2}} *)
notation (latex) "std\<^sub>2" ("_\<^latex>\<open>$\\mathit{\\stdtwo}$\<close>")
    
end
