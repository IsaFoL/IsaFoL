section {* More Terms and Literals *}

theory ExtraSnippets imports Main begin

text_raw {*\DefineSnippet{snippetname}{*}
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<forall> A. \<exists> a. A = f a" using surj_def by metis
  then have "\<exists> a. {x. x \<notin> f x} = f a" by blast
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  then show "False" by blast
qed
text_raw {*}%EndSnippet*}

end

