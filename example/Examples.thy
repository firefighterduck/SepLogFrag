theory Examples
imports "../Sep_Log_Frag"
begin 

section \<open>Examples\<close>
text \<open>In this section, some example entailments are either proven or disproven by usage of
      the decision procedures rules.\<close>

subsection \<open>Auxiliary lemmata:\<close>
lemma spatial_commut_entail: "\<Pi>\<bar>(s1*s2*\<Sigma>) \<turnstile> consequent \<Longrightarrow> \<Pi>\<bar>(s2*s1*\<Sigma>) \<turnstile> consequent"
using entails_def spatial_commut_form by force
lemma pure_commut_entail: "(p1\<and>\<^sub>pp2\<and>\<^sub>p\<Pi>)\<bar>\<Sigma> \<turnstile> consequent \<Longrightarrow> (p2\<and>\<^sub>pp1\<and>\<^sub>p\<Pi>)\<bar>\<Sigma> \<turnstile> consequent"
using entails_def pure_commut_form by simp

subsection \<open>First example (cf. \cite{seminar-paper} 2.4)\<close>
lemma "[\<acute>''x''`\<noteq>\<^sub>p\<acute>p`]\<bar>\<acute>''x''`\<longmapsto>\<acute>''y''` * \<acute>''y''`\<longmapsto>nil * emp \<turnstile> []\<bar>[ls(\<acute>''x''`,nil)]"
\<comment> \<open>First enrich the formula to contain all necessary inequalities, ...\<close>
apply (rule nil_not_lval)
apply (rule spatial_commut_entail)  (* Reordering *)
apply (rule nil_not_lval)
\<comment> \<open>... then destructure the ls step by step, ...\<close>
apply (rule pure_commut_entail)     (* Reordering *)
apply (rule spatial_commut_entail)  (* Reordering *)
apply (rule non_empty_ls)
apply (rule pure_commut_entail)     (* Reordering *)
apply (rule non_empty_ls)
\<comment> \<open>... then exchange the empty ls with emp ...\<close>
apply (rule empty_ls)
\<comment> \<open>... and finally prove the entailment with the axiom. \<close>
by (rule axiom)

subsection \<open>Second example (cf. \cite{seminar-paper} 2.4)\<close>
text \<open>At first try to prove this by applying the decision procedure as far as possible.\<close>
lemma "(\<top>\<bar>\<acute>''x''`\<longmapsto>nil * \<acute>''y''`\<longmapsto>nil * emp \<turnstile> [\<acute>''x''`=\<^sub>p\<acute>''y''`]\<bar>[\<acute>''y''`\<longmapsto>nil])"
\<comment> \<open>First enrich the formula to contain all necessary inequalities, ...\<close>
apply (rule sep_conj_partial)
apply (rule nil_not_lval)
apply (rule spatial_commut_entail)  (* Reordering *)
apply (rule nil_not_lval)
\<comment> \<open>... then remove the duplicate $y\mapsto nil$ ...\<close>
apply (rule frame)
\<comment> \<open>... and there is no applicable rule and so the decision procedure halts.\<close>
sorry

text \<open>The resulting transformed goal can no be proven wrong with a counter example.\<close>
lemma "\<not>([\<acute>''y''`\<noteq>\<^sub>pnil, \<acute>''x''`\<noteq>\<^sub>pnil, \<acute>''x''`\<noteq>\<^sub>p\<acute>''y''`]\<bar>[\<acute>''x''`\<longmapsto>nil] \<turnstile> [\<acute>''x''`=\<^sub>p\<acute>''y''`]\<bar>emp)" 
  (is "\<not>(?ant \<turnstile> ?cons)")
proof
  assume "?ant \<turnstile> ?cons"
  hence hyp: "\<forall>s h. (s,h)\<Turnstile>?ant \<longrightarrow> (s,h)\<Turnstile>?cons" using entails_def by simp
  define s h where s_def:"(s::stack) = ((\<lambda>_. Nilval)(''x'':=Val 5))(''y'':=Val 23)" 
    and h_def: "(h::heap) = [5\<mapsto>Nilval]" 
  have "(s,h)\<Turnstile>?ant" proof \<comment> \<open>The state (s,h) satisfies the antecedent ...\<close>
    show "(s,h)\<Turnstile>PureF (\<acute>''y''`\<noteq>\<^sub>pnil \<and>\<^sub>p \<acute>''x''`\<noteq>\<^sub>pnil \<and>\<^sub>p \<acute>''x''`\<noteq>\<^sub>p\<acute>''y''` \<and>\<^sub>p \<top>)" proof
      show "(s,h)\<Turnstile>Pure (\<acute>''y''`\<noteq>\<^sub>pnil)" by (simp add: NeqSat s_def)
    next
      show "(s,h)\<Turnstile>PureF (\<acute>''x''`\<noteq>\<^sub>pnil \<and>\<^sub>p \<acute>''x''`\<noteq>\<^sub>p\<acute>''y''` \<and>\<^sub>p \<top>)" proof
        show "(s,h)\<Turnstile>Pure (\<acute>''x''`\<noteq>\<^sub>pnil)" by (simp add: NeqSat s_def)
      next
        show "(s,h)\<Turnstile>PureF (\<acute>''x''`\<noteq>\<^sub>p\<acute>''y''` \<and>\<^sub>p \<top>)" proof
          show "(s,h)\<Turnstile>Pure (\<acute>''x''`\<noteq>\<^sub>p\<acute>''y''`)" by (simp add: NeqSat s_def)
        next
          show "(s,h)\<Turnstile>PureF (\<top>)" by auto
        qed
      qed
    qed
  next
    define h1 h2 where h_defs: "h1 = h" "(h2::heap) = Map.empty"
    hence "h1\<bottom>h2" "h=h1++h2" by simp_all
    moreover from h_defs have "(s,h2)\<Turnstile>SpatF emp" by auto
    moreover have "(s,h1)\<Turnstile>Spat (\<acute>''x''`\<longmapsto>nil)" proof
      show "\<lbrakk>\<acute>''x''`\<rbrakk>s = Val 5" using s_def by simp
    next
      show "h1 = [5 \<mapsto> \<lbrakk>nil\<rbrakk>s]" using h_defs h_def by simp
    qed
    ultimately show "(s,h)\<Turnstile>SpatF (\<acute>''x''`\<longmapsto>nil * emp)" by blast
  qed
  with hyp have "(s,h)\<Turnstile>?cons" by simp
  moreover have contradiction: "\<not>(s,h)\<Turnstile>?cons" proof \<comment> \<open>... but not the consequent.\<close>
    assume "(s,h)\<Turnstile>?cons"
    hence "(s,h)\<Turnstile>Pure (\<acute>''x''` =\<^sub>p \<acute>''y''`)" by auto
    hence "\<lbrakk>\<acute>''x''`\<rbrakk>s = \<lbrakk>\<acute>''y''`\<rbrakk>s" by auto
    moreover from s_def have "\<lbrakk>\<acute>''x''`\<rbrakk>s \<noteq> \<lbrakk>\<acute>''y''`\<rbrakk>s" by simp
    ultimately show False by simp
  qed
  ultimately show False by simp  
qed
end