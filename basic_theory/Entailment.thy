theory Entailment
imports Assertion_Semantics
begin

section \<open>Entailments\<close>
text \<open>Entailments formalize single deduction steps in separation logic.\<close>

text \<open>An entailment describes that the consequent is satisfied by at least all states that also 
      satisfy the antecedent.\<close>
definition entails :: "formula \<Rightarrow> formula \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "antecedent \<turnstile> consequent \<equiv> (\<forall>s h. (s,h)\<Turnstile>antecedent \<longrightarrow> (s,h)\<Turnstile>consequent)"

text \<open>Auxiliary lemma to lift reasoning from Isabelle/HOL to Isabelle/Pure\<close>
lemma entailment_lift: "(\<And>s h. (s,h)\<Turnstile>\<Pi>\<Sigma> \<Longrightarrow> (s,h)\<Turnstile>\<Pi>\<Sigma>') \<Longrightarrow> \<Pi>\<Sigma> \<turnstile> \<Pi>\<Sigma>'"
  unfolding entails_def using HOL.impI HOL.allI by simp

lemma entailment_lift_rev: "\<Pi>\<Sigma> \<turnstile> \<Pi>\<Sigma>' \<Longrightarrow> (\<And>s h. (s,h)\<Turnstile>\<Pi>\<Sigma> \<Longrightarrow> (s,h)\<Turnstile>\<Pi>\<Sigma>')"
  unfolding entails_def using HOL.impI HOL.allI by simp
  
lemma entailment_trans: "\<lbrakk>\<Pi>\<Sigma> \<turnstile> \<Pi>\<Sigma>'; \<Pi>\<Sigma>' \<turnstile> \<Pi>\<Sigma>''\<rbrakk> \<Longrightarrow> \<Pi>\<Sigma> \<turnstile> \<Pi>\<Sigma>''"
by (simp add: entails_def)  
  
subsection \<open>Example entailments from the paper\<close>

text \<open>Entailments are reflexive with regard to equality.\<close>
lemma eq_refl: "[\<acute>x`=\<^sub>p\<acute>y`, E=\<^sub>pF] \<bar> [\<acute>x`\<longmapsto>E] \<turnstile> Spat (\<acute>y`\<longmapsto>F)"
proof(rule entailment_lift)
  fix s h
  assume antecedent: "(s,h)\<Turnstile>[\<acute>x`=\<^sub>p\<acute>y`, E=\<^sub>pF] \<bar> [\<acute>x`\<longmapsto>E]"
  hence "(s,h)\<Turnstile> PureF [\<acute>x`=\<^sub>p\<acute>y`, E=\<^sub>pF]" by auto
  hence "\<lbrakk>\<acute>x`\<rbrakk>s = \<lbrakk>\<acute>y`\<rbrakk>s" "\<lbrakk>E\<rbrakk>s = \<lbrakk>F\<rbrakk>s" by blast+
  moreover from sing_heap antecedent have "(s,h)\<Turnstile>Spat (\<acute>x`\<longmapsto>E)" by auto
  ultimately show "(s,h)\<Turnstile>Spat (\<acute>y`\<longmapsto>F)" by fastforce
qed

text \<open>In the following some simple entailments for list segment are shown to hold.\<close>
lemma emp_entails_ls: "[x=\<^sub>py] \<bar> emp \<turnstile> Spat (ls(x,y))"
proof (rule entailment_lift)
  fix s h
  assume "(s, h) \<Turnstile> [x=\<^sub>py] \<bar> emp"
  hence "\<lbrakk>x\<rbrakk>s = \<lbrakk>y\<rbrakk>s" "dom h = {}" by auto
  hence "(s,h)\<Turnstile>ls\<^sup>0(x,y)" by auto
  thus "(s, h) \<Turnstile> Spat (ls(x, y))" by auto
qed

lemma one_entails_ls: "[x\<noteq>\<^sub>py] \<bar> [x\<longmapsto>y] \<turnstile> Spat (ls(x,y))"
proof (rule entailment_lift)
  define xs where xs: "xs = - (fv x \<union> fv y)"
  fix s h
  assume antecedent: "(s,h)\<Turnstile>[x\<noteq>\<^sub>py] \<bar> [x \<longmapsto> y]"
  hence "\<lbrakk>x\<rbrakk>s\<noteq>\<lbrakk>y\<rbrakk>s" by blast
  moreover from antecedent obtain v where "\<lbrakk>x\<rbrakk>s = Val v" "h = [v\<mapsto>\<lbrakk>y\<rbrakk>s]" by fastforce
  moreover have "h=h++Map.empty" "h \<bottom> Map.empty" by auto
  moreover have "\<forall>x' \<in> xs. (s(x':=\<lbrakk>y\<rbrakk>s),Map.empty)\<Turnstile>ls\<^sup>0(\<acute>x'`,y)"
    by (metis EmptyLs dom_empty eval.simps(1) eval.simps(2) fun_upd_apply fv_expr.cases)
  moreover have "1 = Suc 0" by simp
  moreover from xs have "xs \<subseteq> - (fv x \<union> fv y)" by simp
  ultimately have "(s,h)\<Turnstile>ls\<^sup>1(x,y)" using ListSegment by blast
  thus "(s,h)\<Turnstile>Spat(ls(x, y))" by blast
qed
end