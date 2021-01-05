theory Proof_System
imports "../basic_theory/Entailment"
begin

section \<open>Rules of the proof System\<close>
text \<open>The proof system at the core of the decision procedure is based on the following rules.\<close>

theorem axiom: "\<Pi>\<bar>emp \<turnstile> \<top>\<bar>emp"
by (auto simp: entails_def)

theorem inconsistent: "E\<noteq>\<^sub>pE \<and>\<^sub>p \<Pi>\<bar>\<Sigma> \<turnstile> F"
by (auto simp: entails_def)

theorem substitution: "subst x E (\<Pi>\<bar>\<Sigma>) \<turnstile> subst x E (\<Pi>'\<bar>\<Sigma>') \<Longrightarrow> \<acute>x`=\<^sub>pE \<and>\<^sub>p \<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
proof (rule entailment_lift)
  fix s h
  assume assm1: "subst x E (\<Pi>\<bar>\<Sigma>) \<turnstile> subst x E (\<Pi>'\<bar>\<Sigma>')"
  assume assm2: "(s,h)\<Turnstile>\<acute>x`=\<^sub>pE\<and>\<^sub>p\<Pi>\<bar>\<Sigma>"
  hence s_eq: "\<lbrakk>\<acute>x`\<rbrakk>s=\<lbrakk>E\<rbrakk>s" and "(s,h)\<Turnstile>\<Pi>\<bar>\<Sigma>" by fast+
  hence "(s,h)\<Turnstile>subst x E (\<Pi>\<bar>\<Sigma>)" using subst_sat_rev by blast
  with assm1 have "(s,h)\<Turnstile>subst x E (\<Pi>'\<bar>\<Sigma>')" by (simp add: entails_def)
  with s_eq show "(s,h)\<Turnstile>\<Pi>'\<bar>\<Sigma>'" using subst_sat by blast
qed

theorem eq_reflexivel: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> E=\<^sub>pE\<and>\<^sub>p\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by blast

theorem eq_reflexiver: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>\<Sigma> \<turnstile> E=\<^sub>pE\<and>\<^sub>p\<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by blast

theorem hypothesis: "P\<and>\<^sub>p\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> P\<and>\<^sub>p\<Pi>\<bar>\<Sigma> \<turnstile> P\<and>\<^sub>p\<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by blast

theorem empty_ls: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>ls(E,E)*\<Sigma>'"
unfolding entails_def by fastforce

theorem nil_not_lval: "E\<^sub>1\<noteq>\<^sub>pnil \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by force

theorem sep_conj_partial: "E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' 
  \<Longrightarrow> \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
proof (rule entailment_lift)
  fix s h
  assume assm1: "E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
  assume assm2: "(s,h)\<Turnstile>\<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma>"
  then obtain h1 h2 where "h=h1++h2" "h1\<bottom>h2" "(s,h1)\<Turnstile>Spat(E\<^sub>1\<longmapsto>E\<^sub>2)" "(s,h2)\<Turnstile>SpatF(E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma>)"
    by fastforce
  moreover then obtain h3 h4 where "h2=h3++h4" "h3\<bottom>h4" "(s,h3)\<Turnstile>Spat(E\<^sub>3\<longmapsto>E\<^sub>4)" by auto
  ultimately have "\<lbrakk>E\<^sub>1\<rbrakk>s \<noteq> \<lbrakk>E\<^sub>3\<rbrakk>s" by fastforce
  hence "(s,h)\<Turnstile>Pure(E\<^sub>1\<noteq>\<^sub>pE\<^sub>3)" by auto
  with assm2 have "(s,h)\<Turnstile>E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma>" by auto
  with assm1 show "(s,h)\<Turnstile>\<Pi>'\<bar>\<Sigma>'" by (simp add: entails_def)
qed

theorem frame: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>S * \<Sigma> \<turnstile> \<Pi>'\<bar>S * \<Sigma>'"
proof (rule entailment_lift)
  fix s h
  assume assm1: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
  assume assm2: "(s,h)\<Turnstile>\<Pi>\<bar>S * \<Sigma>"
  then obtain h1 h2 where sep_conj: "h=h1++h2" "h1\<bottom>h2" "(s,h1)\<Turnstile>Spat S" "(s,h2)\<Turnstile>SpatF \<Sigma>" by fast
  moreover {
    from assm2 have "(s,h)\<Turnstile>PureF \<Pi>" by fastforce
    from heap_puref[OF this] have "(s,h2)\<Turnstile>PureF \<Pi>" by simp
    with sep_conj(4) have "(s,h2)\<Turnstile>\<Pi>\<bar>\<Sigma>" by fast
    with assm1 have "(s,h2)\<Turnstile>\<Pi>'\<bar>\<Sigma>'" by (simp add: entails_def)
    hence "(s,h2)\<Turnstile>PureF \<Pi>'" "(s,h2)\<Turnstile>SpatF \<Sigma>'" by auto
  }
  ultimately show "(s,h)\<Turnstile>\<Pi>'\<bar>S * \<Sigma>'" using heap_puref by blast
qed

theorem non_empty_ls: "E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>ls(E\<^sub>2,E\<^sub>3) * \<Sigma>' 
  \<Longrightarrow> E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * \<Sigma> \<turnstile> \<Pi>'\<bar>ls(E\<^sub>1,E\<^sub>3) * \<Sigma>'"
proof (rule entailment_lift)
  fix s h
  assume assm1: "E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>ls(E\<^sub>2,E\<^sub>3) * \<Sigma>'"
  assume assm2: "(s,h)\<Turnstile>E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * \<Sigma>"
  then obtain h1 h2 where sep_conj:"h=h1++h2" "h1\<bottom>h2" "(s,h1)\<Turnstile>Spat(E\<^sub>1\<longmapsto>E\<^sub>2)" "(s,h2)\<Turnstile>SpatF \<Sigma>" 
    by fastforce
  then obtain v where hd: "\<lbrakk>E\<^sub>1\<rbrakk>s = Val v" "h1 = [v\<mapsto>\<lbrakk>E\<^sub>2\<rbrakk>s]" by fast
  from assm2 have "\<lbrakk>E\<^sub>1\<rbrakk>s\<noteq>\<lbrakk>E\<^sub>3\<rbrakk>s" by blast  
  {
    from assm2 have "(s,h)\<Turnstile>PureF (E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>)" by blast
    hence "(s,h2)\<Turnstile>PureF (E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>)" using heap_puref by auto
    with sep_conj(4) have "(s,h2)\<Turnstile>(E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>)\<bar>\<Sigma>" by auto
    with assm1 have "(s,h2)\<Turnstile>\<Pi>'\<bar>ls(E\<^sub>2,E\<^sub>3) * \<Sigma>'" by (simp add: entails_def)
  }
  then obtain h2_1 h2_2 where sep_conj2:"h2=h2_1++h2_2" "h2_1\<bottom>h2_2" "(s,h2_1)\<Turnstile>Spat (ls(E\<^sub>2,E\<^sub>3))" 
    "(s,h2_2)\<Turnstile>SpatF \<Sigma>'" by blast
  then obtain m where tail: "(s,h2_1)\<Turnstile>ls\<^sup>m(E\<^sub>2,E\<^sub>3)" by fast
  then obtain n where n: "n = Suc m" by simp
  obtain x where "x \<notin> fv E\<^sub>1 \<union> fv E\<^sub>2 \<union> fv E\<^sub>3" using fv_finite_expr fv_finite_un fv_other_x_un
    by (metis Un_iff fv_expr.elims singleton_iff)
  {
    hence "x \<notin> fv E\<^sub>2 \<union> fv E\<^sub>3" by fast
    from ls_extend_rhs[OF tail this] have tail_ext: "(s(x:=\<lbrakk>E\<^sub>2\<rbrakk>s),h2_1)\<Turnstile>ls\<^sup>m(E\<^sub>2,E\<^sub>3)" .
    have "\<lbrakk>E\<^sub>2\<rbrakk>s(x:=\<lbrakk>E\<^sub>2\<rbrakk>s) = \<lbrakk>\<acute>x`\<rbrakk>s(x:=\<lbrakk>E\<^sub>2\<rbrakk>s)"
      by (metis eval.simps(1) eval.simps(2) expr.exhaust fun_upd_apply)
    from ls_change_fst_general[OF tail_ext this] have "(s(x:=\<lbrakk>E\<^sub>2\<rbrakk>s),h2_1)\<Turnstile>ls\<^sup>m(\<acute>x`,E\<^sub>3)" .
  }
  from \<open>x \<notin> fv E\<^sub>1 \<union> fv E\<^sub>2 \<union> fv E\<^sub>3\<close> have "x \<notin> fv E\<^sub>1 \<union> fv E\<^sub>3" by simp
  from sep_conj sep_conj2 have "h1\<bottom>h2_1" by auto
  have "h1++h2_1=h1++h2_1" by simp
  from ListSegment[OF hd \<open>x \<notin> fv E\<^sub>1 \<union> fv E\<^sub>3\<close> \<open>h1\<bottom>h2_1\<close> this \<open>(s(x:=\<lbrakk>E\<^sub>2\<rbrakk>s),h2_1)\<Turnstile>ls\<^sup>m(\<acute>x`,E\<^sub>3)\<close> n 
    \<open>\<lbrakk>E\<^sub>1\<rbrakk>s\<noteq>\<lbrakk>E\<^sub>3\<rbrakk>s\<close>] have "(s,h1++h2_1)\<Turnstile>ls\<^sup>n(E\<^sub>1,E\<^sub>3)" .
  {
    hence "(s,h1++h2_1)\<Turnstile>Spat (ls(E\<^sub>1,E\<^sub>3))" by auto
    moreover from sep_conj(1,2) sep_conj2(1,2) have "h=h1++h2_1++h2_2" "h1++h2_1\<bottom>h2_2" by auto
    ultimately have "(s,h)\<Turnstile>SpatF (ls(E\<^sub>1,E\<^sub>3) * \<Sigma>')" using sep_conj2(4) by blast
  }
  moreover from \<open>(s,h2)\<Turnstile>\<Pi>'\<bar>ls(E\<^sub>2,E\<^sub>3) * \<Sigma>'\<close> have "(s,h)\<Turnstile>PureF \<Pi>'" using heap_puref by fast
  ultimately show "(s,h)\<Turnstile>\<Pi>'\<bar>ls(E\<^sub>1,E\<^sub>3) * \<Sigma>'" by blast
qed
end