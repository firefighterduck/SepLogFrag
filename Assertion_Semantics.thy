theory Assertion_Semantics
imports Assertion_Lang Assertion_Misc
begin

section \<open>Semantics\<close>
text \<open> Defines the syntax for the assertion language formulae\<close>

subsection \<open>Satisfaction predicate\<close>
text \<open>Satisfactions describe the semantics of the assertion language\<close>

fun eval :: "expr \<Rightarrow> stack \<Rightarrow> val" where
  "eval (nil) s = Nilval" |
  "eval (\<acute>x`) s = s x"
notation eval ("\<lbrakk>_\<rbrakk>_" [60, 61] 61)

text \<open>A satisfaction with a ls segment holds iff there exists a path of heap cells that 
  point to each other and that form a super list of the given segment.\<close>
inductive ls_ind :: "state \<Rightarrow> nat \<Rightarrow> (expr \<times> expr) \<Rightarrow> bool" ("_\<Turnstile>ls\<^sup>__" 50) where
EmptyLs: "\<lbrakk>e1\<rbrakk>s = \<lbrakk>e2\<rbrakk>s \<Longrightarrow> dom h = {} \<Longrightarrow> (s,h)\<Turnstile>ls\<^sup>0(e1,e2)" |
ListSegment: "\<lbrakk>e1\<rbrakk>s = Val v \<Longrightarrow> h1 = [v\<mapsto>v'] \<Longrightarrow> x \<notin> fv e1 \<union> fv e2 \<Longrightarrow> h1 \<bottom> h2 \<Longrightarrow> h = h1++h2
   \<Longrightarrow> (s(x:=v'),h2)\<Turnstile>ls\<^sup>n(\<acute>x`,e2) \<Longrightarrow> m = Suc n \<Longrightarrow> \<lbrakk>e1\<rbrakk>s \<noteq> \<lbrakk>e2\<rbrakk>s \<Longrightarrow> (s,h)\<Turnstile>ls\<^sup>m(e1,e2)"
  
inductive satisfaction :: "state \<Rightarrow> formula \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
EqSat: "\<lbrakk>e1\<rbrakk>s=\<lbrakk>e2\<rbrakk>s \<Longrightarrow> (s,h)\<Turnstile>Pure(e1=\<^sub>pe2)" |
NeqSat: "\<lbrakk>e1\<rbrakk>s\<noteq>\<lbrakk>e2\<rbrakk>s \<Longrightarrow> (s,h)\<Turnstile>Pure(e1\<noteq>\<^sub>pe2)" |
TrueSat: "(s,h)\<Turnstile>PureF []" |
ConjSat: "(s,h)\<Turnstile>Pure P \<Longrightarrow> (s,h)\<Turnstile>PureF \<Pi> \<Longrightarrow> (s,h)\<Turnstile>PureF(P \<and>\<^sub>p \<Pi>)" |
PointsToSat: "\<lbrakk>\<lbrakk>e1\<rbrakk>s = Val v; h = [v\<mapsto>\<lbrakk>e2\<rbrakk>s]\<rbrakk> \<Longrightarrow> (s,h)\<Turnstile>Spat(e1 \<longmapsto> e2)" |
EmpSat: "h = Map.empty \<Longrightarrow> (s,h)\<Turnstile>SpatF emp" |
SepConjSat: "h1 \<bottom> h2 \<Longrightarrow> h = h1++h2 \<Longrightarrow> (s,h1)\<Turnstile>Spat S \<Longrightarrow> (s,h2)\<Turnstile>SpatF \<Sigma>
   \<Longrightarrow> (s,h)\<Turnstile>SpatF(S * \<Sigma>)" |
FormSat: "(s,h)\<Turnstile>PureF \<Pi> \<Longrightarrow> (s,h)\<Turnstile>SpatF \<Sigma> \<Longrightarrow> (s,h)\<Turnstile>(\<Pi> \<bar> \<Sigma>)" |
LsSat: "(s,h)\<Turnstile>ls\<^sup>n(e1,e2) \<Longrightarrow> (s,h)\<Turnstile>Spat(ls(e1,e2))"

declare ls_ind.intros[intro]
declare satisfaction.intros[intro]
lemmas ls_induct = ls_ind.induct[split_format(complete)]
lemmas sat_induct = satisfaction.induct[split_format(complete)]

inductive_cases [elim]: "(s,h)\<Turnstile>ls\<^sup>0(e1,e2)" "(s,h)\<Turnstile>ls\<^sup>m(e1,e2)"
inductive_cases [elim]: "(s,h)\<Turnstile>Pure(e1=\<^sub>pe2)" "(s,h)\<Turnstile>Pure(e1\<noteq>\<^sub>pe2)" "(s,h)\<Turnstile>PureF []" 
  "(s,f)\<Turnstile>PureF(P \<and>\<^sub>p \<Pi>)" "(s,h)\<Turnstile>Spat(e1 \<longmapsto> e2)" "(s,h)\<Turnstile>SpatF emp" "(s,h)\<Turnstile>SpatF(S * \<Sigma>)"
  "(s,h)\<Turnstile>(\<Pi> \<bar> \<Sigma>)" "(s,h)\<Turnstile>Spat(ls(e1,e2))"

subsection \<open>Satisfaction properties\<close>
text \<open>There are a number of helpful properties that follow from the satisfaction definition\<close>

text \<open>Satisfaction is decidable, cf. Lemma 1\<close>
corollary sat_decidable: "(s,h)\<Turnstile>F \<or> \<not> (s,h)\<Turnstile>F"
by simp

text \<open>Separating conjunctions are only allowed on distinct heap parts\<close>
corollary sep_conj_ortho: "\<nexists>s h. (s,h) \<Turnstile> [\<acute>x`=\<^sub>p\<acute>y`] \<bar> [\<acute>x` \<longmapsto> xv, \<acute>y` \<longmapsto> yv]"
proof
  assume "\<exists>s h. (s, h) \<Turnstile> [\<acute>x` =\<^sub>p \<acute>y`] \<bar> [\<acute>x` \<longmapsto> xv, \<acute>y` \<longmapsto> yv]"
  then obtain s h where "(s,h) \<Turnstile> [\<acute>x`=\<^sub>p\<acute>y`] \<bar> [\<acute>x` \<longmapsto> xv, \<acute>y` \<longmapsto> yv]" by auto
  hence "(s,h)\<Turnstile>PureF [\<acute>x`=\<^sub>p\<acute>y`]" and spatf: "(s,h) \<Turnstile> SpatF [\<acute>x` \<longmapsto> xv, \<acute>y` \<longmapsto> yv]" by auto
  {
    hence "(s,h)\<Turnstile>Pure(\<acute>x`=\<^sub>p\<acute>y`)" by auto
    hence "\<lbrakk>\<acute>x`\<rbrakk>s = \<lbrakk>\<acute>y`\<rbrakk>s" by auto
  }
  from spatf obtain h1 h2 where "h1 \<bottom> h2" "h = h1++h2" "(s,h1)\<Turnstile>Spat (\<acute>x`\<longmapsto>xv)" 
    "(s,h2)\<Turnstile>SpatF [\<acute>y`\<longmapsto>yv]" by blast
  from \<open>(s,h1)\<Turnstile>Spat (\<acute>x`\<longmapsto>xv)\<close> obtain v where "\<lbrakk>\<acute>x`\<rbrakk>s = Val v" "dom h1 = {v}" by auto
  from \<open>(s,h2)\<Turnstile>SpatF [\<acute>y`\<longmapsto>yv]\<close> obtain h3 h4 where "h3 \<bottom> h4" "h2 = h3++h4" 
    "(s,h3)\<Turnstile>Spat(\<acute>y`\<longmapsto>yv)" by auto
  then obtain v' where "\<lbrakk>\<acute>y`\<rbrakk>s = Val v'" "dom h3 = {v'}" by auto
  with \<open>\<lbrakk>\<acute>x`\<rbrakk>s = Val v\<close> \<open>\<lbrakk>\<acute>x`\<rbrakk>s = \<lbrakk>\<acute>y`\<rbrakk>s\<close> have "v = v'" by simp
  with \<open>dom h3 = {v'}\<close> \<open>dom h1 = {v}\<close> have "\<not> h3 \<bottom> h1" by simp
  hence "\<not> (h3++h4) \<bottom> h1" using ortho_distr by auto
  with \<open>h2 = h3++h4\<close> have "\<not> h1 \<bottom> h2" using ortho_commut by metis
  with \<open>h1 \<bottom> h2\<close> show False by simp
qed

text \<open>Order in pure formulae does not matter\<close>
lemma pure_commut: "(s,h)\<Turnstile>PureF(p1\<and>\<^sub>pp2\<and>\<^sub>p\<Pi>) \<longleftrightarrow> (s,h)\<Turnstile>PureF(p2\<and>\<^sub>pp1\<and>\<^sub>p\<Pi>)" by auto

text \<open>Singular spatial formulae are only satisfied by singular heaps\<close>
corollary sing_heap: "(s,h)\<Turnstile>SpatF[x\<longmapsto>y] \<longleftrightarrow> (s,h)\<Turnstile>Spat(x\<longmapsto>y) \<and> (\<exists> v v'. \<lbrakk>x\<rbrakk>s = Val v \<and>
   \<lbrakk>y\<rbrakk>s = v' \<and> h = [v\<mapsto>v'])" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  hence spat: "(s, h) \<Turnstile> Spat (x \<longmapsto> y)" by fastforce
  moreover then obtain v v' where "\<lbrakk>x\<rbrakk>s = Val v" "\<lbrakk>y\<rbrakk>s= v'" by blast
  moreover with spat have "h = [v\<mapsto>v']" by fastforce
  ultimately show "?rhs" by simp
next
  assume "?rhs"
  moreover have "h \<bottom> Map.empty" by simp
  ultimately have "(s,h++Map.empty)\<Turnstile>SpatF[x\<longmapsto>y]" by blast
  thus "?lhs" by simp
qed

text \<open>Order in spatial formulae does not matter\<close>
corollary spatial_commut: "(s,h)\<Turnstile>SpatF(s1*s2*\<Sigma>) \<longleftrightarrow> (s,h)\<Turnstile>SpatF(s2*s1*\<Sigma>)" (is "?P s1 s2 \<longleftrightarrow> ?p s2 s1")
proof
  assume "?P s1 s2"
  then obtain h1 h2 where h:"h1 \<bottom> h2 \<and> h = h1++h2" and s1:"(s,h1)\<Turnstile>Spat s1" and "(s,h2)\<Turnstile>SpatF (s2*\<Sigma>)" 
    by auto
  then obtain h3 h4 where h2:"h3 \<bottom> h4 \<and> h2 = h3++h4" and s2: "(s,h3)\<Turnstile>Spat s2" and \<sigma>: "(s,h4)\<Turnstile>SpatF \<Sigma>"
    by auto
  from h h2 have "h4 \<bottom> h1" by auto
  moreover then obtain h2' where h2': "h2' = h1++h4" by simp  
  ultimately have "(s,h2')\<Turnstile>SpatF(s1*\<Sigma>)" using s1 \<sigma> by auto
  moreover from h h2 h2' have "h3 \<bottom> h2'" by auto
  moreover with h h2 h2' have "h=h3++h2'" by (metis map_add_assoc map_add_comm)
  ultimately show "?P s2 s1" using s2 by auto
next
  assume "?P s2 s1"
  then obtain h1 h2 where h:"h1 \<bottom> h2 \<and> h = h1++h2" and s2:"(s,h1)\<Turnstile>Spat s2" and "(s,h2)\<Turnstile>SpatF (s1*\<Sigma>)" 
    by auto
  then obtain h3 h4 where h2:"h3 \<bottom> h4 \<and> h2 = h3++h4" and s1:"(s,h3)\<Turnstile>Spat s1" and \<sigma>: "(s,h4)\<Turnstile>SpatF \<Sigma>"
    by auto
  from h h2 have "h4 \<bottom> h1" by auto
  moreover then obtain h2' where h2': "h2' = h1++h4" by simp  
  ultimately have "(s,h2')\<Turnstile>SpatF(s2*\<Sigma>)" using s2 \<sigma> by auto
  moreover from h h2 h2' have "h3 \<bottom> h2'" by auto
  moreover with h h2 h2' have "h=h3++h2'" by (metis map_add_assoc map_add_comm)
  ultimately show "?P s1 s2" using s1 by auto
qed

text \<open>An empty list is equivalent to an empty heap\<close>
corollary empty_ls: "(s,h)\<Turnstile>SpatF emp \<longleftrightarrow> (s,h)\<Turnstile>Spat(ls(x,x))"
proof
  assume "(s, h) \<Turnstile> SpatF emp"
  hence "dom h = {}" by blast
  hence "(s,h)\<Turnstile>ls\<^sup>0(x,x)" by blast
  thus "(s, h) \<Turnstile> Spat (ls(x, x))" by blast
next
  assume "(s, h) \<Turnstile> Spat (ls(x, x))"
  then obtain n where "(s,h)\<Turnstile>ls\<^sup>n(x,x)" by auto
  hence "n=0" "dom h = {}" by auto
  thus "(s, h) \<Turnstile> SpatF emp" by auto
  qed
text \<open>Due to this theorem circular list segements can only be formulated as follows:\<close>
term "\<acute>x`\<longmapsto>\<acute>y` * ls(\<acute>y`,\<acute>y`) * emp"


lemma subst_sat:"\<lbrakk>(s,h)\<Turnstile>F'; F'=subst x E F; \<lbrakk>\<acute>x`\<rbrakk>s=\<lbrakk>E\<rbrakk>s\<rbrakk> \<Longrightarrow> (s,h)\<Turnstile>F"
proof (induction arbitrary: F rule: sat_induct)
  case (EqSat e1 s e2 h)
  from EqSat.prems(1) obtain e3 e4 where F: "F = Pure (e3=\<^sub>pe4)" 
    using subst_distinct_pure1 subst_distinct_formula2
    by (metis formula.inject(1) subst_formula.simps(1))
  with EqSat.prems(1) have e1: "e1 = subst x E e3" and e2: "e2 = subst x E e4" by simp_all
  then show ?case proof (cases "\<acute>x`=e3")
    case True
    with e1 have "e1 = E" by auto
    then show ?thesis using EqSat by (metis F True e2 satisfaction.EqSat subst_not_eq_expr)
  next
    case False
    then show ?thesis proof (cases "\<acute>x`=e4")
      case True
      with e2 have "e2 = E" by auto    
      then show ?thesis using EqSat F False True by auto
    next
      case False
      with \<open>\<acute>x`\<noteq>e3\<close> F have "x \<notin> fv F" by (metis Un_iff empty_iff fv_expr.simps(1) fv_expr.simps(2) 
        fv_formula.simps(1) fv_pure.simps(1) insert_iff subst_expr.elims)
      then show ?thesis using subst_not_free_formula EqSat.hyps F e1 e2 by auto
    qed
  qed
next
  case (NeqSat e1 s e2 h)
  from NeqSat.prems(1) obtain e3 e4 where F: "F = Pure (e3\<noteq>\<^sub>pe4)" 
    using subst_distinct_pure2 subst_distinct_formula2
    by (metis formula.inject(1) subst_formula.simps(1))
  with NeqSat.prems(1) have e1: "e1 = subst x E e3" and e2: "e2 = subst x E e4" by simp_all
  then show ?case proof (cases "\<acute>x`=e3")
    case True
    with e1 have "e1 = E" by auto
    then show ?thesis using NeqSat by (metis F True e1 e2 satisfaction.NeqSat subst_not_eq_expr)
  next
    case False
    then show ?thesis proof (cases "\<acute>x`=e4")
      case True
      with e2 have "e2 = E" by auto    
      then show ?thesis using NeqSat F False True by auto
    next
      case False
      with \<open>\<acute>x`\<noteq>e3\<close> F have "x \<notin> fv F" by (smt Un_iff fv_expr.simps(1) fv_expr.simps(2)
        fv_formula.simps(1) fv_pure.simps(2) insert_absorb insert_iff insert_not_empty
        subst_expr.elims)
      then show ?thesis using subst_not_free_formula NeqSat.hyps F e1 e2 by auto
    qed
  qed
next
  case (TrueSat s h)
  then show ?case using subst_preserve_True satisfaction.TrueSat by metis
next
  case (ConjSat s h P \<Pi>)
  from ConjSat.prems(1) obtain P' \<Pi>' where F: "F = PureF (P'\<and>\<^sub>p\<Pi>')" 
    using subst_distinct_formula1 subst_distinct_puref
    by (metis formula.inject(2) subst_formula.simps(2))
  with ConjSat.prems(1) have "Pure P = subst x E (Pure P')" "PureF \<Pi> = subst x E (PureF \<Pi>')"
    by simp_all
  from ConjSat.IH(1)[OF this(1) ConjSat.prems(2)] ConjSat.IH(2)[OF this(2) ConjSat.prems(2)] F
  show ?case by auto
next
  case (PointsToSat e1 s v h e2)
  then show ?case proof (cases "x \<in> fv F")
    case True
    then show ?thesis using PointsToSat
    by (smt formula.inject(3) satisfaction.PointsToSat spatial.inject(1) subst_distinct_formula4 
      subst_distinct_spat1 subst_expr.simps(2) subst_formula.simps(3) subst_not_eq_expr 
      subst_spatial.simps(1))
  next
    case False
    show ?thesis using subst_not_free_formula[OF False] PointsToSat by fastforce
  qed
next
  case (EmpSat h s)
  then show ?case using satisfaction.EmpSat subst_preserve_emp by metis
next
  case (SepConjSat h1 h2 h s S \<Sigma>)
  from SepConjSat.prems(1) obtain S' \<Sigma>' where F: "F = SpatF (S'*\<Sigma>')" 
    using subst_distinct_spatf subst_distinct_formula3
    by (metis formula.inject(4) subst_formula.simps(4))
  with SepConjSat.prems(1) have "Spat S = subst x E (Spat S')" "SpatF \<Sigma> = subst x E (SpatF \<Sigma>')" 
    by simp_all
  with SepConjSat.IH SepConjSat.prems(2) have "(s,h1)\<Turnstile>Spat S'" "(s,h2)\<Turnstile>SpatF \<Sigma>'" by simp_all
  then show ?case using F SepConjSat.hyps by blast
next
  case (FormSat s h \<Pi> \<Sigma>)
  from FormSat.prems(1) obtain \<Pi>' \<Sigma>' where F:"F = \<Pi>'\<bar>\<Sigma>'" using subst_distinct_formula5 by metis
  with FormSat.prems(1) have "substl x E \<Pi>' = \<Pi>" and "substl x E \<Sigma>' = \<Sigma>" by simp_all
  with FormSat.IH FormSat.prems(2) have "(s,h)\<Turnstile>PureF \<Pi>'" and "(s,h)\<Turnstile>SpatF \<Sigma>'" by simp_all
  with F show ?case by auto
next
  case (LsSat s h n e1 e2)
  then show ?case sorry
qed

lemma subst_sat_rev:"\<lbrakk>(s,h)\<Turnstile>F; \<lbrakk>\<acute>x`\<rbrakk>s=\<lbrakk>E\<rbrakk>s\<rbrakk> \<Longrightarrow> (s,h)\<Turnstile>subst x E F"
proof (induction rule: sat_induct)
  case (EqSat e1 s e2 h)
  then show ?case by (metis satisfaction.EqSat subst_expr.simps(2) subst_formula.simps(1)
    subst_not_eq_expr subst_pure.simps(1))
next
  case (NeqSat e1 s e2 h)
  then show ?case by (metis satisfaction.NeqSat subst_expr.simps(2) subst_formula.simps(1)
    subst_not_eq_expr subst_pure.simps(2))
next
  case (PointsToSat e1 s v h e2)
  then show ?case by (smt satisfaction.PointsToSat subst_expr.simps(2) subst_formula.simps(3)
    subst_not_eq_expr subst_spatial.simps(1))
next
  case (LsSat s h n e1 e2)
  then show ?case sorry
qed auto

lemma subst_sat_eq: "\<lbrakk>F'=subst x E F; \<lbrakk>\<acute>x`\<rbrakk>s=\<lbrakk>E\<rbrakk>s\<rbrakk> \<Longrightarrow> ((s,h)\<Turnstile>F') = ((s,h)\<Turnstile>F)"
using subst_sat subst_sat_rev by fast

end