theory Assertion_Misc
imports Assertion_Lang
begin

section \<open>Miscellaneous definitions used with the assertion language\<close>

text \<open>A type class of functions that extract used variables (similarly to vars).\<close>
class fv =
fixes fv :: "'a \<Rightarrow> var set"

text \<open>A type class of functions that extract used variables from lists.\<close>
class fvl = fv +
fixes fvl :: "'a list \<Rightarrow> var set"

instantiation expr :: fv
begin
fun fv_expr :: "expr \<Rightarrow> var set" where
"fv_expr (nil) = {}" |
"fv_expr (\<acute>v`) = {v}"
instance ..
end

instantiation pure :: fv
begin
fun fv_pure :: "pure \<Rightarrow> var set" where
"fv_pure (e1 =\<^sub>p e2) = fv e1 \<union> fv e2" |
"fv_pure (e1 \<noteq>\<^sub>p e2) =  fv e1 \<union> fv e2"
instance ..
end

instantiation pure :: fvl
begin
fun fvl_pure :: "pure_form \<Rightarrow> var set" where
  "fvl_pure pf = \<Union> (fv`(set pf))"
instance ..
end

instantiation spatial :: fv
begin
fun fv_spatial :: "spatial \<Rightarrow> var set" where
"fv_spatial (e1 \<longmapsto> e2) = fv e1 \<union> fv e2" |
"fv_spatial (ls(e1,e2)) = fv e1 \<union> fv e2"
instance ..
end

instantiation spatial :: fvl
begin
fun fvl_spatial :: "spatial_form \<Rightarrow> var set" where
  "fvl_spatial sf = \<Union> (fv`(set sf))"
instance ..
end

instantiation formula :: fv
begin
fun fv_formula :: "formula \<Rightarrow> var set" where
"fv_formula (Pure p) = fv p" |
"fv_formula (PureF pf) = fvl pf" |
"fv_formula (Spat s) = fv s" |
"fv_formula (SpatF sf) = fvl sf" |
"fv_formula (pf \<bar> sf) = fvl pf \<union> fvl sf"
instance ..
end

lemma fv_finite_expr: "finite (fv (x::expr))"
by (metis finite.simps fv_expr.elims)

lemma fv_finite_un: "\<exists>v. v \<notin> fv (x::expr) \<union> fv (y::expr)"
using fv_finite_expr Finite_Set.finite_Un Finite_Set.ex_new_if_finite infinite_UNIV_listI by metis

lemma fv_other_x: "\<And>x. \<exists>x'. x' \<notin> fv (e::expr) \<and> x' \<noteq> x"
  using fv_finite_expr fv_finite_un by (metis Un_iff fv_expr.simps(2) insertI1)

lemma fv_other_x_un: "x \<notin> fv (e1::expr) \<union> fv (e2::expr) \<Longrightarrow> \<exists>x'. x' \<notin> fv (e1::expr) \<union> fv (e2::expr) \<and> x' \<noteq> x"
proof -
assume assm: "x \<notin> fv (e1::expr) \<union> fv (e2::expr)"
have "finite (fv e1 \<union> fv e2)" using fv_finite_expr by simp
hence "\<not>finite(-(fv e1 \<union> fv e2))" by (meson finite_compl infinite_UNIV_listI)
moreover have "\<not>finite (S::string set) \<Longrightarrow> \<forall>y \<in> S. \<exists>y' \<in> S. y\<noteq>y'" for S
by (metis (no_types, hide_lams) finite.simps insertCI insert_absorb insert_is_Un subsetI subset_antisym sup_ge1)
ultimately obtain y where "y \<in> -(fv e1 \<union> fv e2)" "y\<noteq>x" using assm by auto
thus ?thesis by auto
qed

text \<open>Orthogonality property of heaps.\<close>
abbreviation "orthogonal h1 h2 \<equiv> dom h1 \<inter> dom h2 = {}"
notation orthogonal ("_ \<bottom> _" [60, 61] 61)

theorem ortho_commut: "h1 \<bottom> h2 \<longleftrightarrow> h2 \<bottom> h1" by auto
theorem ortho_distr: "h1 \<bottom> (h2++h3) \<longleftrightarrow> (h1 \<bottom> h2 \<and> h1 \<bottom> h3)" by auto

text \<open>A type class that functions that substitute a variable for another expression.\<close>
class subst =
fixes subst :: "var \<Rightarrow> expr \<Rightarrow> 'a \<Rightarrow> 'a"

text \<open>A type class that functions that substitute a variable for another expression in a list.\<close>
class substl = subst +
fixes substl :: "var \<Rightarrow> expr \<Rightarrow> 'a list \<Rightarrow> 'a list"

instantiation expr :: subst
begin
fun subst_expr :: "var \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
"subst_expr v _ Nil = Nil" |
"subst_expr v e (\<acute>x`) = (if v=x then e else \<acute>x`)"
instance ..
end

instantiation pure :: subst
begin
fun subst_pure :: "var \<Rightarrow> expr \<Rightarrow> pure \<Rightarrow> pure" where
"subst_pure v e (e1 =\<^sub>p e2) = (subst v e e1) =\<^sub>p (subst v e e2)" |
"subst_pure v e (e1 \<noteq>\<^sub>p e2) = (subst v e e1) \<noteq>\<^sub>p (subst v e e2)"
instance ..
end

instantiation pure :: substl
begin
fun substl_pure :: "var \<Rightarrow> expr \<Rightarrow> pure_form \<Rightarrow> pure_form" where
"substl_pure v e = map (subst v e)"
instance ..
end

instantiation spatial :: subst
begin
fun subst_spatial :: "var \<Rightarrow> expr \<Rightarrow> spatial \<Rightarrow> spatial" where
"subst_spatial v e (e1 \<longmapsto> e2) = (subst v e e1) \<longmapsto> (subst v e e2)" |
"subst_spatial v e (ls(e1, e2)) = ls((subst v e e1), (subst v e e2))"
instance ..
end 

instantiation spatial :: substl
begin
fun substl_spatial :: "var \<Rightarrow> expr \<Rightarrow> spatial_form \<Rightarrow> spatial_form" where
"substl_spatial v e = map (subst v e)"
instance ..
end

instantiation formula :: subst
begin
fun subst_formula :: "var \<Rightarrow> expr \<Rightarrow> formula \<Rightarrow> formula" where
"subst_formula v e (Pure p) = Pure (subst v e p)" |
"subst_formula v e (PureF pf) = PureF (substl v e pf)" |
"subst_formula v e (Spat s) = Spat (subst v e s)" |
"subst_formula v e (SpatF sf) = SpatF (substl v e sf)" |
"subst_formula v e (pf \<bar> sf) = (substl v e pf) \<bar> (substl v e sf)"
instance ..
end

lemma subst_not_free_expr[simp]: "v \<notin> fv (e::expr) \<Longrightarrow> subst v E e = e"
by (induction e) auto

lemma subst_not_eq_expr[simp]: "e\<noteq>\<acute>v` \<Longrightarrow> subst v E e = e"
by (induction e) auto

lemma subst_not_free_pure[simp]: "v \<notin> fv (p::pure) \<Longrightarrow> subst v E p = p"
by (induction p) auto

lemma subst_not_free_spatial[simp]: "v \<notin> fv (s::spatial) \<Longrightarrow> subst v E s = s"
by (induction s) auto

lemma subst_not_free_puref[simp]: "v \<notin> fvl (pf::pure_form) \<Longrightarrow> substl v E pf = pf"
by (auto simp: map_idI)

lemma subst_not_free_spatialf[simp]: "v \<notin> fvl (sf::spatial_form) \<Longrightarrow> substl v E sf = sf"
by (auto simp: map_idI)

lemma subst_not_free_formula[simp]: "x \<notin> fv (F::formula) \<Longrightarrow> subst x E F = F"
proof (induction F)
  case (PureF x)
  then show ?case using subst_not_free_puref by auto
next
  case (SpatF x)
  then show ?case using subst_not_free_spatialf by auto
next
  case (Form x1a x2a)
  then show ?case using subst_not_free_puref subst_not_free_spatialf by auto
qed simp_all

lemma subst_distinct_pure1: "subst x E P = e1=\<^sub>pe2 \<Longrightarrow> \<exists>e3 e4. P = e3=\<^sub>pe4"
using subst_pure.elims by blast

lemma subst_distinct_pure2: "subst x E P = e1\<noteq>\<^sub>pe2 \<Longrightarrow> \<exists>e3 e4. P = e3\<noteq>\<^sub>pe4"
using subst_pure.elims by blast

lemma subst_distinct_puref: "substl x E Pf = P\<and>\<^sub>p\<Pi> \<Longrightarrow> \<exists>P' \<Pi>'. Pf = P'\<and>\<^sub>p\<Pi>'"
  by auto

lemmas subst_distinct_pure = subst_distinct_pure1 subst_distinct_pure2 subst_distinct_puref

lemma subst_distinct_spat1: "subst x E S = e1\<longmapsto>e2 \<Longrightarrow> \<exists>e3 e4. S = e3\<longmapsto>e4"
using subst_spatial.elims by blast

lemma subst_distinct_spat2: "subst x E S = ls(e1,e2) \<Longrightarrow> \<exists>e3 e4. S = ls(e3,e4)"
using subst_spatial.elims by blast

lemma subst_distinct_spatf: "substl x E Sf = S*\<Sigma> \<Longrightarrow> \<exists>S' \<Sigma>'. Sf = S'*\<Sigma>'"
  by auto

lemmas subst_distinct_spat = subst_distinct_spat1 subst_distinct_spat2 subst_distinct_spatf

lemma subst_distinct_formula1: "subst x E F = PureF P \<Longrightarrow> \<exists>P'. F = PureF P'"
using subst_formula.elims by blast

lemma subst_distinct_formula2: "subst x E F = Pure P \<Longrightarrow> \<exists>P'. F = Pure P'"
using subst_formula.elims by blast

lemma subst_distinct_formula3: "subst x E F = SpatF S \<Longrightarrow> \<exists>S'. F = SpatF S'"
using subst_formula.elims by blast

lemma subst_distinct_formula4: "subst x E F = Spat S \<Longrightarrow> \<exists>S'. F = Spat S'"
using subst_formula.elims by blast

lemma subst_distinct_formula5: "subst x E F = \<Pi>\<bar>\<Sigma> \<Longrightarrow> \<exists>\<Pi>' \<Sigma>'. F = \<Pi>'\<bar>\<Sigma>'"
using subst_formula.elims by blast

lemma subst_preserve_True[simp]: "subst x E F = PureF [] \<Longrightarrow> F = PureF []"
using subst_distinct_formula1 by fastforce

lemma subst_preserve_emp[simp]: "subst x E F = SpatF [] \<Longrightarrow> F = SpatF []"
using subst_distinct_formula3 by fastforce

lemmas subst_distinct_formula = subst_distinct_formula1 subst_distinct_formula2
  subst_distinct_formula3 subst_distinct_formula4 subst_distinct_formula5
  subst_preserve_True subst_preserve_emp

lemma subst_reflexive: "\<acute>x`=E \<Longrightarrow> subst x E (e::expr) = e"
using subst_expr.elims by metis
  
lemma subst_fv_expr: "\<acute>x`\<noteq>E \<Longrightarrow> x \<notin> fv (subst x E (e::expr))"
  by (metis empty_iff expr.exhaust fv_expr.simps(1) fv_expr.simps(2) insert_iff
    subst_expr.simps(2) subst_not_eq_expr)

lemma subst_fv_expr_set: "\<acute>x`\<noteq>E \<Longrightarrow> fv (subst x E (e::expr)) \<supseteq> (fv e - {x})"
  using subst_fv_expr by (metis Diff_cancel Diff_subset fv_expr.simps(2) subst_not_eq_expr)

lemma subst_fv_expr_set_un: 
  "\<acute>x`\<noteq>E \<Longrightarrow> fv (subst x E (e1::expr)) \<union> fv (subst x E (e2::expr)) \<supseteq> (fv e1 \<union> fv e2) - {x}"
  using subst_fv_expr_set by auto
end