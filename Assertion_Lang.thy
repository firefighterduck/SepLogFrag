theory Assertion_Lang
imports Main
begin

section \<open>Syntax and Datatytpes\<close>
text \<open>Defines the language of formulae\<close>

type_synonym var = string
type_synonym lval = nat
datatype val = Nilval | Val lval
type_synonym stack = "var \<Rightarrow> val"
type_synonym heap = "lval \<rightharpoonup> val"
type_synonym state = "stack \<times> heap"

datatype expr = 
  Nil                             ("nil" 61)
  | Var var                       ("\<acute>_`" [0] 61)
datatype pure = 
  Eq expr expr                    ("_ =\<^sub>p _" [60, 61] 62)
  | Neq expr expr                 ("_ \<noteq>\<^sub>p _" [60, 61] 62)
type_synonym pure_form = "pure list"
datatype spatial =
  PointsTo expr expr              ("_ \<longmapsto> _" [60, 61] 60)
  | Ls "expr \<times> expr"              ("ls_" [61] 60)
type_synonym spatial_form = "spatial list"
datatype formula =
  Pure pure
  | PureF pure_form
  | Spat spatial
  | SpatF spatial_form
  | Form pure_form spatial_form   ("_ \<bar> _" [60, 61] 59)

abbreviation "PureTrue \<equiv> ([] :: pure_form)"
notation PureTrue ("\<top>" 61)
abbreviation "pure_conj \<equiv> (Cons :: pure \<Rightarrow> pure_form \<Rightarrow> pure_form)"
notation pure_conj ("_ \<and>\<^sub>p _" [62, 61] 63)
abbreviation "emp \<equiv> ([] :: spatial_form)"
abbreviation "sep_conj \<equiv> (Cons :: spatial \<Rightarrow> spatial_form \<Rightarrow> spatial_form)"
notation sep_conj ("_ * _" [60, 61] 61)

(* Example formula *)
term "\<acute>x`\<noteq>\<^sub>p\<acute>y` \<and>\<^sub>p \<acute>y`\<noteq>\<^sub>pnil \<and>\<^sub>p \<acute>z`=\<^sub>p\<acute>x` \<and>\<^sub>p \<top> \<bar> \<acute>x` \<longmapsto> \<acute>y` * ls(\<acute>y`,nil) * emp"
(* The same formula but with list notation (less ambiguously parsed) *)
term "[\<acute>x`\<noteq>\<^sub>p\<acute>y`, \<acute>y`\<noteq>\<^sub>pnil, \<acute>z`=\<^sub>p\<acute>x`] \<bar> [\<acute>x` \<longmapsto> \<acute>y`, ls(\<acute>y`,nil)]"
end