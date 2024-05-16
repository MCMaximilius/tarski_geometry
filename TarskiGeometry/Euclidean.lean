import TarskiGeometry.Axioms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.Linarith

namespace Tarski

open FirstOrder Language BoundedFormula Structure Term Interval Fin

abbrev eucildeanPlane := EuclideanSpace ℝ (Fin 2)

noncomputable instance eucildeanPlane.innerProductSpace : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin 2)
) := PiLp.innerProductSpace (fun _ : Fin 2 => ℝ)

abbrev euclidean_relations : ∀ {n}, tarski.Relations n → (Fin n → eucildeanPlane) → Prop
  | 3, TarskiRel.between, f => ∃ t : ℝ , t ∈ [[0, 1]] ∧ t • f 0 + (1 - t) • f 2 = f 1
  | 4, TarskiRel.congr, f => dist (f 0) (f 1) = dist (f 2) (f 3)

instance : Structure tarski eucildeanPlane where
  funMap := fun _ => default
  RelMap := euclidean_relations

noncomputable example : NormedField ℝ := inferInstance

lemma eucildeanPlane.reflexivityOfCongruence : eucildeanPlane ⊨ reflexivityOfCongruence := by
  intro x y
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  apply dist_comm

lemma eucildeanPlane.identityOfCongruence : eucildeanPlane ⊨ identityOfCongruence := by
  intro x y z
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  simp only [dist_self, dist_eq_zero, imp_self]

lemma eucildeanPlane.transitivityOfCongruence : eucildeanPlane ⊨ transitivityOfCongruence := by
  intro x y z u v w
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  exact Eq.trans

lemma eucildeanPlane.identityOfBetweenness : eucildeanPlane ⊨ identityOfBetweenness := by
  intro x y
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  simp only [ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc, smul_add_one_sub_smul, exists_and_right, and_imp, imp_self, implies_true]

lemma eucildeanPlane.axiomOfPasch : eucildeanPlane ⊨ axiomOfPasch := by
  intro x y z u v
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

-- example {n} {φ ψ : BoundedFormula tarski Empty (n + 2)} : (ℝ × ℝ) ⊨ axiomOfContinuity φ ψ := by
--   unfold axiomOfContinuity
--   unfold Sentence.Realize
--   rw [realize_alls]
--   intro xs
--   simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
--   intro h
--   sorry

lemma eucildeanPlane.lowerDimension : eucildeanPlane ⊨ lowerDimension := by
  unfold lowerDimension
  unfold Sentence.Realize
  unfold Formula.Realize
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  use ![0, 0]; use ![0, 1]; use ![1, 0]
  constructor <;> (try constructor) <;> intro h <;> rcases h with ⟨t, ht⟩
  <;> have := congrFun ht.2 0 <;> have := congrFun ht.2 1 <;> simp_all

lemma eucildeanPlane.upperDimension : eucildeanPlane ⊨ upperDimension := by
  intro x y z u v
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

lemma eucildeanPlane.axiomOfEuclid : eucildeanPlane ⊨ axiomOfEuclid := by
  intro x y z u v
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

lemma eucildeanPlane.fiveSegment : eucildeanPlane ⊨ fiveSegment := by
  intro x y z u v w a b
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

lemma eucildeanPlane.segmentConstruction : eucildeanPlane ⊨ segmentConstruction := by
  intro x y a b
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry
