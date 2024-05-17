import TarskiGeometry.Axioms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Interval.Set.UnorderedInterval

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

lemma eucildeanPlane.reflexivity_of_congruence : eucildeanPlane ⊨ reflexivityOfCongruence := by
  intro x y
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons, cons_elim0, cons_zero, cons_succ, nonzero_numeral_eq_succ]
  apply dist_comm

lemma eucildeanPlane.identity_of_congruence : eucildeanPlane ⊨ identityOfCongruence := by
  intro x y z
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  simp only [dist_self, dist_eq_zero, imp_self]

lemma eucildeanPlane.transitivity_of_congruence : eucildeanPlane ⊨ transitivityOfCongruence := by
  intro x y z u v w
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  exact Eq.trans

lemma eucildeanPlane.identity_of_betweenness : eucildeanPlane ⊨ identityOfBetweenness := by
  intro x y
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  simp only [ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc, smul_add_one_sub_smul, exists_and_right, and_imp, imp_self, implies_true]

lemma eucildeanPlane.axiom_of_pasch : eucildeanPlane ⊨ axiomOfPasch := by
  intro x y z u v
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  intro h
  sorry

-- example {n} {φ ψ : BoundedFormula tarski Empty (n + 2)} : (ℝ × ℝ) ⊨ axiomOfContinuity φ ψ := by
--   unfold axiomOfContinuity
--   unfold Sentence.Realize
--   rw [realize_alls]
--   intro xs
--   simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
--   intro h
--   sorry

lemma eucildeanPlane.lower_dimension : eucildeanPlane ⊨ lowerDimension := by
  simp only [lowerDimension, Sentence.Realize, Formula.Realize]
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  use ![0, 0]; use ![0, 1]; use ![1, 0]
  constructor <;> (try constructor) <;> intro h <;> rcases h with ⟨t, ht⟩
  <;> have := congrFun ht.2 0 <;> have := congrFun ht.2 1 <;> simp_all

lemma eucildeanPlane.upper_dimension : eucildeanPlane ⊨ upperDimension := by
  intro x y z u v
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  sorry

lemma eucildeanPlane.axiom_of_euclid : eucildeanPlane ⊨ axiomOfEuclid := by
  intro x y z u v
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  sorry

lemma eucildeanPlane.five_segment : eucildeanPlane ⊨ fiveSegment := by
  intro x y z u v w a b
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  sorry

lemma eucildeanPlane.segment_construction : eucildeanPlane ⊨ segmentConstruction := by
  intro x y a b
  simp only [realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Function.comp_apply, Sum.elim_inr, RelMap, euclidean_relations]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons, Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, nonzero_numeral_eq_succ]
  by_cases h : y = x
  . simp_all [h]
    use (b - a + x)
    constructor
    . use 1
      simp only [zero_le_one, le_refl, and_self, one_smul, sub_self, smul_add, zero_smul, add_zero]
    . simp only [SeminormedAddCommGroup.dist_eq, sub_add_cancel_right, neg_sub]
  . use (dist b a / dist y x) • (y - x) + y
    constructor
    . use dist y x / (dist y x + dist b a)
      constructor
      . simp only [ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc]
        constructor
        . simp only [div_nonneg, add_nonneg, dist_nonneg]
        . rw [div_le_one]
          simp only [le_add_iff_nonneg_right, dist_nonneg]
          rw [add_comm]
          apply add_pos_of_nonneg_of_pos
          . apply dist_nonneg
          . apply dist_pos.2 h
      . simp only [smul_add]
        sorry
    . sorry
