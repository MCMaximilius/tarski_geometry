import TarskiGeometry.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Tarski

open FirstOrder

open Language

open BoundedFormula

open Structure

open Term

def rel_in_reals : ∀ {n}, tarski.Relations n → (Fin n → ℝ × ℝ) → Prop
  | 3, TarskiRel.between, f => ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (t * (f 0).1 + (1 - t) * (f 2).1 = (f 1).1) ∧ (t * (f 0).2 + (1 - t) * (f 2).2 = (f 1).2)
  | 4, TarskiRel.congr, f => ((f 0).1 - (f 1).1)^2 + ((f 0).2 - (f 1).2)^2 = ((f 2).1 - (f 3).1)^2 + ((f 2).2 - (f 3).2)^2

instance : Structure tarski (ℝ × ℝ) where
  funMap := fun _ => default
  RelMap := rel_in_reals

open Fin

example : (ℝ × ℝ) ⊨ reflexivityOfCongruence := by
  intro x y
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  ring

example : (ℝ × ℝ) ⊨ identityOfCongruence := by
  intro x y z
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  intro h
  simp only [sq, mul_self_add_mul_self_eq_zero, sub_eq_zero] at h
  ext; exact h.1; exact h.2

example : (ℝ × ℝ) ⊨ transitivityOfCongruence := by
  intro x y z w u v
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  intro h
  rw [← h.1, h.2]

example : (ℝ × ℝ) ⊨ identityOfBetweenness := by
  intro x y
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  intro h; ext <;> rcases h <;> linarith

example : (ℝ × ℝ) ⊨ axiomOfPasch := by
  intro x y z u v
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

example : (ℝ × ℝ) ⊨ lowerDimension := by
  unfold lowerDimension
  unfold Sentence.Realize
  unfold Formula.Realize
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  use ⟨0, 0⟩; use ⟨0, 1⟩; use ⟨1, 0⟩
  simp only [mul_zero, mul_one, zero_add, add_zero, _root_.zero_ne_one, and_false, exists_const,
    not_false_eq_true, false_and, and_self, not_exists, not_and, true_and]
  intro x _ _ h₃
  simp only [h₃, sub_zero, one_ne_zero, not_false_eq_true]

example : (ℝ × ℝ) ⊨ upperDimension := by
  intro x y z u v
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  intro h
  sorry

example : (ℝ × ℝ) ⊨ axiomOfEuclid := by
  intro x y z u v
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

example : (ℝ × ℝ) ⊨ fiveSegment := by
  intro x y z u v w r s
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

example : (ℝ × ℝ) ⊨ segmentConstruction := by
  intro x y z u
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  simp only [snoc_eq_append, cons_elim0, append_left_nil, cast_refl, Function.comp_id, append_left_eq_cons, append_cons]
  simp only [Matrix.vecCons_head, cons_zero, cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one, two, three, four, five, six, seven, eight]
  sorry

example {n} {φ ψ : BoundedFormula tarski Empty (n + 2)} : (ℝ × ℝ) ⊨ axiomOfContinuity φ ψ := by
  unfold axiomOfContinuity
  unfold Sentence.Realize
  rw [realize_alls]
  intro xs
  simp only [LC, PB, Function.comp_apply, realize_rel₃, realize_rel₄, realize_var, realize_imp, realize_inf, realize_ex, realize_not, realize_bdEqual, realize_sup, Sum.elim_inr, RelMap, rel_in_reals]
  intro h
  sorry
