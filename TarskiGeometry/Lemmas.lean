import Mathlib.ModelTheory.Semantics

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable {α : Type u'}

def Relations.boundedFormula₃ (r : L.Relations 3) (t₁ t₂ t₃ : L.Term (Sum α (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂, t₃]

def Relations.boundedFormula₄ (r : L.Relations 4) (t₁ t₂ t₃ t₄: L.Term (Sum α (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂, t₃, t₄]

def Relations.formula₃ (r : L.Relations 3) (t₁ t₂ t₃: L.Term α) : L.Formula α := r.formula ![t₁, t₂, t₃]

def Relations.formula₄ (r : L.Relations 4) (t₁ t₂ t₃ t₄: L.Term α) : L.Formula α := r.formula ![t₁, t₂, t₃, t₄]

namespace BoundedFormula

variable {M : Type w} [L.Structure M]

variable {v : α → M} {xs : Fin l → M}

open Structure

@[simp]
theorem realize_rel₃ {R : L.Relations 3} {t₁ t₂ t₃ : L.Term _} :
    (R.boundedFormula₃ t₁ t₂ t₃).Realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs), t₃.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₃, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Fin.cases _ _))
  · simp only [Matrix.cons_val_zero]
  . intro i
    match i with
    | 0 => simp only [Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.head_cons]
    | 1 => simp only [Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

@[simp]
theorem realize_rel₄ {R : L.Relations 4} {t₁ t₂ t₃ t₄: L.Term _} :
    (R.boundedFormula₄ t₁ t₂ t₃ t₄).Realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs), t₃.realize (Sum.elim v xs), t₄.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₄, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Fin.cases _ _))
  · simp only [Matrix.cons_val_zero]
  . intro i
    match i with
    | 0 => simp only [Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.head_cons]
    | 1 => simp only [Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    | 2 => simp only [Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

end BoundedFormula

namespace Formula

variable {M : Type w} [L.Structure M]

variable {v : α → M}

open Structure

@[simp]
theorem realize_rel₃ {R : L.Relations 3} {t₁ t₂ t₃ : L.Term _} :
    (R.formula₃ t₁ t₂ t₃).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v, t₃.realize v] := by
  rw [Relations.formula₃, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Fin.cases _ _))
  · simp only [Matrix.cons_val_zero]
  · intro i
    match i with
    | 0 => simp only [Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.head_cons]
    | 1 => simp only [Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

@[simp]
theorem realize_rel₄ {R : L.Relations 4} {t₁ t₂ t₃ t₄: L.Term _} :
    (R.formula₄ t₁ t₂ t₃ t₄).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v, t₃.realize v, t₄.realize v] := by
  rw [Relations.formula₄, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Fin.cases _ _))
  · simp only [Matrix.cons_val_zero]
  · intro i
    match i with
    | 0 => simp only [Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.head_cons]
    | 1 => simp only [Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    | 2 => simp only [Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

end Formula

end Language

end FirstOrder

--------------------------------------------------------------------------

namespace Fin

universe u

variable {α : Type u}

@[simp]
lemma cons_elim0 (x : α) : Fin.cons x Fin.elim0 = ![x] := by
  funext y
  match y with
  | 0 => rfl

lemma nonzero_numeral_eq_succ (n : ℕ) : (1 : Fin (n + 2)) = Fin.succ 0 ∧ (2 : Fin (n + 3)) = Fin.succ 1 ∧ (3 : Fin (n + 4)) = Fin.succ 2 ∧ (4 : Fin (n + 5)) = Fin.succ 3 ∧ (5 : Fin (n + 6)) = Fin.succ 4 ∧ (6 : Fin (n + 7)) = Fin.succ 5 ∧ (7 : Fin (n + 8)) = Fin.succ 6 ∧ (8 : Fin (n + 9)) = Fin.succ 7 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- theorem nonzero_eq_succ (m n : ℕ) : (Fin.ofNat (m + 1) : Fin (n + m + 1)) = Fin.succ (@Fin.ofNat (n + m) m) := by
--   simp only [Nat.succ_eq_add_one, val_succ, Nat.cast_add, cast_val_eq_self, Nat.cast_one]
--   sorry

end Fin

--------------------------------------------------------------------------

namespace Matrix

universe u

variable {α : Type u}

variable {m n : ℕ}

@[simp]
lemma vecCons_head (x : α) : ![x] 0 = x := rfl

end Matrix
