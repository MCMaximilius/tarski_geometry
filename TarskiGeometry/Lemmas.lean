import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Real.Basic

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
theorem cons_elim0 (x : α) : Fin.cons x Fin.elim0 = ![x] := by
  funext y
  match y with
  | 0 => rfl

-- @[simp]
-- theorem cons_elim0' (x : α) : Fin.cons x Fin.elim0' = ![x] := by
--   funext y
--   match y with
--   | 0 => rfl

-- theorem nonzero_eq_succ (n : ℕ) (m : Fin (Nat.iterate Nat.succ (m + 1) n)) : Nat.succ m = Fin.succ m := by
--   simp only [Function.iterate_succ, Function.comp_apply, val_succ]

-- lemma nat_succ_pos (m n : ℕ) : (Nat.iterate Nat.succ (1 + m) n) > 0 := by
--   simp only [Function.iterate_add, Function.iterate_one, Function.comp_apply, Nat.succ_pos]

-- theorem nonzero_eq_succ (m n : ℕ) : Fin.ofNat' m (nat_succ_pos m n) = Fin.succ m:= by
--   sorry

theorem one (n : ℕ) : (1 : Fin (Nat.succ (Nat.succ n))) = Fin.succ 0 := rfl

theorem two (n : ℕ) : (2 : Fin (Nat.succ (Nat.succ (Nat.succ n)))) = Fin.succ 1 := rfl

theorem three (n : ℕ) : (3 : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))) = Fin.succ 2 := rfl

theorem four (n : ℕ) : (4 : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))))) = Fin.succ 3 := rfl

theorem five (n : ℕ) : (5 : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))))) = Fin.succ 4 := rfl

theorem six (n : ℕ) : (6 : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))))))) = Fin.succ 5 := rfl

theorem seven (n : ℕ) : (7 : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))))))) = Fin.succ 6 := rfl

theorem eight (n : ℕ) : (8 : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))))))))) = Fin.succ 7 := rfl

end Fin

--------------------------------------------------------------------------

namespace Matrix

universe u

variable {α : Type u}

variable {m n : ℕ}

@[simp]
lemma vecCons_head (x : α) : ![x] 0 = x := rfl

end Matrix
