import TarskiGeometry.lemmas

namespace Tarski

open FirstOrder Language Structure Term BoundedFormula

inductive TarskiRel : ℕ → Type
  | between : TarskiRel 3
  | congr : TarskiRel 4

def tarski : Language := ⟨fun _ => Empty, TarskiRel⟩

abbrev PB {n} {α} (t₁ t₂ t₃: tarski.Term (Sum α (Fin n))) : tarski.BoundedFormula α n := Relations.boundedFormula₃ TarskiRel.between t₁ t₂ t₃

abbrev LC {n} {α} (t₁ t₂ t₃ t₄ : tarski.Term (Sum α (Fin n))) : tarski.BoundedFormula α n := Relations.boundedFormula₄ TarskiRel.congr t₁ t₂ t₃ t₄

def reflexivityOfCongruence : tarski.Sentence := ∀' ∀'(LC &0 &1 &1 &0)

def identityOfCongruence : tarski.Sentence := ∀' ∀' ∀'(LC &0 &1 &2 &2 ⟹ &0 =' &1)

def transitivityOfCongruence : tarski.Sentence := ∀' ∀' ∀' ∀' ∀' ∀'(LC &0 &1 &2 &3 ⟹ LC &2 &3 &4 &5 ⟹ LC &0 &1 &4 &5)

def identityOfBetweenness : tarski.Sentence := ∀' ∀' (PB &0 &1 &0 ⟹ &0 =' &1)

def axiomOfPasch : tarski.Sentence := ∀' ∀' ∀' ∀' ∀' ∃' (PB &0 &3 &2 ⊓ PB &1 &4 &2 ⟹ PB &3 &5 &1 ⊓ PB &4 &5 &0)

def axiomOfContinuity {n : ℕ} (φ ψ: BoundedFormula tarski Empty (n + 2)) : tarski.Sentence :=
alls (∃' ∀' ∀' ((liftAt 1 2 φ) ⊓ (liftAt 1 2 ψ) ⟹ PB &2 &0 &1)
⟹ ∃' ∀' ∀'((liftAt 1 2 φ) ⊓ (liftAt 1 2 ψ) ⟹ PB &0 &2 &1) )

def lowerDimension : tarski.Sentence := ∃' ∃' ∃'(∼(PB &0 &1 &2) ⊓ ∼(PB &1 &2 &0) ⊓ ∼(PB &2 &0 &1))

def upperDimension : tarski.Sentence := ∀' ∀' ∀' ∀' ∀'(LC &0 &3 &0 &4 ⊓ LC &1 &3 &1 &4 ⊓ LC &2 &3 &2 &4 ⊓ ∼(&3 =' &4) ⟹ PB &0 &1 &2 ⊔ PB &1 &2 &0 ⊔ PB &2 &0 &1)

def axiomOfEuclid : tarski.Sentence := ∀' ∀' ∀' ∀' ∀' ∃' ∃' (PB &0 &3 &4 ⊓ PB &1 &3 &2 ⊓ ∼(&0 =' &3) ⟹ PB &0 &1 &5 ⊓ PB &0 &2 &6 ⊓ PB &5 &4 &6)

def fiveSegment : tarski.Sentence := ∀' ∀' ∀' ∀' ∀' ∀' ∀' ∀'(∼(&0 =' &1) ⊓ PB &0 &1 &2 ⊓ PB &3 &4 &5 ⊓ LC &0 &1 &3 &4 ⊓ LC &1 &2 &4 &5 ⊓ LC &0 &6 &3 &7 ⊓ LC &1 &6 &4 &7 ⟹ LC &2 &6 &5 &7)

def segmentConstruction : tarski.Sentence := ∀' ∀' ∀' ∀' ∃'(PB &0 &1 &4 ⊓ LC &1 &4 &2 &3)

def euclideanAxioms : Theory tarski := {reflexivityOfCongruence, identityOfCongruence, transitivityOfCongruence, identityOfBetweenness, axiomOfPasch, lowerDimension, upperDimension, axiomOfEuclid, fiveSegment, segmentConstruction} ∪ ⋃ (n : ℕ), {axiomOfContinuity φ.1 φ.2 | φ : (BoundedFormula tarski Empty (n + 2) × BoundedFormula tarski Empty (n + 2))}
