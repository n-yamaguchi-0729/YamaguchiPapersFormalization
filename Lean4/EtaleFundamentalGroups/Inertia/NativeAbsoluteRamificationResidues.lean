/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeSeparableRoots
import EtaleFundamentalGroups.Inertia.NativeSeparableResidueGroup
import EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Mathlib.Algebra.CharP.Invertible
import Mathlib.FieldTheory.IsSepClosed

/-!
# Native absolute residue fields and their literal full roots target

Store the original two fields and coefficient algebra once. The separable
field, residue Galois group and roots group are computed from these data.
The roots group is literally the full primeToRootsSystem inverse limit,
indexed by InvertibleExponent, without a further subtype restriction.

The residue conclusions below are an OUTPUT certificate. Its constructor
uses algebraic closedness and standard separable-closure facts in this
field-only owner, before the original fraction field or groups are joined.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory

universe u w

/-- The literal residue fields and their existing coefficient action. -/
structure NativeAbsoluteRamificationResidues where
  /-- The original base residue field. -/
  baseResidue : Bundled Field.{u}
  /-- The literal normalization quotient field. -/
  residue : Bundled Field.{w}
  /-- Its actual algebra over the base residue field. -/
  residueAlgebra : Algebra baseResidue.α residue.α

namespace NativeAbsoluteRamificationResidues

variable (R : NativeAbsoluteRamificationResidues.{u, w})

/-- The relative separable closure inside the stored literal quotient. -/
def separableResidue : Bundled Field.{w} :=
  nativeSeparableResidueField R.baseResidue.α R.residue R.residueAlgebra

/-- The stored separable carrier is the existing relative separable closure. -/
theorem separableResidue_carrier :
    let := R.residueAlgebra
    R.separableResidue.α = separableClosure R.baseResidue.α R.residue.α := by
  intro a
  rfl

/-- The actual Galois group of the stored separable residue extension. -/
def residueAutomorphisms : GrpCat.{w} :=
  nativeSeparableResidueGroup R.baseResidue.α R.residue R.residueAlgebra

/-- The full roots group over the SAME stored relative separable closure. -/
def rootsGroup : GrpCat.{w} :=
  nativeSeparableRootsGroup R.baseResidue.α R.residue R.residueAlgebra

instance rootsGroup_topology : TopologicalSpace R.rootsGroup.carrier :=
  nativeSeparableRootsGroup_topology R.baseResidue.α R.residue R.residueAlgebra

/-- The target is the literal full inverse limit, with no restricted index. -/
theorem rootsGroup_full :
    R.rootsGroup =
      GrpCat.of (primeToRootsSystem R.baseResidue.α R.separableResidue.α).inverseLimit :=
  rfl

/-- The coefficient action is the existing separable residue action on every full exponent. -/
def rootsAction
    (σ : R.residueAutomorphisms.carrier) (x : R.rootsGroup.carrier) :
    R.rootsGroup.carrier :=
  nativeSeparableRootsAction_apply R.baseResidue.α R.residue R.residueAlgebra σ x

end NativeAbsoluteRamificationResidues

/-- Closure and literal full-index conclusions, separated from the original group context. -/
structure NativeAbsoluteResidueConclusions
    (R : NativeAbsoluteRamificationResidues.{u, w}) : Prop where
  /-- The literal quotient is an algebraic closure of the original residue field. -/
  algebraic_closure : let := R.residueAlgebra; IsAlgClosure R.baseResidue.α R.residue.α
  /-- Its relative separable part is indeed an absolute separable closure. -/
  separable_closure : let := R.residueAlgebra
    IsSepClosure R.baseResidue.α (separableClosure R.baseResidue.α R.residue.α)
  /-- Every displayed index is positive and residue-invertible. -/
  index_positive_invertible : ∀ n : InvertibleExponent R.baseResidue.α,
    0 < n.val ∧ IsUnit (n.val : R.baseResidue.α)
  /-- In positive characteristic the index consists exactly of integers prime to p. -/
  index_coprime : ∀ (p : ℕ) [Fact p.Prime] [CharP R.baseResidue.α p] (n : ℕ),
    IsUnit (n : R.baseResidue.α) ↔ Nat.Coprime n p
  /-- In characteristic zero EVERY positive integer occurs in the full index. -/
  index_char_zero : ∀ [CharZero R.baseResidue.α] (n : ℕ), 0 < n →
    ∃ e : InvertibleExponent R.baseResidue.α, e.val = n

/-- Construct every residue conclusion from actual algebraicity and closedness. -/
theorem nativeAbsoluteResidueConclusions_of_algebraic_isAlgClosed
    (R : NativeAbsoluteRamificationResidues.{u, w})
    (hclosed : IsAlgClosed R.residue.α)
    (halgebraic : let := R.residueAlgebra; Algebra.IsAlgebraic R.baseResidue.α R.residue.α) :
    NativeAbsoluteResidueConclusions R where
  algebraic_closure := by
    intro a
    exact ⟨hclosed, halgebraic⟩
  separable_closure := by
    intro a
    have : IsAlgClosed R.residue.α := hclosed
    exact separableClosure.isSepClosure R.baseResidue.α R.residue.α
  index_positive_invertible := fun n => ⟨InvertibleExponent.pos R.baseResidue.α n, n.property⟩
  index_coprime := by
    intro p hp hchar n
    exact (CharP.isUnit_natCast_iff (R := R.baseResidue.α) (p := p)
      (Fact.out : p.Prime)).trans
        ⟨fun hn => ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn).symm,
          fun hn => (Fact.out : p.Prime).coprime_iff_not_dvd.mp hn.symm⟩
  index_char_zero := by
    intro hchar n hn
    exact ⟨⟨n, isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')⟩, rfl⟩

end EtaleFundamentalGroups.Inertia

end
