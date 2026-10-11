/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteNormCompleteExtension
import ValuedFieldTheory.Valuation.FiniteResidueExtension
import ValuedFieldTheory.Valuation.DiscreteValuationField.TorsionFiniteness
import Mathlib.Algebra.CharP.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# Higher local fields and finiteness of roots of unity

A zero-dimensional higher local field is a finite field. At each successor
step we choose a complete discrete valuation whose actual residue field is
one dimension lower. No Galois-theoretic or finite-extension permanence
property is included in the definition.

Finiteness of all roots of unity is proved by induction on this actual
residue tower, using the reduction map in each of the characteristic cases.
-/

namespace ValuationTheory

open ValuationTheory.DiscreteValuationField

universe u v

/-- A finite residue tower of complete discretely valued fields ending in
a finite field. The value groups of the chosen valuations lie in `Type v`. -/
def IsHigherLocalField (n : ℕ) (K : Type u) [Field K] : Prop :=
  match n with
  | 0 => Finite K
  | n + 1 => ∃ D : CompleteDVF.{u, v} K, IsHigherLocalField n D.residueField

/-- Every higher local field has finitely many roots of unity, in all
characteristics and dimensions. -/
theorem IsHigherLocalField.finite_torsion
    (n : ℕ) (K : Type u) [Field K] (hK : IsHigherLocalField.{u, v} n K) :
    Finite (CommGroup.torsion Kˣ) := by
  induction n generalizing K with
  | zero =>
    have : Finite K := hK
    infer_instance
  | succ n ih =>
    obtain ⟨D, hD⟩ := hK
    have : Finite (CommGroup.torsion D.residueFieldˣ) := ih D.residueField hD
    rcases CharP.exists' K with hzero | ⟨p, hp, hKp⟩
    · have : CharZero K := hzero
      rcases CharP.exists' D.residueField with hreszero | ⟨p, hp, hresp⟩
      · have : CharZero D.residueField := hreszero
        exact D.toHenselianDVF.finite_torsion_of_finite_residueTorsion
      · have : Fact p.Prime := hp
        have : CharP D.residueField p := hresp
        exact D.toDVF.finite_torsion_of_finite_residueTorsion_mixedChar p
    · have : Fact p.Prime := hp
      have : CharP K p := hKp
      exact D.toDVF.finite_torsion_of_finite_residueTorsion_charP p

/-- A finite field extension of an `n`-dimensional higher local field is
again an `n`-dimensional higher local field. Its valuation and residue
tower are produced by the conclusion. -/
theorem IsHigherLocalField.of_finiteExtension
    (n : ℕ) (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (hK : IsHigherLocalField.{u, v} n K) :
    IsHigherLocalField.{u, v} n L := by
  induction n generalizing K L with
  | zero =>
    change Finite K at hK
    change Finite L
    have : Finite K := hK
    exact Module.finite_of_finite K
  | succ n ih =>
    obtain ⟨D, hD⟩ := hK
    let E : CompleteDVF.{u, v} L := D.finiteExtension L
    have : D.valuation.HasExtension E.valuation := D.finiteExtension_hasExtension L
    have : FiniteDimensional D.residueField E.residueField :=
      _root_.Valuation.finiteDimensional_residueField D.valuation E.valuation
    exact ⟨E, ih D.residueField E.residueField hD⟩

end ValuationTheory
