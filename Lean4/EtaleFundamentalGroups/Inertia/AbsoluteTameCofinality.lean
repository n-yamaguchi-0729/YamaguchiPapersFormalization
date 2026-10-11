/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.CategoryTheory.CommAlgRingMap
import EtaleFundamentalGroups.Inertia.AbsoluteNormalizationRadicalStage
import EtaleFundamentalGroups.Inertia.AbsoluteTameRootsSystem
import EtaleFundamentalGroups.Inertia.FiniteNormalizationRadicalTameDivisibility
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Cofinality of the actual finite tame orders in every invertible exponent

The chosen finite Galois normalization contains an actual root of a base
uniformizer. The finite-ring divisibility theorem supplies its actual tame
order as a multiple of the prescribed exponent. Thus the literal finite
degree image set is cofinal in the full divisibility order.

Reference: https://stacks.math.columbia.edu/tag/0BUB
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The native finite-field owner supplies radical divisibility before the
original upper normalization prime is introduced. -/
private theorem finiteAbsoluteNormalization_radical_exponent_dvd_tameOrder
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsGalois K Ω]
    (E : FiniteGaloisIntermediateField K Ω) :
    let : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K Ω E) :=
      finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K Ω E
    ∀ (q : Ideal (finiteAbsoluteNormalizationAlgebra A K Ω E)) [q.IsPrime]
      (hq : q ≠ ⊥) (n : ℕ), IsUnit (n : A) → ∀ (π : A), Irreducible π →
      ∀ (γ : finiteAbsoluteNormalizationAlgebra A K Ω E),
      γ ^ n = (commAlgCoefficientMap (finiteAbsoluteNormalizationAlgebra A K Ω E)).toFun π →
      n ∣ commAlgIdealTameOrder A (finiteAbsoluteNormalizationAlgebra A K Ω E) q hq := by
  dsimp only
  intro q qPrime hq n hn π hπ γ hγ
  let q' : Ideal (normalizationCommAlgCat A (finiteLevelFieldAlgebra A K Ω E)) := q
  have : q'.IsPrime := qPrime
  exact finiteNormalization_radical_exponent_dvd_tameOrder A K
    (finiteLevelFieldAlgebra A K Ω E) q' hq n hn π hπ γ hγ

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]

/-- Every exponent invertible in the original DVR divides the actual tame
order at the chosen original prime of some finite Galois subextension. -/
theorem exists_actualFiniteStageTameOrder_multiple
    (n : ℕ) (hn : IsUnit (n : A)) :
    ∃ E : FiniteGaloisIntermediateField K Ω, n ∣ actualFiniteStageTameOrder A K Ω Q E := by
  obtain ⟨E, π, γ, hπ, hγ⟩ :=
    exists_finiteAbsoluteNormalization_uniformizer_radical A K Ω n hn
  have := finiteAbsoluteNormalizationPrime_isPrime A K Ω Q E
  refine ⟨E, ?_⟩
  exact finiteAbsoluteNormalization_radical_exponent_dvd_tameOrder A K Ω E
    (finiteAbsoluteNormalizationPrime A K Ω Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K Ω Q E) n hn π hπ γ hγ

/-- The actual image of finite tame degrees is cofinal among all positive
exponents invertible in the base residue field. In characteristic zero this
includes every positive integer. -/
theorem actualFiniteTameDegreeSet_cofinal :
    ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : actualFiniteTameDegreeSet A K Ω Q, n ≤ t.val := by
  intro n
  have hnA : IsUnit (n.val : A) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (n.val : A)).mp (by
      simpa only [map_natCast] using n.property.ne_zero)
  obtain ⟨E, hE⟩ := exists_actualFiniteStageTameOrder_multiple A K Ω Q n.val hnA
  refine ⟨⟨actualFiniteStageTameIndex A K Ω Q E, ⟨E, rfl⟩⟩, ?_⟩
  exact hE

end EtaleFundamentalGroups.Inertia

end
