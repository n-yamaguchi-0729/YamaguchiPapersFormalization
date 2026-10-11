/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateComparison
import Nyll.ProCGroups.Abelian.FullTateCharacters

/-!
# Finite-exponent characters factor through actual multiplication covers

The full Tate comparison and the explicit kernel calculation show that a
character killed by n factors through monodromy of the actual n-multiplication
cover. This uses the same integer n, without a larger auxiliary level.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A character of exponent dividing n is evaluated on the actual
n-torsion displacement of the multiplication cover. -/
theorem character_factors_multiplicationMonodromy
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {J : Scheme} {b : J ⟶ Spec (.of K)}
    [IsProper b] [Smooth b] [GeometricallyConnected b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative)
    {H : Type} [AddCommGroup H] (n : ℕ+)
    (χ : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) →* Multiplicative H)
    (hH : ∀ a : H, (n : ℕ) • a = 0) :
    ∃ ψ : ProCGroups.torsionLevel (G.AlgPoints hc K) n →+ H,
      ∀ g, ψ (G.multiplicationMonodromy hc n g) = (χ g).toAdd := by
  let E := G.fundamentalGroupEquivFullTate hc
  let φ : ProCGroups.FullTateModule (G.AlgPoints hc K) →+ H :=
    { toFun := fun x => (χ (E.symm (Multiplicative.ofAdd x))).toAdd
      map_zero' := by
        change (χ (E.symm 1)).toAdd = 0
        rw [map_one, map_one]
        rfl
      map_add' := by
        intro x y
        change (χ (E.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y))).toAdd =
          (χ (E.symm (Multiplicative.ofAdd x))).toAdd +
            (χ (E.symm (Multiplicative.ofAdd y))).toAdd
        rw [map_mul, map_mul]
        rfl }
  have hsurj : Function.Surjective
      (ProCGroups.FullTateModule.projection (G.AlgPoints hc K) n) := by
    intro z
    obtain ⟨g, hg⟩ := G.multiplicationMonodromy_surjective hc n z
    exact ⟨(E g).toAdd, hg⟩
  obtain ⟨ψ, hψ⟩ := ProCGroups.FullTateModule.character_factors_through_projection
    n hsurj φ hH
  refine ⟨ψ, ?_⟩
  intro g
  have h := DFunLike.congr_fun hψ (E g).toAdd
  change ψ (G.multiplicationMonodromy hc n g) =
    (χ (E.symm (E g))).toAdd at h
  rw [E.symm_apply_apply] at h
  exact h

end GoodReductionJacobian.RelativeGroupLaw
