/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationDegreeLift
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Multiplication covers of degree invertible in the ground field

The actual multiplication map is finite étale whenever its integer is a unit.
Combined with the degree lifting theorem, this supplies a multiplication cover
over every connected finite étale cover whose degree is invertible, in arbitrary
characteristic.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] {A : Scheme} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

include hc in
/-- Multiplication by an invertible integer is an actual finite étale morphism. -/
theorem isFiniteEtale_schemeNsmul_of_isUnit (n : ℕ) (hn : IsUnit (n : K)) :
    IsFiniteEtale (G.schemeNsmul n) := by
  obtain ⟨d, hd⟩ := G.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have _ : SmoothOfRelativeDimension d f := hd
  have _ : Etale (G.schemeNsmul n) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d n hn
  have _ : IsProper (G.schemeNsmul n) := by
    have _ : IsProper (G.schemeNsmul n ≫ f) := by
      rw [G.schemeNsmul_over]
      infer_instance
    exact IsProper.of_comp _ f
  have _ : LocallyQuasiFinite (G.schemeNsmul n) := locallyQuasiFinite_of_etale _
  have _ : IsFinite (G.schemeNsmul n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  exact IsFiniteEtale.mk

/-- The original multiplication morphism bundled as a finite étale cover. -/
def unitMultiplicationCover (n : ℕ) (hn : IsUnit (n : K)) : FiniteEtale A := by
  have _ : IsFiniteEtale (G.schemeNsmul n) := G.isFiniteEtale_schemeNsmul_of_isUnit hc n hn
  exact FiniteEtale.mk (G.schemeNsmul n)

theorem isConnected_unitMultiplicationCover [GeometricallyConnected f]
    (n : ℕ) (hn : IsUnit (n : K)) : IsConnected (G.unitMultiplicationCover hc n hn) := by
  have _ : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  have _ : ConnectedSpace (G.unitMultiplicationCover hc n hn).left :=
    inferInstanceAs (ConnectedSpace A)
  exact FiniteEtale.isConnected_of_connectedSpace_left (G.unitMultiplicationCover hc n hn)

/-- Every connected finite étale cover of invertible degree is dominated by
the multiplication cover of that same degree, without a characteristic-zero hypothesis. -/
theorem nonempty_unitMultiplicationCover_hom [IsSepClosed K] [GeometricallyConnected f]
    (W : FiniteEtale A) [IsConnected W]
    (hn : IsUnit ((Nat.card ((fiber (G.one (𝟙 (Spec (.of K)))).1).obj W)) : K)) :
    Nonempty (G.unitMultiplicationCover hc
      (Nat.card ((fiber (G.one (𝟙 (Spec (.of K)))).1).obj W)) hn ⟶ W) := by
  obtain ⟨a, ha⟩ := G.exists_schemeNsmul_lift_degree W
  exact ⟨MorphismProperty.Over.homMk a ha⟩

end GoodReductionJacobian.RelativeGroupLaw
