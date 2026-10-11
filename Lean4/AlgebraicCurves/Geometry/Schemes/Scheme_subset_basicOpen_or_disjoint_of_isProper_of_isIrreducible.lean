/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Properties
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Modules.ProjectivePresentation
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme

/-!
# Scheme subset basic Open or disjoint of is Proper of is Irreducible
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace C2E5

theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) (hZ' :
  IsIrreducible Z) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI
  have : IrreducibleSpace I.subscheme := by
    have h : IsIrreducible ((I.support : TopologicalSpace.Closeds X) : Set X) := by
      rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact hZ'
    exact Subtype.irreducibleSpace h
  have hred : ∀ U : X.affineOpens, _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) := fun U => by
    rw [← Ideal.isRadical_iff_quotient_reduced, hI, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    have := hred U
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(X, U.1) ⧸ I.ideal U))))
  have : IsReduced I.subscheme := IsReduced.of_openCover (X := I.subscheme)
    I.subschemeCover.openCover
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem _root_.AlgebraicGeometry.Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
      [IsProper t]
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z) (U : X.Opens) (hZU : Z ⊆ U) (g : Γ(X, U))
      :
    Z ⊆ X.basicOpen g ∨ Disjoint Z (X.basicOpen g) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI
  have : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal Z hZ hZ'
  have hrange : Set.range I.subschemeι.base = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : UniversallyClosed (I.subschemeι ≫ t) := inferInstance
  have hF : IsField Γ(I.subscheme, ⊤) := isField_of_universallyClosed k (I.subschemeι ≫ t)
  have hpre : I.subschemeι ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    change I.subschemeι.base z ∈ U
    exact hZU (hrange ▸ Set.mem_range_self z)
  have hF' : IsField Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) := by rw [hpre]; exact hF
  let := hF'.toField
  have key : I.subschemeι ⁻¹ᵁ X.basicOpen g = I.subscheme.basicOpen (I.subschemeι.app U g) :=
    Scheme.preimage_basicOpen I.subschemeι g
  by_cases h0 : I.subschemeι.app U g = 0
  · right
    rw [Set.disjoint_left]
    rintro z hz hzg
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    have : z' ∈ I.subschemeι ⁻¹ᵁ X.basicOpen g := hzg
    rw [key, h0, Scheme.basicOpen_zero] at this
    exact this
  · left
    intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    change z' ∈ I.subschemeι ⁻¹ᵁ X.basicOpen g
    rw [key, I.subscheme.basicOpen_of_isUnit (isUnit_iff_ne_zero.mpr h0), hpre]
    trivial

end C2E5
end Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

attribute [local instance] MvPolynomial.gradedAlgebra
