/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isReduced_of_etale.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Tactic.Set
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing

/-!
# is Reduced of etale
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.isReduced_of_etale
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace L3gen

theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hI
  have hrad : I.radical = I := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    have hsupp : I.support = Z := by
      apply Closeds.ext
      rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rw [hsupp]
  have : ∀ U : I.subschemeCover.openCover.I₀, IsReduced (I.subschemeCover.openCover.X U) := by
    change ∀ U : X.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    intro U
    show IsReduced (Spec _)
    rw [affine_isReduced_iff]
    change _root_.IsReduced (_ ⧸ I.ideal U)
    have hradU : (I.ideal U).radical = I.ideal U := by
      rw [← Scheme.IdealSheafData.radical_ideal, hrad]
    exact (Ideal.isRadical_iff_quotient_reduced _).mp (hradU ▸ Ideal.radical_isRadical _)
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

theorem reduced_source {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] [IsLocallyNoetherian
  Y] : IsReduced X := by
  suffices h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) by
    have := h; exact isReduced_of_isReduced_stalk X
  intro x
  obtain ⟨U, hU, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base
    x)) isOpen_univ
  obtain ⟨U', hU'aff, rfl⟩ := hU
  have hxV0 : x ∈ (f ⁻¹ᵁ U' : X.Opens) := hxU
  obtain ⟨V, hV, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV0 (f ⁻¹ᵁ U').2
  obtain ⟨V', hV'aff, rfl⟩ := hV
  have het : (f.appLE U' V' hVU).hom.Etale := Etale.etale_appLE f hU'aff hV'aff hVU
  let := (f.appLE U' V' hVU).hom.toAlgebra
  have : Algebra.Etale Γ(Y, U') Γ(X, V') := het
  have : IsNoetherianRing Γ(Y, U') := IsLocallyNoetherian.component_noetherian ⟨U', hU'aff⟩
  have : _root_.IsReduced Γ(Y, U') := IsReduced.component_reduced _
  have hredV : _root_.IsReduced Γ(X, V') :=
    Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing Γ(Y, U') Γ(X, V')
  have : IsAffine (V' : Scheme.{u}) := hV'aff
  let : Algebra Γ(X, V') (X.presheaf.stalk ((⟨x, hxV⟩ : V') : X)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V')
  have := hV'aff.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV'aff.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk ((⟨x, hxV⟩ : V') : X)) hredV

end L3gen

theorem _root_.AlgebraicGeometry.isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := L3gen.reduced_source f
end AlgebraicCurves.Geometry.Schemes.Proofs.isReduced_of_etale
end ProofImplementation
