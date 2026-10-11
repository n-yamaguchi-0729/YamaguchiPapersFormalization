/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Scheme Ideal Sheaf Data is Reduced subscheme vanishing Ideal and le ker
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace P2mReducedInduced

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

theorem isRadical_vanishingIdeal_ideal (Z : Closeds X) (U : X.affineOpens) :
    ((vanishingIdeal Z).ideal U).IsRadical := by
  rw [vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

theorem isReduced_subscheme_vanishingIdeal (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  let I := vanishingIdeal Z
  have h : ∀ U : X.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := by
    intro U
    have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_vanishingIdeal_ideal Z U)
    change IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact (IsReduced.iff_of_openCover _ I.subschemeCover.openCover).mpr h

theorem range_subschemeι_vanishingIdeal (Z : Closeds X) :
    Set.range (vanishingIdeal Z).subschemeι = (Z : Set X) := by
  rw [range_subschemeι]
  rfl

theorem basicOpen_inter_eq_empty_of_mem_vanishingIdeal (Z : Closeds X) (U : X.affineOpens)
    {s : Γ(X, U)} (hs : s ∈ (vanishingIdeal Z).ideal U) :
    (X.basicOpen s : Set X) ∩ Z = ∅ := by
  rw [vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hs
  ext z
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hzZ
  have hzU : z ∈ (U : Set X) := X.basicOpen_le s hz
  rw [← U.2.range_fromSpec] at hzU
  obtain ⟨p, rfl⟩ := hzU
  have hp : s ∈ p.asIdeal := hs p hzZ
  have hp' : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := hz
  rw [U.2.fromSpec_preimage_basicOpen] at hp'
  exact absurd hp ((PrimeSpectrum.mem_basicOpen _ _).mp hp')

theorem vanishingIdeal_le_ker {T : Scheme.{u}} [IsReduced T] (Z : Closeds X) (f : T ⟶ X)
    (hf : Set.range f ⊆ Z) : vanishingIdeal Z ≤ f.ker := by
  rw [Scheme.Hom.ker, le_ofIdeals_iff]
  intro U s hs
  rw [RingHom.mem_ker]
  have hb : T.basicOpen ((f.app U).hom s) = ⊥ := by
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
      Set.mem_empty_iff_false, iff_false]
    intro ht
    have hmem : f t ∈ (X.basicOpen s : Set X) ∩ Z := ⟨ht, hf ⟨t, rfl⟩⟩
    rw [basicOpen_inter_eq_empty_of_mem_vanishingIdeal Z U hs] at hmem
    exact hmem
  exact (basicOpen_eq_bot_iff _).mp hb

theorem exists_lift_subschemeι_vanishingIdeal {T : Scheme.{u}} [IsReduced T] (Z : Closeds X)
    (f : T ⟶ X) (hf : Set.range f ⊆ Z) :
    ∃! g : T ⟶ (vanishingIdeal Z).subscheme, g ≫ (vanishingIdeal Z).subschemeι = f := by
  refine ⟨IsClosedImmersion.lift (vanishingIdeal Z).subschemeι f ?_,
    IsClosedImmersion.lift_fac _ _ _, ?_⟩
  · rw [ker_subschemeι]
    exact vanishingIdeal_le_ker Z f hf
  · intro g hg
    rw [← cancel_mono (vanishingIdeal Z).subschemeι, hg, IsClosedImmersion.lift_fac]

end P2mReducedInduced

open P2mReducedInduced AlgebraicGeometry.Scheme.IdealSheafData in
theorem
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker {X :
  Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme ∧
      ∀ {T : Scheme.{u}} [IsReduced T] (f : T ⟶ X), Set.range f ⊆ Z →
        vanishingIdeal Z ≤ f.ker :=
  ⟨isReduced_subscheme_vanishingIdeal Z, fun f hf => vanishingIdeal_le_ker Z f hf⟩
end Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
