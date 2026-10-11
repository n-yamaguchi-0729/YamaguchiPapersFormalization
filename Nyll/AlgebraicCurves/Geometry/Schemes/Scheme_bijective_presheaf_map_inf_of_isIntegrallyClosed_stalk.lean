/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Nyll.AlgebraicCurves.Geometry.Schemes.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

/-!
# Scheme bijective presheaf map inf of is Integrally Closed stalk
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (IsLocallyNoetherian AffineSpace.toSpecMvPolyIntEquiv Scheme.Hom
  Scheme.Hom.image_preimage_eq_opensRange_inf Spec Scheme AffineSpace.toSpecMvPolyIntEquiv_comp
  AffineSpace Scheme.Opens Scheme.Opens.ι_image_top Scheme.Opens.ι_appTop Scheme.Opens.opensRange_ι
  existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Hom Γ Hom.image_preimage_eq_opensRange_inf Opens
  Opens.ι_image_top Opens.ι_appTop Opens.opensRange_ι)

namespace HartogsSections

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


/--
The polynomial ring in one variable over lifted integers, viewed as a commutative ring object.
-/
noncomputable abbrev A1 : CommRingCat.{u} := CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u}
  ℤ))

theorem bijective_appTop {T : Scheme.{u}} [IsLocallyNoetherian T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    (V' : T.Opens) (hV' : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V') :
    Function.Bijective (V'.ι.appTop).hom := by
  have H := fun v => AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
    (Y := Spec A1) hT V' hV' v
  let E : (T ⟶ Spec A1) ≃ (PUnit.{u + 1} → Γ(T, ⊤)) := AffineSpace.toSpecMvPolyIntEquiv PUnit.{u +
    1}
  let E' : (V'.toScheme ⟶ Spec A1) ≃ (PUnit.{u + 1} → Γ(V'.toScheme, ⊤)) :=
    AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}
  have hcomp : ∀ φ : T ⟶ Spec A1, E' (V'.ι ≫ φ) PUnit.unit = (V'.ι.appTop).hom (E φ PUnit.unit) :=
    fun φ => AffineSpace.toSpecMvPolyIntEquiv_comp _ _ _ _
  constructor
  · intro r₁ r₂ hr
    let φ₁ := E.symm (fun _ => r₁)
    let φ₂ := E.symm (fun _ => r₂)
    have h1 : E φ₁ PUnit.unit = r₁ := by simp [φ₁]
    have h2 : E φ₂ PUnit.unit = r₂ := by simp [φ₂]
    have hv : V'.ι ≫ φ₁ = V'.ι ≫ φ₂ := by
      apply E'.injective
      funext i
      cases i
      rw [hcomp, hcomp, h1, h2, hr]
    obtain ⟨φ, -, huniq⟩ := H (V'.ι ≫ φ₂)
    have : φ₁ = φ₂ := (huniq φ₁ hv).trans (huniq φ₂ rfl).symm
    rw [← h1, ← h2, this]
  · intro s
    obtain ⟨φ, hφ, -⟩ := H (E'.symm (fun _ => s))
    refine ⟨E φ PUnit.unit, ?_⟩
    rw [← hcomp, hφ, Equiv.apply_symm_apply]

theorem bijective_transport {X : Scheme.{u}} {A A' B B' : X.Opens} (hA : A = A') (hB : B = B')
    (k : B ⟶ A) (h : B' ≤ A') (hb : Function.Bijective (X.presheaf.map k.op)) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  subst hA hB
  have : k = homOfLE h := Subsingleton.elim _ _
  subst this
  exact hb

end AlgebraicGeometry.Scheme.HartogsSections


open _root_.AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme


theorem _root_.AlgebraicGeometry.Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (V U : X.Opens)
    (hV : ∀ x : X, x ∈ V → IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hU : ∀ x : X, x ∈ V → ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) := by
  let T : Scheme.{u} := V.toScheme
  let V' : T.Opens := V.ι ⁻¹ᵁ U
  have hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x) := by
    intro x
    let e : T.presheaf.stalk x ≃+* X.presheaf.stalk x.1 := (V.stalkIso x).commRingCatIsoToRingEquiv
    obtain ⟨h1, h2⟩ := hV x.1 x.2
    have : IsDomain (T.presheaf.stalk x) := MulEquiv.isDomain (X.presheaf.stalk x.1) e.toMulEquiv
    exact ⟨this, IsIntegrallyClosed.of_equiv e.symm⟩
  have hV' : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V' := by
    intro x hx
    have e : T.presheaf.stalk x ≃+* X.presheaf.stalk x.1 := (V.stalkIso x).commRingCatIsoToRingEquiv
    rw [ringKrullDim_eq_of_ringEquiv e] at hx
    exact hU x.1 x.2 hx
  have hb := HartogsSections.bijective_appTop hT V' hV'
  rw [Scheme.Opens.ι_appTop] at hb
  change Function.Bijective (X.presheaf.map (V.ι.opensFunctor.map
    (homOfLE (le_top : V'.ι ''ᵁ ⊤ ≤ ⊤))).op) at hb
  refine HartogsSections.bijective_transport ?_ ?_ _ _ hb
  · exact V.ι_image_top
  · rw [Scheme.Opens.ι_image_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
end Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
