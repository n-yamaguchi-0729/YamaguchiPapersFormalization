/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsPullback_surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic.Set
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Schemes.IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq

/-!
# Is Pullback surjective app and ker app eq map ker of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.PullbackSectionsKernel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.IsPullback.surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (D : P.Opens) (hD : IsAffineOpen D) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p D
    Function.Surjective (G.app D).hom ∧
      RingHom.ker (G.app D).hom = (RingHom.ker π).map (algebraMap T' Γ(P, D)) := by
  let inst := Scheme.TwoAffineOpenCover.algebraOfHom p D
  obtain ⟨-, ε, hε⟩ :=
    AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker p p₀
      G hG D hD
  have h1 := congrArg Scheme.Hom.appTop hε
  simp only [Scheme.Hom.comp_appTop, Category.assoc] at h1
  have h2 : (G ∣_ D).appTop = D.topIso.hom ≫ G.app D ≫ (G ⁻¹ᵁ D).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    dsimp only [Scheme.Hom.appTop]
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
  have h4 : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T'
    Γ(P, D)))))).appTop =
      ((Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map
        (algebraMap T' Γ(P, D))))) ≫
        (Scheme.ΓSpecIso _).inv :=
    (Iso.eq_comp_inv _).mpr (Scheme.ΓSpecIso_naturality _)
  rw [h2, hD.isoSpec_hom_appTop, h4] at h1
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h1
  have h5 := (cancel_epi (Scheme.ΓSpecIso Γ(P, D)).hom).1 h1
  set Φ : Γ(P₀, G ⁻¹ᵁ D) ⟶ CommRingCat.of (Γ(P, D) ⧸ (RingHom.ker π).map (algebraMap T' Γ(P, D))) :=
    (G ⁻¹ᵁ D).topIso.inv ≫ ε.hom.appTop ≫ (Scheme.ΓSpecIso _).hom with hΦ
  have key : G.app D ≫ Φ = CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap
    T' Γ(P, D)))) := by
    rw [hΦ]
    have h6 := h5 =≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(P, D) ⧸ (RingHom.ker π).map (algebraMap
      T' Γ(P, D))))).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h6
    exact h6
  have : IsIso ε.hom.appTop :=
    ⟨⟨ε.inv.appTop, by rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop],
      by rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]⟩⟩
  have hΦiso : IsIso Φ := by rw [hΦ]; infer_instance
  have hinj : Function.Injective Φ.hom := by
    intro a b hab
    have e : ∀ x, (inv Φ).hom (Φ.hom x) = x := fun x => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id,
        RingHom.id_apply]
    rw [← e a, ← e b, hab]
  have hcomp : ∀ x, Φ.hom ((G.app D).hom x) =
      Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, D))) x := fun x => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, key, CommRingCat.hom_ofHom]
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := (RingHom.ker π).map (algebraMap T' Γ(P,
      D))) (Φ.hom y)
    refine ⟨x, hinj ?_⟩
    rw [hcomp, hx]
  · ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hcomp]
    constructor
    · intro h; rw [h, map_zero]
    · intro h; exact hinj (by rw [h, map_zero])
end AlgebraicCurves.Geometry.Schemes.Proofs.PullbackSectionsKernel
end ProofImplementation
