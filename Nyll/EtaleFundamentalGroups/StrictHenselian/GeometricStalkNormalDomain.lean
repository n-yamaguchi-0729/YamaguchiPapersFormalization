/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.RingHom.Etale


/-!
# The actual geometric étale stalk over a normal domain is a domain

A zero-product relation between two germs descends to an actual pointed étale
neighborhood, then to an affine refinement. Localizing its sections at the
prime selected by the geometric point gives a domain, by normality of prime
localizations of étale algebras over a normal domain. Its localized germ map
carries one of the two zero factors back to the geometric stalk.

No discrete valuation, Noetherianity, or localness of the base ring is needed.
This supplies the domain needed to use the actual fraction field of a strict
henselization over a normal local ring. Integral closedness of this stalk and
the generic tensor comparison are separate results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] (φ : R →+* Ω)

/-- The actual étale stalk at any geometric point of a normal domain is a
 domain. The zero-product relation is descended to a localized affine étale
 neighborhood, whose domain property is already proved. -/
instance geometricStalk_isDomain_of_normal :
    IsDomain (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  have : NoZeroDivisors (geometricStalk s) := ⟨by
    intro a b hab
    obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representatives s ![a, b]
    have hza : geometricStalkGerm s W t (z 0) = a := hz 0
    have hzb : geometricStalkGerm s W t (z 1) = b := hz 1
    have hzero : geometricStalkGerm s W t (z 0 * z 1) =
        geometricStalkGerm s W t 0 := by
      rw [map_mul, map_zero, hza, hzb]
      exact hab
    obtain ⟨W₁, f, t₁, hf, hzero₁⟩ :=
      ((Scheme.pointEtaleNeighborhoods s).toPresheafFiber_eq_iff'
        (P := etaleSections (Spec (CommRingCat.of R))) W t (z 0 * z 1) 0).mp hzero
    change f.left.appTop (z 0 * z 1) = f.left.appTop 0 at hzero₁
    rw [map_zero] at hzero₁
    obtain ⟨V, v, g, hVaffine, hg⟩ := geometricStalk_exists_affine_refinement s W₁ t₁
    have : IsAffine V.left := hVaffine
    let j : V ⟶ W := g ≫ f
    have hj : (Scheme.pointEtaleNeighborhoods s).fiber.map j v = t := by
      change (Scheme.pointEtaleNeighborhoods s).fiber.map (g ≫ f) v = t
      rw [Functor.map_comp]
      change (Scheme.pointEtaleNeighborhoods s).fiber.map f
        ((Scheme.pointEtaleNeighborhoods s).fiber.map g v) = t
      rw [hg, hf]
    let δ : Γ(W.left, ⊤) ⟶ Γ(V.left, ⊤) := j.left.appTop
    have hzeroV : δ (z 0) * δ (z 1) = 0 := by
      rw [← map_mul]
      change (g.left ≫ f.left).appTop (z 0 * z 1) = 0
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hzero₁, map_zero]
    let β : R →+* Γ(V.left, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
    let : Algebra R Γ(V.left, ⊤) := β.toAlgebra
    have hβ : β.Etale := by
      change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Etale
      apply RingHom.Etale.stableUnderComposition
      · exact RingHom.Etale.of_bijective
          ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
            inferInstance)
      · exact HasRingHomProperty.appTop (P := @Etale)
          (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) inferInstance
    have : Algebra.Etale R Γ(V.left, ⊤) := hβ
    let B := Localization.AtPrime (geometricNeighborhoodPrime s V v).asIdeal
    have : IsDomain B :=
      (Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
        R Γ(V.left, ⊤) (geometricNeighborhoodPrime s V v).asIdeal B).1
    have hzeroB : algebraMap Γ(V.left, ⊤) B (δ (z 0)) *
        algebraMap Γ(V.left, ⊤) B (δ (z 1)) = 0 := by
      rw [← map_mul, hzeroV, map_zero]
    have hgerm : δ ≫ geometricStalkGerm s V v = geometricStalkGerm s W t := by
      have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
        j v (etaleSections (Spec (CommRingCat.of R)))
      rw [hj] at h
      exact h
    have hrepresent (i : Fin 2) :
        geometricStalkLocalizedGerm s V v (algebraMap Γ(V.left, ⊤) B (δ (z i))) =
          geometricStalkGerm s W t (z i) := by
      rw [geometricStalkLocalizedGerm_apply]
      exact ConcreteCategory.congr_hom hgerm (z i)
    rcases mul_eq_zero.mp hzeroB with ha | hb
    · left
      calc
        a = geometricStalkLocalizedGerm s V v
            (algebraMap Γ(V.left, ⊤) B (δ (z 0))) := ((hrepresent 0).trans hza).symm
        _ = 0 := by rw [ha, map_zero]
    · right
      calc
        b = geometricStalkLocalizedGerm s V v
            (algebraMap Γ(V.left, ⊤) B (δ (z 1))) := ((hrepresent 1).trans hzb).symm
        _ = 0 := by rw [hb, map_zero]⟩
  exact NoZeroDivisors.to_isDomain (geometricStalk s)

end EtaleFundamentalGroups.StrictHenselian
