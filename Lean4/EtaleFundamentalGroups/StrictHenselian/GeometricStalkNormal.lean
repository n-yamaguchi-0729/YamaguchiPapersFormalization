/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.RingHom.Etale


/-!
# Integral closedness of the actual geometric étale stalk

A monic integral equation and the numerator and denominator of a fraction
have representatives on one actual pointed étale neighborhood. Clearing the
denominator with `Polynomial.scaleRoots` gives an equality of sections, which
descends to a further affine neighborhood. Its local ring at the selected
prime is normal. Normality there supplies a quotient of the numerator by the
denominator, and the localized germ map carries that divisibility equation
back to the actual stalk.

The denominator is nonzero in the local stage because its germ is nonzero.
No injectivity of localized germ maps, normalization comparison, or normality
of the geometric stalk is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Combine the existing monic-polynomial representative and a pair of germs
using an actual common pointed neighborhood. -/
private theorem geometricStalk_exists_monic_and_pair
    {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) (p : (geometricStalk s)[X]) (hp : p.Monic)
    (a b : geometricStalk s) :
    ∃ (W : S.Etale) (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)
      (q : Γ(W.left, ⊤)[X]) (aW bW : Γ(W.left, ⊤)),
      q.Monic ∧ q.map (geometricStalkGerm s W t).hom = p ∧
        geometricStalkGerm s W t aW = a ∧ geometricStalkGerm s W t bW = b := by
  obtain ⟨Wp, tp, q, hq, hqp⟩ := geometricStalk_monic_exists_representative s p hp
  obtain ⟨Wa, ta, za, zb, hza, hzb⟩ :=
    (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_jointly_surjective₂
      (P := etaleSections S) a b
  obtain ⟨Z, f, g, _⟩ := IsCofilteredOrEmpty.cone_objs
    ((Scheme.pointEtaleNeighborhoods s).fiber.elementsMk Wp tp)
    ((Scheme.pointEtaleNeighborhoods s).fiber.elementsMk Wa ta)
  have hpoly : f.hom.left.appTop ≫ geometricStalkGerm s Z.obj Z.val =
      geometricStalkGerm s Wp tp := by
    have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
      f.hom Z.val (etaleSections S)
    have hf : (Scheme.pointEtaleNeighborhoods s).fiber.map f.hom Z.val = tp := f.map_val
    rw [hf] at h
    exact h
  have hpair : g.hom.left.appTop ≫ geometricStalkGerm s Z.obj Z.val =
      geometricStalkGerm s Wa ta := by
    have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
      g.hom Z.val (etaleSections S)
    have hg : (Scheme.pointEtaleNeighborhoods s).fiber.map g.hom Z.val = ta := g.map_val
    rw [hg] at h
    exact h
  refine ⟨Z.obj, Z.val, q.map f.hom.left.appTop.hom,
    g.hom.left.appTop za, g.hom.left.appTop zb, hq.map _, ?_, ?_, ?_⟩
  · rw [Polynomial.map_map]
    change q.map (f.hom.left.appTop ≫ geometricStalkGerm s Z.obj Z.val).hom = p
    rw [hpoly]
    exact hqp
  · exact (ConcreteCategory.congr_hom hpair za).trans hza
  · exact (ConcreteCategory.congr_hom hpair zb).trans hzb

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] (φ : R →+* Ω)

/-- The actual geometric étale stalk over a normal domain is integrally closed.
The proof descends an integral equation after clearing its denominator and
uses normality of an actual prime-localized affine étale neighborhood. -/
instance geometricStalk_isIntegrallyClosed_of_normal :
    IsIntegrallyClosed (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  let A := geometricStalk s
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective A x
  have hscaled : (p.scaleRoots b).eval a = 0 := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_zero, ← Polynomial.eval₂_at_apply]
    apply Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero
      (IsFractionRing.injective A (FractionRing A)) _ hb
    rw [hfrac]
    exact hpx
  obtain ⟨W, t, q, aW, bW, hq, hqp, haW, hbW⟩ :=
    geometricStalk_exists_monic_and_pair s p hp a b
  let u : Γ(W.left, ⊤) := (q.scaleRoots bW).eval aW
  have hzero : geometricStalkGerm s W t u = geometricStalkGerm s W t 0 := by
    change (geometricStalkGerm s W t).hom ((q.scaleRoots bW).eval aW) = _
    rw [map_zero, ← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_scaleRoots q bW (geometricStalkGerm s W t).hom
        (by rw [hq.leadingCoeff, map_one]; exact one_ne_zero), hqp, haW, hbW]
    exact hscaled
  obtain ⟨W₁, f, t₁, hf, hzero₁⟩ :=
    ((Scheme.pointEtaleNeighborhoods s).toPresheafFiber_eq_iff'
      (P := etaleSections (Spec (CommRingCat.of R))) W t u 0).mp hzero
  change f.left.appTop u = f.left.appTop 0 at hzero₁
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
  have hzeroV : δ u = 0 := by
    change (g.left ≫ f.left).appTop u = 0
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
  obtain ⟨hBdomain, hBnormal⟩ :=
    Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
      R Γ(V.left, ⊤) (geometricNeighborhoodPrime s V v).asIdeal B
  have : IsDomain B := hBdomain
  have : IsIntegrallyClosed B := hBnormal
  let ρ : Γ(W.left, ⊤) →+* B := (algebraMap Γ(V.left, ⊤) B).comp δ.hom
  let θ : B →+* A := geometricStalkLocalizedGerm s V v
  have hgerm : δ ≫ geometricStalkGerm s V v = geometricStalkGerm s W t := by
    have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
      j v (etaleSections (Spec (CommRingCat.of R)))
    rw [hj] at h
    exact h
  have hrepresent (z : Γ(W.left, ⊤)) : θ (ρ z) = geometricStalkGerm s W t z := by
    change geometricStalkLocalizedGerm s V v (algebraMap Γ(V.left, ⊤) B (δ z)) = _
    rw [geometricStalkLocalizedGerm_apply]
    exact ConcreteCategory.congr_hom hgerm z
  have hden : ρ bW ≠ 0 := by
    intro h
    apply nonZeroDivisors.ne_zero hb
    calc
      b = θ (ρ bW) := ((hrepresent bW).trans hbW).symm
      _ = 0 := by rw [h, map_zero]
  have hzeroB : ρ ((q.scaleRoots bW).eval aW) = 0 := by
    change algebraMap Γ(V.left, ⊤) B (δ u) = 0
    rw [hzeroV, map_zero]
  let qB : B[X] := q.map ρ
  have hscaledB : (qB.scaleRoots (ρ bW)).eval (ρ aW) = 0 := by
    change ((q.map ρ).scaleRoots (ρ bW)).eval (ρ aW) = 0
    rw [← Polynomial.map_scaleRoots q bW ρ
      (by rw [hq.leadingCoeff, map_one]; exact one_ne_zero), Polynomial.eval_map_apply]
    exact hzeroB
  let xB : FractionRing B :=
    algebraMap B (FractionRing B) (ρ aW) / algebraMap B (FractionRing B) (ρ bW)
  have hdenF : algebraMap B (FractionRing B) (ρ bW) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr hden
  have hxB : IsIntegral B xB := by
    refine ⟨qB, hq.map ρ, ?_⟩
    have hmul : algebraMap B (FractionRing B) (ρ bW) * xB =
        algebraMap B (FractionRing B) (ρ aW) := mul_div_cancel₀ _ hdenF
    have hproduct : algebraMap B (FractionRing B) (ρ bW) ^ qB.natDegree *
        qB.eval₂ (algebraMap B (FractionRing B)) xB = 0 := by
      rw [← Polynomial.scaleRoots_eval₂_mul, hmul, Polynomial.eval₂_at_apply,
        hscaledB, map_zero]
    exact (mul_eq_zero.mp hproduct).resolve_left (pow_ne_zero _ hdenF)
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxB
  have hdiv : c * ρ bW = ρ aW := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul, hc]
    exact div_mul_cancel₀ _ hdenF
  have hrelation : θ c * b = a := by
    have h := congrArg θ hdiv
    rw [map_mul, hrepresent, hrepresent, haW, hbW] at h
    exact h
  refine ⟨θ c, ?_⟩
  rw [← hfrac]
  apply (eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)).mpr
  rw [← map_mul, hrelation]

end EtaleFundamentalGroups.StrictHenselian
