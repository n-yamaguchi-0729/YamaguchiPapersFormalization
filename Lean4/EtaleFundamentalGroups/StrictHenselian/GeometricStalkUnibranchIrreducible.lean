/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import SchemeTheory.RingTheory.Descent.EtaleLocalIrreducibilityOfIntegralNormalExtension
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.RingHom.Etale


/-!
# Irreducibility of the actual geometric stalk from normalization data

The base local ring need not be reduced. An integral local map to a normal
local domain with purely inseparable residue field and nilpotent kernel
elements gives irreducible local étale neighborhoods. A nilpotence relation
between actual stalk germs descends to one of these neighborhoods.

For a geometrically unibranch local ring, the normalization of its reduction
supplies the extension used here. All comparison maps and the
étale neighborhoods are actual constructions, not assumed conclusions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsLocalRing R]
  [Field Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- The nilradical of the actual geometric stalk is prime when the base maps
integrally and locally to a normal local domain with purely inseparable residue
field and a kernel consisting of nilpotents. -/
theorem geometricStalk_nilradical_isPrime_of_integral_normal_extension
    (N : Type u) [CommRing N] [IsLocalRing N] [IsDomain N] [IsIntegrallyClosed N]
    [Algebra R N] [Algebra.IsIntegral R N] [IsLocalHom (algebraMap R N)]
    [IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField N)]
    (hker : RingHom.ker (algebraMap R N) ≤ nilradical R) :
    (nilradical (geometricStalk (Spec.map (CommRingCat.ofHom φ)))).IsPrime := by
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  constructor
  · intro htop
    have hmem : (1 : geometricStalk s) ∈ nilradical (geometricStalk s) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ := mem_nilradical.mp hmem
    rw [one_pow] at hn
    exact one_ne_zero hn
  · intro a b hab
    obtain ⟨n, hn⟩ := mem_nilradical.mp hab
    obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representatives s ![a, b]
    have hza : geometricStalkGerm s W t (z 0) = a := hz 0
    have hzb : geometricStalkGerm s W t (z 1) = b := hz 1
    have hzero : geometricStalkGerm s W t ((z 0 * z 1) ^ n) =
        geometricStalkGerm s W t 0 := by
      rw [map_pow, map_mul, map_zero, hza, hzb]
      exact hn
    obtain ⟨W₁, f, t₁, hf, hzero₁⟩ :=
      ((Scheme.pointEtaleNeighborhoods s).toPresheafFiber_eq_iff'
        (P := etaleSections (Spec (CommRingCat.of R))) W t ((z 0 * z 1) ^ n) 0).mp hzero
    change f.left.appTop ((z 0 * z 1) ^ n) = f.left.appTop 0 at hzero₁
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
    have hzeroV : (δ (z 0) * δ (z 1)) ^ n = 0 := by
      rw [← map_mul, ← map_pow]
      change (g.left ≫ f.left).appTop ((z 0 * z 1) ^ n) = 0
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
    let δB : B →+* geometricStalk s := geometricStalkLocalizedGerm s V v
    have hcoeff : δB.comp (algebraMap R B) = geometricStalkStructureMap φ := by
      rw [IsScalarTower.algebraMap_eq R Γ(V.left, ⊤) B, ← RingHom.comp_assoc]
      exact (congrArg (fun f : Γ(V.left, ⊤) →+* geometricStalk s => f.comp β)
        (geometricStalkLocalizedGerm_comp s V v)).trans
          (geometricStalkGerm_comp_structure φ V v)
    have : IsLocalHom (δB.comp (algebraMap R B)) := by
      rw [hcoeff]
      infer_instance
    have : IsLocalHom (algebraMap R B) := isLocalHom_of_comp (algebraMap R B) δB
    have : (nilradical B).IsPrime :=
      SchemeTheory.nilradical_isPrime_atPrime_of_etale_of_integral_normal_extension
        R N Γ(V.left, ⊤) hker (geometricNeighborhoodPrime s V v).asIdeal
    have hzeroB : (algebraMap Γ(V.left, ⊤) B (δ (z 0)) *
        algebraMap Γ(V.left, ⊤) B (δ (z 1))) ^ n = 0 := by
      rw [← map_mul, ← map_pow, hzeroV, map_zero]
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
    have hprod : algebraMap Γ(V.left, ⊤) B (δ (z 0)) *
        algebraMap Γ(V.left, ⊤) B (δ (z 1)) ∈ nilradical B :=
      mem_nilradical.mpr ⟨n, hzeroB⟩
    rcases (inferInstance : (nilradical B).IsPrime).mem_or_mem hprod with ha | hb
    · left
      have hnil := (mem_nilradical.mp ha).map (geometricStalkLocalizedGerm s V v)
      rw [hrepresent 0, hza] at hnil
      exact mem_nilradical.mpr hnil
    · right
      have hnil := (mem_nilradical.mp hb).map (geometricStalkLocalizedGerm s V v)
      rw [hrepresent 1, hzb] at hnil
      exact mem_nilradical.mpr hnil

end EtaleFundamentalGroups.StrictHenselian
