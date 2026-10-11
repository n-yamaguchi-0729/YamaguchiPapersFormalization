/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The actual geometric stalk has a separable residue extension

Every residue element is represented by an actual affine pointed étale
neighborhood. Its selected prime localization has a finite separable residue
extension. The existing local germ map sends that residue element to the
original stalk residue, so its separability follows through the actual local
maps. No separability of the entire chosen geometric overfield is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The actual local structure map to the geometric stalk induces a separable
extension of residue fields, even when the chosen geometric field contains
inseparable elements over the base residue field. -/
theorem geometricStalk_residue_isSeparable
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω]
    (φ : R →+* Ω) [IsLocalHom φ] :
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap R (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
  intro actualStructureAlgebra actualStructureLocal
  let s := Spec.map (CommRingCat.ofHom φ)
  let H := geometricStalk s
  constructor
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := H) x
  obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representative s a
  obtain ⟨V, v, g, hVaffine, hg⟩ := geometricStalk_exists_affine_refinement s W t
  have : IsAffine V.left := hVaffine
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
  let δ : B →+* H := geometricStalkLocalizedGerm s V v
  let : Algebra B H := δ.toAlgebra
  have : IsLocalHom (algebraMap B H) := by
    change IsLocalHom (geometricStalkLocalizedGerm s V v)
    infer_instance
  have hcoeff : δ.comp (algebraMap R B) = geometricStalkStructureMap φ := by
    rw [IsScalarTower.algebraMap_eq R Γ(V.left, ⊤) B, ← RingHom.comp_assoc]
    exact (congrArg (fun f : Γ(V.left, ⊤) →+* H => f.comp β)
      (geometricStalkLocalizedGerm_comp s V v)).trans
        (geometricStalkGerm_comp_structure φ V v)
  have : IsScalarTower R B H := IsScalarTower.of_algebraMap_eq' hcoeff.symm
  have : IsLocalHom (δ.comp (algebraMap R B)) := by
    rw [hcoeff]
    infer_instance
  have : IsLocalHom (algebraMap R B) := isLocalHom_of_comp (algebraMap R B) δ
  have : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R Γ(V.left, ⊤) B
  have : Algebra.FormallyUnramified R B :=
    Algebra.FormallyUnramified.comp R Γ(V.left, ⊤) B
  have : Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    inferInstance
  let residueMap : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField H :=
    IsScalarTower.toAlgHom (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField H)
  let b : B := algebraMap Γ(V.left, ⊤) B (g.left.appTop z)
  have hrepresent : δ b = a := by
    change geometricStalkLocalizedGerm s V v
      (algebraMap Γ(V.left, ⊤) B (g.left.appTop z)) = a
    rw [geometricStalkLocalizedGerm_apply]
    have hgerm : g.left.appTop ≫ geometricStalkGerm s V v = geometricStalkGerm s W t := by
      have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
        g v (etaleSections (Spec (CommRingCat.of R)))
      rw [hg] at h
      exact h
    exact (ConcreteCategory.congr_hom hgerm z).trans hz
  have hresidue : residueMap (IsLocalRing.residue B b) = IsLocalRing.residue H a := by
    change IsLocalRing.residue H (δ b) = IsLocalRing.residue H a
    exact congrArg (IsLocalRing.residue H) hrepresent
  have hsep : IsSeparable (IsLocalRing.ResidueField R)
      (residueMap (IsLocalRing.residue B b)) :=
    (Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.residue B b)).map residueMap residueMap.injective
  exact hresidue ▸ hsep

end EtaleFundamentalGroups.StrictHenselian
