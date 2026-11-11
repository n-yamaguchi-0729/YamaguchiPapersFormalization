/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Shared actual affine étale representatives

These are the affine-refinement and structure-map arguments already
used in the field-fiber integrality proof. They are shared by that proof
and the residue-fiber separability proof.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- A stalk element has a representative on an actual affine pointed
étale neighborhood, with its original germ map retained. -/
theorem geometricStalk_exists_affine_representative
    {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) (a : geometricStalk s) :
    ∃ (V : S.Etale) (v : (Scheme.pointEtaleNeighborhoods s).fiber.obj V),
      IsAffine V.left ∧ ∃ b : Γ(V.left, ⊤), geometricStalkGerm s V v b = a := by
  obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representative s a
  obtain ⟨V, v, j, hVaffine, hj⟩ := geometricStalk_exists_affine_refinement s W t
  refine ⟨V, v, hVaffine, j.left.appTop z, ?_⟩
  have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w j v (etaleSections S)
  rw [hj] at h
  exact (ConcreteCategory.congr_hom h z).trans hz

/-- The literal coefficient map on an affine étale neighborhood is étale. -/
theorem geometricNeighborhood_structureMap_etale
    {R : Type u} [CommRing R] (V : (Spec (CommRingCat.of R)).Etale)
    [IsAffine V.left] :
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom).Etale := by
  change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Etale
  apply RingHom.Etale.stableUnderComposition
  · exact RingHom.Etale.of_bijective
      ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
        inferInstance)
  · exact HasRingHomProperty.appTop (P := @Etale)
      (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) inferInstance

end EtaleFundamentalGroups.StrictHenselian
