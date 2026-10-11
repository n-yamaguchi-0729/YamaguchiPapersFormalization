/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.LocalRing.RingHom.Basic


/-!
# The actual structure map into the geometric étale stalk

For a geometric point of `Spec R` given by a ring map `φ : R →+* Ω`, use the
identity étale neighborhood of `Spec R`. Its germ map, composed with the
canonical identification of the sections of `Spec R` with `R`, constructs the
structure homomorphism into the geometric stalk. Evaluation composed with this
structure homomorphism is exactly `φ`.

If `φ` is local, so is the constructed structure homomorphism. In particular this
applies when `R` is local and `φ` is its residue map followed by an embedding of
its residue field into the chosen separably closed field. Neither flatness of
this structure map nor a comparison with a separately chosen strict
henselization is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω)

/-- The structure map is the actual germ map of the identity étale
neighborhood, precomposed with the sections--ring identification for `Spec R`. -/
def geometricStalkStructureMap :
    R →+* geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ))
      (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of R))))
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) (Category.comp_id _))).hom

/-- The structure map has the specified value at the geometric point. -/
theorem geometricStalkStructureMap_evaluation :
    (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom.comp
      (geometricStalkStructureMap φ) = φ := by
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  let T : (Spec (CommRingCat.of R)).Etale :=
    Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of R)))
  let tT : (Scheme.pointEtaleNeighborhoods s).fiber.obj T :=
    Over.homMk s (Category.comp_id _)
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    geometricStalkGerm s T tT) ≫ geometricStalkEvaluation s).hom = φ
  apply congrArg CommRingCat.Hom.hom
  calc
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ geometricStalkGerm s T tT) ≫
        geometricStalkEvaluation s =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (geometricStalkGerm s T tT ≫ geometricStalkEvaluation s) :=
          Category.assoc _ _ _
    _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ tT.left.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
          exact congrArg
            (fun h : Γ(T.left, ⊤) ⟶ CommRingCat.of Ω =>
              (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h)
            (geometricStalkGerm_evaluation s T tT)
    _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := rfl
    _ = CommRingCat.ofHom φ := by
      change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom φ)).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom φ
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- Pointwise form of the compatibility with the geometric point. -/
theorem geometricStalkStructureMap_evaluation_apply (r : R) :
    geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))
      (geometricStalkStructureMap φ r) = φ r :=
  RingHom.congr_fun (geometricStalkStructureMap_evaluation φ) r

/-- The structure map factors through the sections of every actual pointed
étale neighborhood, compatibly with its germ map. -/
theorem geometricStalkGerm_comp_structure
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t).hom.comp
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom) =
      geometricStalkStructureMap φ := by
  let T : (Spec (CommRingCat.of R)).Etale :=
    Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of R)))
  let tT : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj T :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (Category.comp_id _)
  let f : W ⟶ T := MorphismProperty.Over.homMk W.hom (Category.comp_id _)
  have ht : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom φ))).fiber.map f t = tT := by
    apply Over.OverMorphism.ext
    exact Over.w t
  have h := (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_w
    f t (etaleSections (Spec (CommRingCat.of R)))
  rw [ht] at h
  change W.hom.appTop ≫ geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) T tT at h
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop) ≫
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t).hom = _
  rw [Category.assoc, h]
  rfl

/-- A closed geometric point of a local ring gives a local structure map into
the constructed geometric stalk. -/
instance geometricStalkStructureMap_isLocalHom [IsLocalHom φ] :
    IsLocalHom (geometricStalkStructureMap φ) where
  map_nonunit r hr := by
    have hunit := hr.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom
    rw [geometricStalkStructureMap_evaluation_apply] at hunit
    exact (inferInstance : IsLocalHom φ).map_nonunit r hunit

end EtaleFundamentalGroups.StrictHenselian
