/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.Affine
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Affine relative normalization and arbitrary localization

Let `Rm` be the localization of `R` at `M`, and let `Bm` be the localization
of an `R`-algebra `B` at the image of `M`.  The actual map between integral
closures is constructed by mapping integral elements and extending scalars.
Mathlib's localization theorem for integral closures makes the resulting
square a pushout of rings.  Its spectrum is therefore a pullback of schemes.

Using the canonical affine normalization isomorphisms, this gives an actual
isomorphism between the relative normalization of `Spec Bm → Spec Rm` and
the pullback of the relative normalization of `Spec B → Spec R`.  The argument
allows arbitrary multiplicative sets, including the complement of a prime.
It requires no domain, normality, finite-type, or smoothness assumptions.
This file treats the affine comparison; it does not claim that the canonical
map from a scheme's stalk spectrum is smooth.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The canonical affine normalization isomorphism also intertwines the maps
to the base.  This follows from the actual integral-closure inclusion. -/
@[reassoc]
theorem specNormalizationIso_hom_structureMap
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    (specNormalizationIso R B).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R B))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization := by
  apply spec_toNormalization_hom_ext R B
  rw [← Category.assoc, toNormalization_specNormalizationIso_hom,
    ← Spec.map_comp, Scheme.Hom.toNormalization_fromNormalization]
  rfl

variable (R B Rm Bm : Type u)
variable [CommRing R] [CommRing B] [CommRing Rm] [CommRing Bm]
variable [Algebra R B] [Algebra R Rm] [Algebra B Bm]
variable [Algebra Rm Bm] [Algebra R Bm]
variable [IsScalarTower R B Bm] [IsScalarTower R Rm Bm]

/-- The literal integral-closure map in a localization square.  Its definition
already makes sense for every compatible square of algebra maps. -/
def integralClosureLocalizationMap :
    integralClosure R B →ₐ[R] integralClosure Rm Bm where
  toFun b := ⟨algebraMap B Bm (b : B),
    (b.property.map (IsScalarTower.toAlgHom R B Bm)).tower_top⟩
  map_one' := Subtype.ext (map_one (algebraMap B Bm))
  map_mul' b c := Subtype.ext (map_mul (algebraMap B Bm) (b : B) (c : B))
  map_zero' := Subtype.ext (map_zero (algebraMap B Bm))
  map_add' b c := Subtype.ext (map_add (algebraMap B Bm) (b : B) (c : B))
  commutes' r := by
    apply Subtype.ext
    change algebraMap B Bm (algebraMap R B r) = algebraMap R Bm r
    exact (IsScalarTower.algebraMap_apply R B Bm r).symm

variable (M : Submonoid R)
variable [IsLocalization M Rm]
variable [IsLocalization (Algebra.algebraMapSubmonoid B M) Bm]

include M
/-- Integral closure gives a literal pushout square after localizing the base.
The algebra structure on the target closure is constructed from the displayed
map, and its scalar-tower laws are proved from that map. -/
theorem integralClosureLocalization_isPushout :
    IsPushout
      (CommRingCat.ofHom (algebraMap R (integralClosure R B)))
      (CommRingCat.ofHom (algebraMap R Rm))
      (CommRingCat.ofHom (integralClosureLocalizationMap R B Rm Bm).toRingHom)
      (CommRingCat.ofHom (algebraMap Rm (integralClosure Rm Bm))) := by
  let C := integralClosure R B
  let Cm := integralClosure Rm Bm
  let ι : C →ₐ[R] Cm := integralClosureLocalizationMap R B Rm Bm
  let : Algebra C Cm := ι.toRingHom.toAlgebra
  let : IsScalarTower R C Cm :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ι.commutes r).symm
  let : IsScalarTower C Cm Bm :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid C M) Cm :=
    IsLocalization.integralClosure (S := B) (Rf := Rm) (Sf := Bm) M
  let : Algebra.IsPushout R C Rm Cm :=
    Algebra.isPushout_of_isLocalization M Rm C Cm
  exact CommRingCat.isPushout_of_isPushout R C Rm Cm
omit M

/-- The canonical map from the normalization after localization to the
original normalization, expressed through the actual integral-closure map. -/
def affineNormalizationLocalizationMap :
    (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).normalization ⟶
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization :=
  (specNormalizationIso Rm Bm).hom ≫
    Spec.map (CommRingCat.ofHom (integralClosureLocalizationMap R B Rm Bm).toRingHom) ≫
      (specNormalizationIso R B).inv

/-- The comparison is the canonical extension of the original localization
map, as witnessed by its composite with the normalization maps. -/
@[reassoc]
theorem toNormalization_affineNormalizationLocalizationMap :
    (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).toNormalization ≫
        affineNormalizationLocalizationMap R B Rm Bm =
      Spec.map (CommRingCat.ofHom (algebraMap B Bm)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization := by
  apply (cancel_mono (specNormalizationIso R B).hom).mp
  simp only [affineNormalizationLocalizationMap, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    toNormalization_specNormalizationIso_hom_assoc,
    toNormalization_specNormalizationIso_hom]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

include M
/-- The relative-normalization square associated with an arbitrary localization
of affine schemes is cartesian.  All arrows are the actual structure maps or
the map constructed from the integral closures. -/
theorem affineNormalizationLocalization_isPullback :
    IsPullback
      (affineNormalizationLocalizationMap R B Rm Bm)
      (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).fromNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) := by
  have h := isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (algebraMap R (integralClosure R B)))
    (CommRingCat.ofHom (algebraMap R Rm))
    (CommRingCat.ofHom (integralClosureLocalizationMap R B Rm Bm).toRingHom)
    (CommRingCat.ofHom (algebraMap Rm (integralClosure Rm Bm)))
    (integralClosureLocalization_isPushout R B Rm Bm M)
  refine h.of_iso' (specNormalizationIso Rm Bm) (specNormalizationIso R B)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [affineNormalizationLocalizationMap, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, specNormalizationIso_hom_structureMap]
  · simp only [Iso.refl_hom, Category.comp_id, specNormalizationIso_hom_structureMap]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
omit M

include M
/-- Normalization after localization is canonically isomorphic to the actual
pullback of the original normalization.  This applies in particular to
localization at a prime ideal. -/
def affineNormalizationLocalizationIso :
    (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).normalization ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization
        (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) :=
  (affineNormalizationLocalization_isPullback R B Rm Bm M).isoPullback

@[reassoc]
theorem affineNormalizationLocalizationIso_hom_fst :
    (affineNormalizationLocalizationIso R B Rm Bm M).hom ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization
          (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) =
      affineNormalizationLocalizationMap R B Rm Bm :=
  (affineNormalizationLocalization_isPullback R B Rm Bm M).isoPullback_hom_fst

@[reassoc]
theorem affineNormalizationLocalizationIso_hom_snd :
    (affineNormalizationLocalizationIso R B Rm Bm M).hom ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization
          (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) =
      (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).fromNormalization :=
  (affineNormalizationLocalization_isPullback R B Rm Bm M).isoPullback_hom_snd

end EtaleFundamentalGroups.Inertia
