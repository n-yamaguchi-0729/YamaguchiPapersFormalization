/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.StrictGenericTrivialCover
import EtaleFundamentalGroups.Normalization.GenericFiber
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import EtaleFundamentalGroups.Inertia.AffineNormalizationAction
import SchemeTheory.Normalization.AffineFiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic


/-!
# Etaleness of an actual normalization from strict generic triviality

The finite cover is replaced by its actual affine coordinate algebra, with
both scalar structures supplied by its morphisms. All isomorphisms of covers
and relative normalizations are constructed from the canonical affine map.
No connectedness or Galois hypothesis on the finite cover is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem affineMorphismAlgebra_tower
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of K)) :
    let : Algebra K Γ(Y, ⊤) := affineMorphismAlgebra K h
    let : Algebra R Γ(Y, ⊤) := affineMorphismAlgebra R
      (h ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
    IsScalarTower R K Γ(Y, ⊤) := by
  intro fieldAction baseAction
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change h.appTop ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop
    ((Scheme.ΓSpecIso (.of R)).inv a)) =
      h.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap R K a))
  exact congrArg h.appTop
    (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K))) a).symm

private theorem moduleFinite_affineMorphismAlgebra
    (K : Type u) [CommRing K] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of K)) [IsFinite h] :
    let : Algebra K Γ(Y, ⊤) := affineMorphismAlgebra K h
    Module.Finite K Γ(Y, ⊤) := by
  intro sectionAction
  apply RingHom.finite_algebraMap.mp
  change (h.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).Finite
  exact h.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).surjective)

/-- Transfer actual affine integral-closure étaleness to the literal
relative normalization, using the existing source and normalization isomorphisms. -/
private theorem etale_normalization_of_affineMorphism_integralClosure
    (R : Type u) [CommRing R] {Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ Spec (.of R)) :
    let : Algebra R Γ(Y, ⊤) := affineMorphismAlgebra R f
    Algebra.Etale R (integralClosure R Γ(Y, ⊤)) → Etale f.fromNormalization := by
  intro sectionAction hEt
  let n := Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, ⊤)))
  let eN : f.normalization ≅ n.normalization := affineMorphismNormalizationIso R f
  have heN : eN.hom ≫ n.fromNormalization = f.fromNormalization :=
    normalizationSourceIso_hom_fromNormalization f n Y.isoSpec
      (isoSpec_affineMorphismAlgebra R f)
  let eB := specNormalizationIso R Γ(Y, ⊤)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Γ(Y, ⊤))))
  have : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr hEt)
  have hcomp : Etale (eN.hom ≫ eB.hom ≫ g) := inferInstance
  have he : eN.hom ≫ eB.hom ≫ g = f.fromNormalization :=
    (congrArg (fun q => eN.hom ≫ q)
      (specNormalizationIso_hom_fromNormalization R Γ(Y, ⊤))).trans heN
  exact he ▸ hcomp

/-- A finite etale cover of a normal local domain's fraction field whose entire
fiber is fixed by the actual strict generic image has etale relative normalization. -/
theorem etale_fractionCover_normalization_of_strictGeneric_image_fixed
    {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (V : FiniteEtale (Spec (.of (FractionRing R))))
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))))
    (hfixed : ∀ (g : Aut (fiber point))
      (w : (fiber (point ≫ Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))).obj V),
      fundamentalGroupHom (Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))
        point g • w = w) :
    Etale ((show V.left ⟶ Spec (.of (FractionRing R)) from V.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).fromNormalization := by
  let K := FractionRing R
  let h : V.left ⟶ Spec (.of K) := V.hom
  have : IsFiniteEtale h := V.2
  have : IsAffine V.left := isAffine_of_isAffineHom h
  let B := Γ(V.left, ⊤)
  let r := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f : V.left ⟶ Spec (.of R) := h ≫ r
  let : Algebra K B := affineMorphismAlgebra K h
  let : Algebra R B := affineMorphismAlgebra R f
  have : IsScalarTower R K B := affineMorphismAlgebra_tower R K h
  have : Module.Finite K B := moduleFinite_affineMorphismAlgebra K h
  have : Algebra.Etale K B := by
    apply RingHom.etale_algebraMap.mp
    change (h.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).Etale
    apply RingHom.Etale.stableUnderComposition
    · exact RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)
    · exact HasRingHomProperty.appTop (P := @Etale) h inferInstance
  have : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap K B))) :=
    IsFiniteEtale.SpecMap_iff.mpr (RingHom.finiteEtale_algebraMap_iff.mpr ⟨⟩)
  let W : FiniteEtale (Spec (.of K)) := mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))
  let E : V ≅ W := MorphismProperty.Over.isoMk V.left.isoSpec
    (isoSpec_affineMorphismAlgebra K h)
  have hEt : Algebra.Etale R (integralClosure R B) := by
    apply integralClosure_etale_of_strictGeneric_image_fixed φ B point
    intro g w
    let F := fiber (point ≫ Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))
    apply (ConcreteCategory.bijective_of_isIso (F.map E.inv)).injective
    exact (CategoryTheory.PreGaloisCategory.mulAction_naturality F
      (fundamentalGroupHom (Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))
        point g) E.inv w).symm.trans (hfixed g (F.map E.inv w))
  exact etale_normalization_of_affineMorphism_integralClosure R f hEt

/-- The actual normalization of an arbitrary finite étale fraction-field
cover recovers that cover on the generic fiber, with the original maps. -/
theorem isPullback_fractionCover_normalization
    (R : Type u) [CommRing R] [IsDomain R]
    (V : FiniteEtale (Spec (.of (FractionRing R)))) :
    IsPullback
      ((show V.left ⟶ Spec (.of (FractionRing R)) from V.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).toNormalization
      (show V.left ⟶ Spec (.of (FractionRing R)) from V.hom)
      ((show V.left ⟶ Spec (.of (FractionRing R)) from V.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).fromNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) := by
  let K := FractionRing R
  let h : V.left ⟶ Spec (.of K) := V.hom
  have : IsFiniteEtale h := V.2
  have : IsAffine V.left := isAffine_of_isAffineHom h
  let B := Γ(V.left, ⊤)
  let r := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f : V.left ⟶ Spec (.of R) := h ≫ r
  let : Algebra K B := affineMorphismAlgebra K h
  let : Algebra R B := affineMorphismAlgebra R f
  have : IsScalarTower R K B := affineMorphismAlgebra_tower R K h
  have : Module.Finite K B := moduleFinite_affineMorphismAlgebra K h
  let n : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let E : f.normalization ≅ n.normalization := affineMorphismNormalizationIso R f
  have htop : f.toNormalization ≫ E.hom = V.left.isoSpec.hom ≫ n.toNormalization :=
    toNormalization_normalizationSourceIso_hom f n V.left.isoSpec
      (isoSpec_affineMorphismAlgebra R f)
  have hbase : E.hom ≫ n.fromNormalization = f.fromNormalization :=
    normalizationSourceIso_hom_fromNormalization f n V.left.isoSpec
      (isoSpec_affineMorphismAlgebra R f)
  have H : IsPullback n.toNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) n.fromNormalization r :=
    isPullback_affineNormalization_generic R K B
  exact H.of_iso' V.left.isoSpec E (Iso.refl _) (Iso.refl _)
    htop.symm
    ((isoSpec_affineMorphismAlgebra K h).trans (Category.comp_id h).symm)
    (hbase.trans (Category.comp_id f.fromNormalization).symm)
    (by simp only [r, K, Iso.refl_hom, Category.id_comp, Category.comp_id])

/-- A cover fixed by the actual strict generic image extends by its actual
finite étale normalization. The witness in the essential image is that
normalization, recovered by the literal generic pullback square. -/
theorem fractionCover_normalization_finiteEtale_and_essImage_of_strictGeneric_image_fixed
    {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (V : FiniteEtale (Spec (.of (FractionRing R))))
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))))
    (hfixed : ∀ (g : Aut (fiber point))
      (w : (fiber (point ≫ Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))).obj V),
      fundamentalGroupHom (Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))
        point g • w = w) :
    IsFiniteEtale ((show V.left ⟶ Spec (.of (FractionRing R)) from V.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).fromNormalization ∧
      (FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).essImage V := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let f : V.left ⟶ Spec (.of R) := V.hom ≫ r
  have : Etale f.fromNormalization :=
    etale_fractionCover_normalization_of_strictGeneric_image_fixed φ V point hfixed
  have : IsFinite f.fromNormalization :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f.fromNormalization).mpr
      ⟨inferInstance, inferInstance⟩
  have hfinite : IsFiniteEtale f.fromNormalization := ⟨⟩
  refine ⟨hfinite, ?_⟩
  let Z : FiniteEtale (Spec (.of R)) := mk f.fromNormalization
  have H : IsPullback f.toNormalization
      (show V.left ⟶ Spec (.of (FractionRing R)) from V.hom) f.fromNormalization r :=
    isPullback_fractionCover_normalization R V
  let E : V ≅ (FiniteEtale.pullback r).obj Z :=
    MorphismProperty.Over.isoMk H.isoPullback H.isoPullback_hom_snd
  exact ⟨Z, ⟨E.symm⟩⟩

end EtaleFundamentalGroups.StrictHenselian
