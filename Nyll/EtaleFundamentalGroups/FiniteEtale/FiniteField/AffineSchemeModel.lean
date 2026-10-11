/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.Model
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Affine Scheme Model

A finite étale cover of the literal constant extension of an affine scheme
descends to an actual finite intermediate field, with its literal inclusion map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleHasPullbacksAlongAffineModel
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongAffineModel
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

private def affineCoefficientIso
    (k E R : Type u) [Field k] [Field E] [CommRing R]
    [Algebra k E] [Algebra k R]
    (U : Scheme.{u}) (f : U ⟶ Spec (CommRingCat.of k))
    (e : U ≅ Spec (CommRingCat.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f) :
    Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f ≅
      Spec (CommRingCat.of (R ⊗[k] E)) :=
  asIso (Limits.pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id])
      (by rw [Category.comp_id]; exact he.symm)) ≪≫
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso k R E

@[reassoc]
private theorem affineCoefficientIso_inv_fst
    (k E R : Type u) [Field k] [Field E] [CommRing R]
    [Algebra k E] [Algebra k R]
    (U : Scheme.{u}) (f : U ⟶ Spec (CommRingCat.of k))
    (e : U ≅ Spec (CommRingCat.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f) :
    (affineCoefficientIso k E R U f e he).inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : E →ₐ[k] R ⊗[k] E).toRingHom) := by
  rw [Iso.inv_comp_eq]
  dsimp only [affineCoefficientIso, Iso.trans_hom]
  simp only [Category.assoc, AlgHom.toRingHom_eq_coe, pullbackSpecIso_hom_snd,
    pullbackSymmetry_hom_comp_snd, asIso_hom, Limits.pullback.map,
    Limits.pullback.lift_fst, Category.comp_id]

@[reassoc]
private theorem affineCoefficientIso_inv_snd
    (k E R : Type u) [Field k] [Field E] [CommRing R]
    [Algebra k E] [Algebra k R]
    (U : Scheme.{u}) (f : U ⟶ Spec (CommRingCat.of k))
    (e : U ≅ Spec (CommRingCat.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f) :
    (affineCoefficientIso k E R U f e he).inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] E))) ≫ e.inv := by
  rw [Iso.inv_comp_eq]
  dsimp only [affineCoefficientIso, Iso.trans_hom]
  simp only [Category.assoc, pullbackSpecIso_hom_fst'_assoc,
    pullbackSymmetry_hom_comp_fst_assoc, asIso_hom, Limits.pullback.map,
    Limits.pullback.lift_snd_assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem affine_structure_factorization
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U]
    (f : U ⟶ Spec (CommRingCat.of k)) :
    let _ : Algebra k Γ(U, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(U, ⊤))) = f := by
  intro
  change U.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, Scheme.isoSpec_hom_naturality_assoc,
    ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]

private theorem affineCoefficientIso_naturality
    (k L R : Type u) [Field k] [Field L] [CommRing R]
    [Algebra k L] [Algebra k R] (F : IntermediateField k L)
    (U : Scheme.{u}) (f : U ⟶ Spec (CommRingCat.of k))
    (e : U ≅ Spec (CommRingCat.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f) :
    Limits.pullback.map
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
        (Spec.map (CommRingCat.ofHom (algebraMap k F))) f
        (Spec.map (CommRingCat.ofHom F.val.toRingHom)) (𝟙 U) (𝟙 _)
        (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
        (by rw [Category.comp_id, Category.id_comp]) ≫
      (affineCoefficientIso k F R U f e he).hom =
    (affineCoefficientIso k L R U f e he).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).toRingHom) := by
  let p := Limits.pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
    (Spec.map (CommRingCat.ofHom (algebraMap k F))) f
    (Spec.map (CommRingCat.ofHom F.val.toRingHom)) (𝟙 U) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  let t := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).toRingHom)
  have hnat : (affineCoefficientIso k L R U f e he).inv ≫ p =
      t ≫ (affineCoefficientIso k F R U f e he).inv := by
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, p, Limits.pullback.map, Limits.pullback.lift_fst,
        affineCoefficientIso_inv_fst_assoc, affineCoefficientIso_inv_fst]
      dsimp only [t]
      rw [← Spec.map_comp, ← Spec.map_comp]
      apply congrArg (fun g : CommRingCat.of F ⟶ CommRingCat.of (R ⊗[k] L) => Spec.map g)
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change (1 : R) ⊗ₜ[k] F.val x =
        Algebra.TensorProduct.map (AlgHom.id R R) F.val ((1 : R) ⊗ₜ[k] x)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    · simp only [Category.assoc, p, Limits.pullback.map, Limits.pullback.lift_snd,
        Category.comp_id, affineCoefficientIso_inv_snd]
      dsimp only [t]
      rw [← Spec.map_comp_assoc]
      congr 2
  change p ≫ (affineCoefficientIso k F R U f e he).hom =
    (affineCoefficientIso k L R U f e he).hom ≫ t
  rw [← Iso.inv_comp_eq]
  rw [← Category.assoc, hnat, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A finite étale cover of the literal constant extension of an affine scheme
descends to an actual finite intermediate field, with its literal inclusion map. -/
theorem exists_finiteIntermediateField_affine_scheme_model
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (U : Scheme.{u}) [IsAffine U] (f : U ⟶ Spec (CommRingCat.of k))
    (X : FiniteEtale (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      ∃ X₀ : FiniteEtale (Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k F))) f),
        Nonempty ((FiniteEtale.pullback (Limits.pullback.map
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
          (Spec.map (CommRingCat.ofHom (algebraMap k F))) f
          (Spec.map (CommRingCat.ofHom F.val.toRingHom)) (𝟙 U) (𝟙 _)
          (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
          (by rw [Category.comp_id, Category.id_comp]))).obj X₀ ≅ X) := by
  let R := Γ(U, ⊤)
  let : Algebra k R := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have he : U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f :=
    affine_structure_factorization k U f
  let eL := affineCoefficientIso k L R U f U.isoSpec he
  let XT : FiniteEtale (Spec (CommRingCat.of (R ⊗[k] L))) :=
    (FiniteEtale.pullback eL.inv).obj X
  obtain ⟨F, hF, X₀, ⟨e₀⟩⟩ :=
    exists_finiteIntermediateField_affine_model k L R XT
  let eF := affineCoefficientIso k F R U f U.isoSpec he
  let p := Limits.pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
    (Spec.map (CommRingCat.ofHom (algebraMap k F))) f
    (Spec.map (CommRingCat.ofHom F.val.toRingHom)) (𝟙 U) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  let t := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).toRingHom)
  have hpt : p ≫ eF.hom = eL.hom ≫ t :=
    affineCoefficientIso_naturality k L R F U f U.isoSpec he
  let c₁ : FiniteEtale.pullback (p ≫ eF.hom) ≅
      FiniteEtale.pullback eF.hom ⋙ FiniteEtale.pullback p :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) p eF.hom
  let c₂ : FiniteEtale.pullback (p ≫ eF.hom) ≅
      FiniteEtale.pullback (eL.hom ≫ t) :=
    MorphismProperty.Over.pullbackCongr (P := @IsFiniteEtale) (Q := ⊤) hpt
  let c₃ : FiniteEtale.pullback (eL.hom ≫ t) ≅
      FiniteEtale.pullback t ⋙ FiniteEtale.pullback eL.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) eL.hom t
  let E : FiniteEtale (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) ≌
      FiniteEtale (Spec (CommRingCat.of (R ⊗[k] L))) :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ eL
  refine ⟨F, hF, (FiniteEtale.pullback eF.hom).obj X₀, ⟨?_⟩⟩
  exact (c₁.app X₀).symm ≪≫ c₂.app X₀ ≪≫ c₃.app X₀ ≪≫
    (FiniteEtale.pullback eL.hom).mapIso e₀ ≪≫ (E.unitIso.app X).symm

end AlgebraicGeometry.FiniteEtale
