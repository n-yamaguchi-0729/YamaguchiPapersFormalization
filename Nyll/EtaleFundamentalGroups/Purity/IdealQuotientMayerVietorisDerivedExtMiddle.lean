/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisDerivedExtSupports
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-!
# The middle term of the derived Mayer--Vietoris sequence

The middle object in the ideal-quotient Mayer--Vietoris sequence is a
Cartesian product of quotient modules.  This file identifies its derived-Ext
diagram with the pointwise biproduct of the two ideal-power diagrams.  Since
filtered colimits in abelian groups are additive, the middle colimit is the
biproduct of the two derived local-cohomology objects.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u v w

/-- The explicit pointwise binary biproduct of two diagrams. -/
def pointwiseBiprodFunctor
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {D : Type w} [Category D]
    (A B : D ⥤ C) : D ⥤ C where
  obj d := A.obj d ⊞ B.obj d
  map f := biprod.map (A.map f) (B.map f)
  map_id d := by ext <;> simp
  map_comp f g := by ext <;> simp

/-- Taking opposites carries a pointwise biproduct diagram to the pointwise
biproduct of the opposite diagrams. -/
def diagramOpBiprodIso
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {D : Type w} [Category D]
    (A B : D ⥤ C) :
    (pointwiseBiprodFunctor A B).op ≅
      pointwiseBiprodFunctor A.op B.op :=
  NatIso.ofComponents
    (fun d => biprod.opIso (A.obj (unop d)) (B.obj (unop d)))
    (by
      intro d e f
      change
        (biprod.map (A.map f.unop) (B.map f.unop)).op ≫
            (biprod.opIso (A.obj (unop e)) (B.obj (unop e))).hom =
          (biprod.opIso (A.obj (unop d)) (B.obj (unop d))).hom ≫
            biprod.map (A.map f.unop).op (B.map f.unop).op
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.opIso_hom_fst, biprod.map_fst]
        rw [← op_comp, biprod.inl_map, op_comp]
        rw [← Category.assoc, biprod.opIso_hom_fst]
      · simp only [Category.assoc, biprod.opIso_hom_snd, biprod.map_snd]
        rw [← op_comp, biprod.inr_map, op_comp]
        rw [← Category.assoc, biprod.opIso_hom_snd])

/-- An additive functor carries an explicit pointwise biproduct diagram to
the corresponding pointwise biproduct of the composite diagrams. -/
def additiveFunctorCompBiprodIso
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {E : Type w} [Category E] [Preadditive E]
    [HasBinaryBiproducts E]
    {D : Type*} [Category D]
    (A B : D ⥤ C) (F : C ⥤ E) [F.Additive] :
    pointwiseBiprodFunctor A B ⋙ F ≅
      pointwiseBiprodFunctor (A ⋙ F) (B ⋙ F) := by
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact NatIso.ofComponents
    (fun d => F.mapBiprod (A.obj d) (B.obj d))
    (by
      intro d e f
      change
        F.map (biprod.map (A.map f) (B.map f)) ≫
            (F.mapBiprod (A.obj e) (B.obj e)).hom =
          (F.mapBiprod (A.obj d) (B.obj d)).hom ≫
            biprod.map (F.map (A.map f)) (F.map (B.map f))
      apply biprod.hom_ext
      · simp only [Category.assoc, Functor.mapBiprod_hom,
          biprod.lift_fst, biprod.lift_fst_assoc,
          biprod.map_fst, ← F.map_comp]
      · simp only [Category.assoc, Functor.mapBiprod_hom,
          biprod.lift_snd, biprod.lift_snd_assoc,
          biprod.map_snd, ← F.map_comp])

/-- The explicit pointwise biproduct diagram is canonically isomorphic to the
chosen binary biproduct in the functor category. -/
def pointwiseBiprodFunctorIso
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {D : Type w} [Category D]
    (A B : D ⥤ C) :
    pointwiseBiprodFunctor A B ≅ A ⊞ B := by
  change (pointwiseBinaryBicone A B).pt ≅ A ⊞ B
  exact IsLimit.conePointUniqueUpToIso
    (pointwiseBinaryBicone.isBilimit A B).isLimit
    (BinaryBiproduct.isLimit A B)

/-- Colimits carry explicit pointwise binary biproducts to binary
biproducts. -/
def pointwiseBiprodColimitIso
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {D : Type w} [Category D] [HasColimitsOfShape D C]
    (A B : D ⥤ C) :
    colimit (pointwiseBiprodFunctor A B) ≅
      colimit A ⊞ colimit B := by
  letI : PreservesBinaryBiproducts (colim (J := D) (C := C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact HasColimit.isoOfNatIso (pointwiseBiprodFunctorIso A B) ≪≫
    (colim (J := D) (C := C)).mapBiprod A B

variable {R : Type u} [CommRing R]

/-- Derived Ext in its contravariant variable is additive. -/
instance derivedExtContravariantFunctor_additive
    (M : ModuleCat.{u} R) (n : ℕ) :
    (derivedExtContravariantFunctor M n).Additive := by
  unfold derivedExtContravariantFunctor
  infer_instance

/-- The middle quotient-product term of the powers Mayer--Vietoris
diagram. -/
def idealQuotientMayerVietorisProductPowersDiagram (I J : Ideal R) :
    ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  idealQuotientMayerVietorisPowersDiagram I J ⋙ ShortComplex.π₂

/-- The pointwise biproduct of the two quotient-module powers diagrams. -/
def idealQuotientPowersBiprodDiagram (I J : Ideal R) :
    ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  pointwiseBiprodFunctor
    (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I))
    (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J))

/-- The quotient-product diagram is the pointwise biproduct of its two
coordinate quotient diagrams. -/
def idealQuotientMayerVietorisProductPowersIso (I J : Ideal R) :
    idealQuotientMayerVietorisProductPowersDiagram I J ≅
      idealQuotientPowersBiprodDiagram I J :=
  NatIso.ofComponents
    (fun n => by
      change ModuleCat.of R
          ((R ⧸ I ^ unop n) × (R ⧸ J ^ unop n)) ≅
        ModuleCat.of R (R ⧸ I ^ unop n) ⊞
          ModuleCat.of R (R ⧸ J ^ unop n)
      exact (ModuleCat.biprodIsoProd
        (ModuleCat.of R (R ⧸ I ^ unop n))
        (ModuleCat.of R (R ⧸ J ^ unop n))).symm)
    (by
      intro m n f
      change
        ModuleCat.ofHom
              (idealQuotientMayerVietorisProductMap
                (Ideal.pow_le_pow_right f.unop.down.down)
                (Ideal.pow_le_pow_right f.unop.down.down)) ≫
            (ModuleCat.biprodIsoProd
              (ModuleCat.of R (R ⧸ I ^ unop n))
              (ModuleCat.of R (R ⧸ J ^ unop n))).inv =
          (ModuleCat.biprodIsoProd
              (ModuleCat.of R (R ⧸ I ^ unop m))
              (ModuleCat.of R (R ⧸ J ^ unop m))).inv ≫
            biprod.map
              (ModuleCat.ofHom (idealQuotientMapOfLE
                (Ideal.pow_le_pow_right f.unop.down.down)))
              (ModuleCat.ofHom (idealQuotientMapOfLE
                (Ideal.pow_le_pow_right f.unop.down.down)))
      apply biprod.hom_ext
      · simp only [Category.assoc,
          ModuleCat.biprodIsoProd_inv_comp_fst, biprod.map_fst]
        rw [← Category.assoc,
          ModuleCat.biprodIsoProd_inv_comp_fst]
        apply ModuleCat.hom_ext
        rfl
      · simp only [Category.assoc,
          ModuleCat.biprodIsoProd_inv_comp_snd, biprod.map_snd]
        rw [← Category.assoc,
          ModuleCat.biprodIsoProd_inv_comp_snd]
        apply ModuleCat.hom_ext
        rfl)

/-- The index-four term of the six-term diagram is derived Ext of the middle
quotient-product diagram. -/
def idealQuotientMayerVietorisDerivedExtPowersMiddleTermRefl
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (idealQuotientMayerVietorisDerivedExtPowersDiagram
        I J M n₀ n₁ h ⋙
      (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨4, by omega⟩) ≅
      (idealQuotientMayerVietorisProductPowersDiagram I J).op ⋙
        derivedExtContravariantFunctor M n₁ :=
  Iso.refl _

/-- The index-four term is naturally the pointwise biproduct of the two
derived local-cohomology powers diagrams. -/
def idealQuotientMayerVietorisDerivedExtPowersMiddleTermIso
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (idealQuotientMayerVietorisDerivedExtPowersDiagram
        I J M n₀ n₁ h ⋙
      (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨4, by omega⟩) ≅
      pointwiseBiprodFunctor
        (derivedLocalCohomologyPowersDiagram I M n₁)
        (derivedLocalCohomologyPowersDiagram J M n₁) :=
  idealQuotientMayerVietorisDerivedExtPowersMiddleTermRefl
      I J M n₀ n₁ h ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (idealQuotientMayerVietorisProductPowersIso I J).symm)
      (derivedExtContravariantFunctor M n₁) ≪≫
    Functor.isoWhiskerRight
      (diagramOpBiprodIso
        (localCohomology.ringModIdeals
          (localCohomology.idealPowersDiagram I))
        (localCohomology.ringModIdeals
          (localCohomology.idealPowersDiagram J)))
      (derivedExtContravariantFunctor M n₁) ≪≫
    additiveFunctorCompBiprodIso
      (localCohomology.ringModIdeals
        (localCohomology.idealPowersDiagram I)).op
      (localCohomology.ringModIdeals
        (localCohomology.idealPowersDiagram J)).op
      (derivedExtContravariantFunctor M n₁)

/-- The colimit of the index-four term is the biproduct of the two derived
local-cohomology objects. -/
def idealQuotientMayerVietorisDerivedExtPowersMiddleColimitIso
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    colimit
        (idealQuotientMayerVietorisDerivedExtPowersDiagram
            I J M n₀ n₁ h ⋙
          (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨4, by omega⟩) ≅
      derivedLocalCohomology I M n₁ ⊞
        derivedLocalCohomology J M n₁ :=
  HasColimit.isoOfNatIso
      (idealQuotientMayerVietorisDerivedExtPowersMiddleTermIso
        I J M n₀ n₁ h) ≪≫
    pointwiseBiprodColimitIso
      (derivedLocalCohomologyPowersDiagram I M n₁)
      (derivedLocalCohomologyPowersDiagram J M n₁)

/-- If both support-local-cohomology objects vanish, then the middle colimit
in the Mayer--Vietoris sequence vanishes. -/
theorem idealQuotientMayerVietorisDerivedExtPowersMiddleColimit_isZero
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)
    (hI : IsZero (derivedLocalCohomology I M n₁))
    (hJ : IsZero (derivedLocalCohomology J M n₁)) :
    IsZero
      (colimit
        (idealQuotientMayerVietorisDerivedExtPowersDiagram
            I J M n₀ n₁ h ⋙
          (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨4, by omega⟩)) :=
  (idealQuotientMayerVietorisDerivedExtPowersMiddleColimitIso
      I J M n₀ n₁ h).isZero_iff.mpr
    ((biprod_isZero_iff _ _).mpr ⟨hI, hJ⟩)

end EtaleFundamentalGroups

end
