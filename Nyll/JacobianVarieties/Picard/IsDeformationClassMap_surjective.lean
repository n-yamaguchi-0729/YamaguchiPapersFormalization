/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic.LinearCombination
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_isFrameOn_of_isUnit
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul
import Nyll.JacobianVarieties.Picard.Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isInvertible_of_forall_exists_isFrameOn

/-!
# Surjectivity of the dual-number deformation class map

Transition units of the form `1 + ε f` glue an invertible module whose reduction
and rigidifying section are trivial. Its class maps to the prescribed Cech class.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DeformationSurjectivity
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


namespace PicTanSurj

section RingSide

theorem map01_fst_oneAddEpsMul {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u)
    [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (f : ((𝒱.pullback c A).cover
      (pullback.snd c (specMap R A))).A01) :
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).map01 (oneAddEpsMul A 𝒱 c f) = 1 := by
  have h1 : oneAddEpsMul A 𝒱 c f = 1 + (DualNumber.eps : DualNumber A) • (dualNumberThickening A 𝒱
    c).map01 f := by
    simp only [oneAddEpsMul, Algebra.smul_def]
  rw [h1, map_add, LinearMap.map_smulₛₗ]
  have h2 : (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 := by
    exact DualNumber.fst_eps
  rw [h2, zero_smul, add_zero, HomOver.map01_apply]
  exact map_one ((HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom.appLE
    ((𝒱.pullback c (TrivSqZeroExt A A)).U0 ⊓ (𝒱.pullback c (TrivSqZeroExt A A)).U1)
    ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1)
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).inf_le).hom

theorem nonempty_iso_unit_of_isFrameOn_of_map_eq {X : Scheme.{u}} {L : X.Modules} {U V : X.Opens}
    (hUV : U ⊔ V = ⊤)
    {sU : Γ(L, U)} {sV : Γ(L, V)} (hsU : Scheme.Modules.IsFrameOn sU U) (hsV :
      Scheme.Modules.IsFrameOn sV V)
    (h : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU =
      L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by
  refine Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul hUV hsU hsV
    (Scheme.Modules.isFrameOn_unitSection U) (Scheme.Modules.isFrameOn_unitSection V) 1 ?_ ?_
  · rw [h]; exact (one_smul _ _).symm
  · change (𝟙_ X.Modules).presheaf.map (homOfLE _).op (Scheme.Modules.unitSection U) =
      (1 : Γ(X, U ⊓ V)) • (𝟙_ X.Modules).presheaf.map (homOfLE _).op (Scheme.Modules.unitSection V)
    rw [Scheme.Modules.map_unitSection, Scheme.Modules.map_unitSection]
    exact ((Scheme.Modules.smul_unitSection _).trans rfl).symm

theorem isInvertible_of_isFrameOn_two {X : Scheme.{u}} {L : X.Modules} {U V : X.Opens}
    (hUV : U ⊔ V = ⊤)
    {sU : Γ(L, U)} {sV : Γ(L, V)} (hsU : Scheme.Modules.IsFrameOn sU U) (hsV :
      Scheme.Modules.IsFrameOn sV V) :
    Scheme.Modules.IsInvertible L := by
  apply Scheme.Modules.isInvertible_of_forall_exists_isFrameOn
  intro x
  have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
  rcases TopologicalSpace.Opens.mem_sup.1 hx with hxU | hxV
  · exact ⟨U, sU, hxU, hsU⟩
  · exact ⟨V, sV, hxV, hsV⟩

end RingSide

section Yoga

variable {X Y Z : Scheme.{u}}

theorem pullback_comp_unit (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (g ≫ f)).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackComp g f).app M).symm ≪≫ (Scheme.Modules.pullback g).mapIso h.some ≪≫
    Scheme.Modules.pullbackUnitIso g⟩

theorem pullback_congr_unit {f f' : Y ⟶ X} (hf : f = f') (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f').obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackCongr hf).app M).symm ≪≫ h.some⟩

theorem unit_of_pullback_comp (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback (g ≫ f)).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M) ≅
      SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackComp g f).app M) ≪≫ h.some⟩

end Yoga

section SchemeSide

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙
  (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

theorem stage_fstHom_hom :
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom = RelPicard.baseChangeSnd c
      (dualNumberReductionOver R A) := by
  change RelPicard.baseChangeSnd c (LFP.stageHom R (TrivSqZeroExt.fstHom R A A)) = _
  congr 1

theorem nonempty_pullback_red_iso_unit (M : (Limits.pullback c (specMap R (DualNumber A))).Modules)
    (a : Γ(M, (𝒱.pullback c (DualNumber A)).U0)) (b : Γ(M, (𝒱.pullback c (DualNumber A)).U1))
    (ha : Scheme.Modules.IsFrameOn a (𝒱.pullback c (DualNumber A)).U0)
    (hb : Scheme.Modules.IsFrameOn b (𝒱.pullback c (DualNumber A)).U1)
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01)
    (hab : M.presheaf.map (homOfLE inf_le_right).op b =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A
            𝒱 c f) •
        M.presheaf.map (homOfLE inf_le_left).op a) :
    Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R
      A))).obj M ≅
      SheafOfModules.unit (Limits.pullback c (specMap R A)).ringCatSheaf) := by
  obtain ⟨a', b', ha', hb', hab'⟩ :=
    Scheme.TwoAffineOpenCover.exists_isFrameOn_pullback_stage_of_map_eq_smul 𝒱 c
      (TrivSqZeroExt.fstHom R A A)
      M a b ha hb _ hab
  dsimp only at hab'
  rw [map01_fst_oneAddEpsMul] at hab'
  have h1 : ((Scheme.Modules.pullback (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom).obj
    M).presheaf.map
      (homOfLE (inf_le_left : (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1 ≤ _)).op a' =
      ((Scheme.Modules.pullback (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom).obj
        M).presheaf.map
      (homOfLE (inf_le_right : (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1 ≤ _)).op b' := by
    rw [hab']
    let N : (Limits.pullback c (specMap R A)).Modules :=
      (Scheme.Modules.pullback (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom).obj M
    exact (one_smul Γ(Limits.pullback c (specMap R A), (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1)
      (show Γ(N, (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) from
        N.presheaf.map (homOfLE inf_le_left).op a')).symm
  obtain ⟨e⟩ := nonempty_iso_unit_of_isFrameOn_of_map_eq (𝒱.pullback c A).sup_eq_top ha' hb' h1
  rw [stage_fstHom_hom] at e
  exact ⟨e⟩

theorem nonempty_pullback_rigSection_iso_unit
    (M : (Limits.pullback c (specMap R (DualNumber A))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (hker : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver
      R A))).obj M ≅
      SheafOfModules.unit (Limits.pullback c (specMap R A)).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (RelPicard.rigSection c (specMap R (DualNumber A)) ε)).obj M
      ≅
      SheafOfModules.unit (Spec (CommRingCat.of (DualNumber A))).ringCatSheaf) := by
  have hN : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (RelPicard.rigSection c (specMap R (DualNumber A)) ε)).obj M) :=
        hM.pullback _
  refine Scheme.Modules.IsInvertible.nonempty_iso_unit_of_dualNumber_of_reduction A _ hN ?_
  have hsq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫
      RelPicard.rigSection c (specMap R (DualNumber A)) ε =
      RelPicard.rigSection c (specMap R A) ε ≫ RelPicard.baseChangeSnd c (dualNumberReductionOver R
        A) := by
    rw [RelPicard.rigSection_baseChangeSnd]
    rfl
  apply unit_of_pullback_comp
  apply pullback_congr_unit hsq.symm
  exact pullback_comp_unit _ _ M hker

end SchemeSide

end PicTanSurj

namespace PicTanSurj
section Units
variable {R : Type u} [CommRing R] {C : Scheme.{u}} (A : Type u) [CommRing A] [Algebra R A]
  (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

theorem oneAddEpsMul_add (f f' : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    oneAddEpsMul A 𝒱 c (f + f') = oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c f' := by
  simp only [oneAddEpsMul, map_add]
  have he : algebraMap (DualNumber A)
      ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01
        DualNumber.eps *
      algebraMap (DualNumber A) _ DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  linear_combination (-((dualNumberThickening A 𝒱 c).map01 f * (dualNumberThickening A 𝒱 c).map01
    f')) * he

theorem isUnit_oneAddEpsMul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    IsUnit (oneAddEpsMul A 𝒱 c f) := by
  refine isUnit_iff_exists_inv.2 ⟨oneAddEpsMul A 𝒱 c (-f), ?_⟩
  rw [← oneAddEpsMul_add, add_neg_cancel]
  erw [oneAddEpsMul, map_zero, mul_zero, add_zero]

end Units
end PicTanSurj

open PicTanSurj in
theorem _root_.AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec
      (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    Function.Surjective δ := by
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have ht : IsUnit (show Γ(Limits.pullback c (specMap R (DualNumber A)),
      (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c
        f) :=
    isUnit_oneAddEpsMul A 𝒱 c f
  obtain ⟨M, a, b, ha, hb, hab⟩ := Scheme.Modules.exists_isFrameOn_of_isUnit
    (𝒱.pullback c (DualNumber A)).U0 (𝒱.pullback c (DualNumber A)).U1 _ ht
  have hM : Scheme.Modules.IsInvertible M :=
    isInvertible_of_isFrameOn_two (𝒱.pullback c (DualNumber A)).sup_eq_top ha hb
  have hker := nonempty_pullback_red_iso_unit c A 𝒱 M a b ha hb f hab
  have hrig := nonempty_pullback_rigSection_iso_unit c ε A M hM hker
  let Mr : RigidifiedLineBundle c ε (specMap R (DualNumber A)) := ⟨M, hM, hrig⟩
  have hmem : Nonempty ((Mr.pullbackAlong (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (specMap R A)).L) := hker
  exact ⟨Quotient.mk _ ⟨Mr, hmem⟩, hδ ⟨Mr, hmem⟩ a b f ha hb hab⟩
end JacobianVarieties.Picard.Proofs.DeformationSurjectivity
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
