/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Schemes.Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field
import AlgebraicCurves.Geometry.Schemes.Scheme_bijective_algebraMap_sections_of_isProper_of_isIntegral
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit

/-!
# Local triviality of fibrewise trivial invertible modules
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleBaseChangeTrivialization
attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
attribute [-simp] DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

noncomputable section

namespace P2mSeesawLocal

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

section Base

variable (k : Type u) [Field k] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

theorem finiteType_sections [LocallyOfFiniteType t] (V : T.Opens) (hV : IsAffineOpen V) :
    letI := algebraOfHom t V
    Algebra.FiniteType k Γ(T, V) := by
  have h1 : (t.appLE ⊤ V le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType t inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩
      le_top
  have h2 : ((Scheme.ΓSpecIso (.of k)).inv ≫ t.appLE ⊤ V le_top).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  exact h2

theorem bijective_algebraMap_residueField [IsAlgClosed k] (R : Type u) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (𝔪 : PrimeSpectrum R) (h𝔪 : 𝔪.asIdeal.IsMaximal) :
    Function.Bijective (algebraMap k 𝔪.asIdeal.ResidueField) := by
  have : Algebra.FiniteType k 𝔪.asIdeal.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom k R _)
      (Ideal.algebraMap_residueField_surjective 𝔪.asIdeal)
  have : Module.Finite k 𝔪.asIdeal.ResidueField := finite_of_finite_type_of_isJacobsonRing k _
  have : Algebra.IsIntegral k 𝔪.asIdeal.ResidueField := Algebra.IsIntegral.of_finite k _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem fromSpec_comp (V : T.Opens) (hV : IsAffineOpen V) :
    letI := algebraOfHom t V
    hV.fromSpec ≫ t = specMap k Γ(T, V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hV (le_top : V ≤ t ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm

end Base

theorem algebraMap_algebraOfHom_top {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of
  R))
    (r : R) :
    (letI := algebraOfHom p ⊤; algebraMap R Γ(Y, ⊤) r) = p.appTop ((Scheme.ΓSpecIso (.of R)).inv r)
      := by
  have happ : p.appLE ⊤ ⊤ le_top = p.app ⊤ := Scheme.Hom.appLE_eq_app p
  change (p.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv r) = _
  rw [happ]

theorem bijective_algebraMap_of_iso {R : Type u} [CommRing R] {Y Y' : Scheme.{u}}
    (p : Y ⟶ Spec (.of R)) (p' : Y' ⟶ Spec (.of R)) (e : Y' ≅ Y) (he : p' = e.hom ≫ p)
    (h : letI := algebraOfHom p ⊤; Function.Bijective (algebraMap R Γ(Y, ⊤))) :
    letI := algebraOfHom p' ⊤; Function.Bijective (algebraMap R Γ(Y', ⊤)) := by
  subst he
  have key : (letI := algebraOfHom (e.hom ≫ p) ⊤; (algebraMap R Γ(Y', ⊤) : R → Γ(Y', ⊤))) =
      e.hom.appTop ∘ (letI := algebraOfHom p ⊤; (algebraMap R Γ(Y, ⊤) : R → Γ(Y, ⊤))) := by
    funext r
    simp only [Function.comp_apply, algebraMap_algebraOfHom_top, Scheme.Hom.comp_appTop]
    rfl
  rw [key]
  have : IsIso e.hom.appTop := (inferInstance : IsIso (e.hom.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).comp h

section Fibre

variable (k : Type u) [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
  (R : Type u) [CommRing R] [Algebra k R] (K : Type u) [CommRing K] [Algebra R K] [Algebra k K]
  [IsScalarTower k R K]

theorem specMap_comp : specMap R K ≫ specMap k R = specMap k K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/--
The canonical comparison between the iterated base change and the direct base change to the
field.
-/
def fibreIso :
    pullback (pullback.snd c (specMap k R)) (specMap R K) ≅ pullback c (specMap k K) :=
  pullbackLeftPullbackSndIso c (specMap k R) (specMap R K) ≪≫ pullback.congrHom rfl (specMap_comp k
    R K)
@[reassoc]
theorem fibreIso_hom_snd :
    (fibreIso k c R K).hom ≫ pullback.snd c (specMap k K) =
      pullback.snd (pullback.snd c (specMap k R)) (specMap R K) := by
  simp only [fibreIso, Iso.trans_hom, Category.assoc]
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_snd c (specMap k R) (specMap R K)

end Fibre

theorem bijective_algebraMap_sections_fibre (k : Type u) [Field k] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of k)) [IsSeparated c] [QuasiCompact c]
    (hX : letI := algebraOfHom c ⊤; Function.Bijective (algebraMap k Γ(X, ⊤)))
    (R : Type u) [CommRing R] [Algebra k R] (𝔭 : PrimeSpectrum R) :
    letI := algebraOfHom (pullback.snd (pullback.snd c (specMap k R))
      (specMap R 𝔭.asIdeal.ResidueField)) ⊤
    Function.Bijective (algebraMap 𝔭.asIdeal.ResidueField
      Γ(pullback (pullback.snd c (specMap k R)) (specMap R 𝔭.asIdeal.ResidueField), ⊤)) :=
  bijective_algebraMap_of_iso _ _ (fibreIso k c R 𝔭.asIdeal.ResidueField)
    (fibreIso_hom_snd k c R _).symm
    (AlgebraicGeometry.Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field k c hX
      _)

section BC

variable {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (s : SchemeHomOver t' t)

@[reassoc]
theorem baseChangeSnd_fst : baseChangeSnd c s ≫ pullback.fst c t = pullback.fst c t' := by
  unfold baseChangeSnd
  rw [pullback.lift_fst, Category.comp_id]
@[reassoc]
theorem baseChangeSnd_snd : baseChangeSnd c s ≫ pullback.snd c t = pullback.snd c t' ≫ s.1 := by
  unfold baseChangeSnd
  rw [pullback.lift_snd]

theorem isOpenImmersion_baseChangeSnd [IsOpenImmersion s.1] : IsOpenImmersion (baseChangeSnd c s)
  := by
  unfold baseChangeSnd
  infer_instance

theorem range_baseChangeSnd [IsOpenImmersion s.1] :
    Set.range (baseChangeSnd c s) = pullback.snd c t ⁻¹' Set.range s.1 := by
  unfold baseChangeSnd
  rw [Scheme.Pullback.range_map]
  have h1 : Set.range (𝟙 C) = Set.univ := Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [h1, Set.preimage_univ, Set.univ_inter]

end BC

section MaxFibre

variable (k : Type u) [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (R : Type u) [CommRing R] [Algebra k R] (i : Spec (.of R) ⟶ T) (hi : i ≫ t = specMap k R)
    (K : Type u) [Field K] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    (hK : Function.Bijective (algebraMap k K))

/--
The point obtained by transporting the residue field through its isomorphism with the base
field.
-/
def pointOf : Spec (.of k) ⟶ T :=
  Spec.map (CommRingCat.ofHom (((RingEquiv.ofBijective _ hK).symm : K →+* k).comp (algebraMap R
    K))) ≫ i
include hi in
theorem pointOf_comp : pointOf k R i K hK ≫ t = 𝟙 _ := by
  rw [pointOf, Category.assoc, hi, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (((RingEquiv.ofBijective _ hK).symm : K →+* k).comp (algebraMap R K)).comp (algebraMap k
    R) =
      RingHom.id k := by
    ext a
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingHom.id_apply]
    rw [← IsScalarTower.algebraMap_apply]
    exact (RingEquiv.ofBijective _ hK).symm_apply_apply a
  rw [this, CommRingCat.ofHom_id]
  exact Spec.map_id _
omit [Algebra k R] [IsScalarTower k R K] in
theorem specMap_pointOf :
    specMap k K ≫ Spec.map (CommRingCat.ofHom
      (((RingEquiv.ofBijective _ hK).symm : K →+* k).comp (algebraMap R K))) = specMap R K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  exact (RingEquiv.ofBijective _ hK).apply_symm_apply _

/-- The morphism from the base-changed fibre to the fibre over the identity point. -/
def fibreToPoint :
    pullback (pullback.snd c (specMap k R)) (specMap R K) ⟶ pullback c (𝟙 (Spec (.of k))) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst c (specMap k R)) (pullback.snd _ _ ≫ specMap k K)
    (by rw [Category.assoc, pullback.condition, pullback.condition_assoc, Category.assoc,
          Category.comp_id, specMap_comp])
include hi in
theorem fibreToPoint_comp :
    fibreToPoint k c R K ≫ baseChangeSnd c (⟨pointOf k R i K hK, pointOf_comp k t R i hi K hK⟩ :
        SchemeHomOver (𝟙 _) t) =
      pullback.fst _ _ ≫ baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R) t) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, baseChangeSnd_fst, baseChangeSnd_fst, fibreToPoint,
      pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, baseChangeSnd_snd, baseChangeSnd_snd, fibreToPoint,
      pullback.lift_snd_assoc]
    change pullback.snd _ _ ≫ specMap k K ≫ Spec.map _ ≫ i = _
    rw [← Category.assoc (specMap k K), specMap_pointOf, ← Category.assoc, ← Category.assoc,
      ← pullback.condition]

theorem nonempty_iso_fibre (L : (pullback c t).Modules)
    (hL : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c
      (⟨pointOf k R i K hK, pointOf_comp k t R i hi K hK⟩ : SchemeHomOver (𝟙 _) t))).obj L ≅
        SheafOfModules.unit (pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback
        (pullback.fst (pullback.snd c (specMap k R)) (specMap R K))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R)
            t))).obj L) ≅
      SheafOfModules.unit (pullback (pullback.snd c (specMap k R)) (specMap R K)).ringCatSheaf) :=
  ⟨(Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr (fibreToPoint_comp k c t R i hi K hK).symm).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback _).mapIso hL.some ≪≫
    Scheme.Modules.pullbackUnitIso _⟩

end MaxFibre

section Final

variable (k : Type u) [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (R : Type u) [CommRing R] [Algebra k R] (i : Spec (.of R) ⟶ T) [IsOpenImmersion i]
    (hi : i ≫ t = specMap k R)

theorem range_eq (g : R) (U : T.Opens) (hU : (U : Set T) = i '' (PrimeSpectrum.basicOpen g).1) :
    Set.range (baseChangeSnd c (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)) =
      Set.range (((pullback.snd c (specMap k R)) ⁻¹ᵁ (PrimeSpectrum.basicOpen g)).ι ≫
        baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R) t)) := by
  have hcomp : ∀ y, (((pullback.snd c (specMap k R)) ⁻¹ᵁ (PrimeSpectrum.basicOpen g)).ι ≫
      baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R) t)) y =
        baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R) t)
          ((((pullback.snd c (specMap k R)) ⁻¹ᵁ (PrimeSpectrum.basicOpen g)).ι) y) :=
    fun y => Scheme.Hom.comp_apply _ _ y
  have hsnd : ∀ y, pullback.snd c t (baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R) t) y) =
      i (pullback.snd c (specMap k R) y) := fun y => by
    rw [← Scheme.Hom.comp_apply, baseChangeSnd_snd, Scheme.Hom.comp_apply]
  rw [range_baseChangeSnd]
  change pullback.snd c t ⁻¹' Set.range U.ι = _
  rw [Scheme.Opens.range_ι, hU]
  ext z
  constructor
  · rintro ⟨q, hq, hz⟩
    have hz' : z ∈ Set.range (baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R) t)) := by
      rw [range_baseChangeSnd]
      exact ⟨q, hz⟩
    obtain ⟨y, rfl⟩ := hz'
    have hy : pullback.snd c (specMap k R) y = q := by
      apply i.isOpenEmbedding.injective
      rw [← hsnd, hz]
    refine ⟨⟨y, ?_⟩, hcomp _⟩
    change pullback.snd c (specMap k R) y ∈ PrimeSpectrum.basicOpen g
    rw [hy]
    exact hq
  · rintro ⟨y, rfl⟩
    rw [hcomp]
    exact ⟨_, y.2, (hsnd _).symm⟩

theorem nonempty_iso_of_isFrameOn (L : (pullback c t).Modules) (g : R)
    (m : Γ((Scheme.Modules.pullback (baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R)
      t))).obj L, ⊤))
    (hm : Scheme.Modules.IsFrameOn m ((pullback.snd c (specMap k R)) ⁻¹ᵁ (PrimeSpectrum.basicOpen
      g)))
    (U : T.Opens) (hU : (U : Set T) = i '' (PrimeSpectrum.basicOpen g).1) :
    Nonempty ((Scheme.Modules.pullback
        (baseChangeSnd c (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t))).obj L ≅
      SheafOfModules.unit (pullback c (U.ι ≫ t)).ringCatSheaf) := by
  obtain ⟨eW⟩ := AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit hm
    ((pullback.snd c (specMap k R)) ⁻¹ᵁ (PrimeSpectrum.basicOpen g)) le_top le_rfl
  have := isOpenImmersion_baseChangeSnd c (⟨i, hi⟩ : SchemeHomOver (specMap k R) t)
  have := isOpenImmersion_baseChangeSnd c (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)
  let φ := IsOpenImmersion.isoOfRangeEq _ _ (range_eq k c t R i hi g U hU)
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (range_eq k c t R i hi g U hU)
  exact ⟨(Scheme.Modules.pullbackCongr hfac.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp φ.hom _).app L).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso (((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫ eW) ≪≫
    Scheme.Modules.pullbackUnitIso φ.hom⟩

end Final

open _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
theorem main (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of
  k))
    [IsProper c] [IsIntegral X]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [IsReduced T]
    (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L)
    (htriv : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t,
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c τ)).obj L ≅
        SheafOfModules.unit (Limits.pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf))
    (x : T) :
    ∃ U : T.Opens, x ∈ U ∧ Nonempty ((Scheme.Modules.pullback
        (baseChangeSnd c (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t))).obj L ≅
      SheafOfModules.unit (Limits.pullback c (U.ι ≫ t)).ringCatSheaf) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : T.Opens) from trivial)
  let : Algebra k Γ(T, V) := algebraOfHom t V
  have : Algebra.FiniteType k Γ(T, V) := finiteType_sections k t V hV
  have : IsNoetherianRing Γ(T, V) := Algebra.FiniteType.isNoetherianRing k _
  have : IsJacobsonRing Γ(T, V) := isJacobsonRing_of_finiteType (A := k)
  have hi : hV.fromSpec ≫ t = specMap k Γ(T, V) := fromSpec_comp k t V hV
  have hX := AlgebraicGeometry.Scheme.bijective_algebraMap_sections_of_isProper_of_isIntegral k c
  have hO := bijective_algebraMap_sections_fibre k c hX Γ(T, V)
  have hL' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback
      (baseChangeSnd c (⟨hV.fromSpec, hi⟩ : SchemeHomOver (specMap k Γ(T, V)) t))).obj L) :=
    hL.pullback _
  have htriv' : ∀ 𝔪 : PrimeSpectrum Γ(T, V), 𝔪.asIdeal.IsMaximal →
      Nonempty ((Scheme.Modules.pullback
        (pullback.fst (pullback.snd c (specMap k Γ(T, V))) (specMap Γ(T, V)
          𝔪.asIdeal.ResidueField))).obj
          ((Scheme.Modules.pullback
            (baseChangeSnd c (⟨hV.fromSpec, hi⟩ : SchemeHomOver (specMap k Γ(T, V)) t))).obj L) ≅
        SheafOfModules.unit (pullback (pullback.snd c (specMap k Γ(T, V)))
          (specMap Γ(T, V) 𝔪.asIdeal.ResidueField)).ringCatSheaf) := fun 𝔪 h𝔪 =>
    nonempty_iso_fibre k c t Γ(T, V) hV.fromSpec hi 𝔪.asIdeal.ResidueField
      (bijective_algebraMap_residueField k Γ(T, V) 𝔪 h𝔪) L (htriv _)
  obtain ⟨g, m, hg, hframe⟩ :=
    exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
      (pullback.snd c (specMap k Γ(T, V))) hO _ hL' htriv' (hV.primeIdealOf ⟨x, hxV⟩)
  refine ⟨T.basicOpen g, ?_, nonempty_iso_of_isFrameOn k c t Γ(T, V) hV.fromSpec hi L g m
    (fun W hWU hWV => hframe W hWV) (T.basicOpen g) ?_⟩
  · have hx : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
    rw [← hx]
    change hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ (T.basicOpen g)
    rw [hV.fromSpec_preimage_basicOpen]
    exact hg
  · rw [← hV.fromSpec_image_basicOpen]
    rfl

end P2mSeesawLocal

end

end AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleBaseChangeTrivialization

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

universe u

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleBaseChangeTrivialization in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard in
open NeronModelInfra in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard in
open NeronModelInfra in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra in
theorem exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsProper c] [IsIntegral X]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [IsReduced T]
    (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L)
    (htriv : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t,
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c τ)).obj L ≅
        SheafOfModules.unit (Limits.pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf))
    (x : T) :
    ∃ U : T.Opens, x ∈ U ∧ Nonempty ((Scheme.Modules.pullback
        (baseChangeSnd c (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t))).obj L ≅
      SheafOfModules.unit (Limits.pullback c (U.ι ≫ t)).ringCatSheaf) :=
  P2mSeesawLocal.main k c t L hL htriv x
end AlgebraicGeometry.Scheme.Modules.IsInvertible
end ProofImplementation

open PresheafOfModules in
open PresheafOfModules.InternalHom in
attribute [-instance]
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  PresheafOfModules.instMonoidalClosed
  InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
  InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
attribute [-instance] SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
attribute [-instance] AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
attribute [-simp] AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
attribute [-simp] DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
