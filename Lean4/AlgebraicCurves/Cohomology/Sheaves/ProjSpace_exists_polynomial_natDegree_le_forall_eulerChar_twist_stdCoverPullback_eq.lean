/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Topology.KrullDimension
import SchemeTheory.ProjectiveSpace.Basic
import SchemeTheory.ProjectiveSpace.Cover
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafEulerChar
import SchemeTheory.Modules.ProjectivePresentation
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import SchemeTheory.Modules.TensorPowers
import AlgebraicCurves.Geometry.Sheaves.ModulesPullbackMonoidalV2
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
import AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import AlgebraicCurves.Foundations.Algebra.LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial
import AlgebraicCurves.Geometry.Projective.ProjSpace_topologicalKrullDim_le_of_isClosedImmersion

/-!
# Proj Space exists polynomial nat Degree le forall euler Char twist std Cover Pullback eq
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq
attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
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
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulFamilies
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleFamilies
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
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
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
attribute [-simp] DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.MvPolynomial
open _root_.TensorProduct
open _root_.CategoryTheory.MonoidalCategory


attribute [local instance] MvPolynomial.gradedAlgebra

namespace C5bSol


open _root_.AlgebraicGeometry.OModulePresheaf hiding twist tensor zero


variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

/-- A natural family of additive maps of presheaf modules compatible with the base-ring action. -/
structure NatFamily (F G : OModulePresheaf π) where
  /-- The additive map on sections over each open. -/
  app : ∀ U : V.Opens, F.obj U →+ G.obj U
  /-- The maps preserve scalar multiplication by the base ring. -/
  smul : ∀ (U : V.Opens) (r : R) (x : F.obj U), app U (r • x) = r • app U x
  /-- The maps commute with restriction to smaller opens. -/
  natural : ∀ {U U' : V.Opens} (h : U ≤ U') (x : F.obj U'), app U (F.res h x) = G.res h (app U' x)

variable {F G : OModulePresheaf π} (η : NatFamily F G) (K : V.OrderedAffineCover)

/-- The component of the natural family as a base-ring linear map on sections. -/
def appₗ (U : V.Opens) : F.obj U →ₗ[R] G.obj U :=
  { toFun := η.app U, map_add' := map_add (η.app U), map_smul' := η.smul U }

theorem appₗ_apply (U : V.Opens) (x : F.obj U) : appₗ η U x = η.app U x := rfl

/-- The induced linear map on Cech cochains obtained by applying the family on each
intersection. -/
def cochainMap (i : ℕ) : F.cochain K i →ₗ[R] G.cochain K i :=
  LinearMap.pi fun s => (appₗ η (K.inter s)).comp (LinearMap.proj s)

theorem cochainMap_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx i) :
    cochainMap η K i c s = η.app (K.inter s) (c s) := rfl

theorem cochainMap_d (i : ℕ) (c : F.cochain K i) :
    cochainMap η K (i + 1) (F.d K i c) = G.d K i (cochainMap η K i c) := by
  funext s
  rw [cochainMap_apply, d_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, η.natural, cochainMap_apply]

theorem cochainMap_bijective (hη : ∀ (i : ℕ) (s : K.Idx i), Function.Bijective (η.app (K.inter s)))
  (i : ℕ) :
    Function.Bijective (cochainMap η K i) := by
  constructor
  · intro c c' h
    funext s
    exact (hη i s).1 (by rw [← cochainMap_apply, ← cochainMap_apply, h])
  · intro c
    refine ⟨fun s => (Equiv.ofBijective _ (hη i s)).symm (c s), funext fun s => ?_⟩
    rw [cochainMap_apply]
    exact Equiv.ofBijective_apply_symm_apply _ (hη i s) (c s)

theorem eulerChar_eq_of_natFamily (hη : ∀ (i : ℕ) (s : K.Idx i), Function.Bijective (η.app (K.inter
  s))) :
    F.eulerChar K = G.eulerChar K := by
  have hcomm := LinearMap.nonempty_kerModRange_equiv_of_equiv_comm (F.d K) (G.d K)
    (fun i => LinearEquiv.ofBijective (cochainMap η K i) (cochainMap_bijective η K hη i))
    (fun i x => cochainMap_d η K i x)
  rw [eulerChar_def, eulerChar_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  cases i with
  | zero =>
      obtain ⟨e⟩ := hcomm.1
      rw [cechFinrank_zero, cechFinrank_zero]
      exact e.finrank_eq
  | succ i =>
      obtain ⟨e⟩ := hcomm.2 i
      rw [cechFinrank_succ, cechFinrank_succ]
      exact e.finrank_eq

theorem eulerChar_eq_of_nonempty_equiv
    (h0 : Nonempty (F.H0 K ≃ₗ[R] G.H0 K)) (hs : ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i)) :
    F.eulerChar K = G.eulerChar K := by
  rw [eulerChar_def, eulerChar_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  cases i with
  | zero => obtain ⟨e⟩ := h0; rw [cechFinrank_zero, cechFinrank_zero]; exact e.finrank_eq
  | succ i => obtain ⟨e⟩ := hs i; rw [cechFinrank_succ, cechFinrank_succ]; exact e.finrank_eq

theorem supportedIn_top (M : V.Modules) : (OModulePresheaf.ofModules π M).SupportedIn ⊤ := by
  intro W hW
  have hW' : ((W : V.Opens) : Set V) = ∅ := by simpa using hW
  have hbot : (W : V.Opens) = ⊥ := TopologicalSpace.Opens.ext (by simpa using hW')
  have : Subsingleton Γ(V, (W : V.Opens)) := by rw [hbot]; infer_instance
  exact Module.subsingleton Γ(V, (W : V.Opens)) _

end C5bSol

end ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq
end AlgebraicCurves.Cohomology.Sheaves.Proofs

namespace AlgebraicGeometry.ProjSpace

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.MvPolynomial
open _root_.TensorProduct
open _root_.CategoryTheory.MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq in
theorem exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧
      ∀ d : ℕ,
        ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).eulerChar (ProjSpace.stdCoverPullback ι) : ℚ)
          = P.eval (d : ℚ) := by
  classical
  obtain ⟨L, 𝔓, h𝔓, hL⟩ :=
    AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial ι
  have hdim : topologicalKrullDim Z ≤ n :=
    AlgebraicGeometry.ProjSpace.topologicalKrullDim_le_of_isClosedImmersion ι
  have : IsProper (ι ≫ ProjSpace.π k n) := inferInstance
  have h1 : ∀ x : Z, ∃ U : Z.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (𝟙_ Z.Modules) ≅ SheafOfModules.unit
        U.toScheme.ringCatSheaf) :=
    fun x => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackTensorUnitObjIso (⊤ : Z.Opens).ι⟩⟩
  obtain ⟨p, hp, hpev⟩ :=
    OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2 (ι ≫
      ProjSpace.π k n)
      (ProjSpace.stdCoverPullback ι) (𝟙_ Z.Modules)
      (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial _ _ h1)
      (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial _ _ h1)
      ⊤ (C5bSol.supportedIn_top _) n ((topologicalKrullDim_subspace_le Z _).trans hdim) L hL
  refine ⟨p, hp, fun d => ?_⟩
  rw [← hpev d]
  congr 1
  have hlam := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso (ι ≫ ProjSpace.π k n) (λ_
    (L.tensorPow d))
    (ProjSpace.stdCoverPullback ι)
  rw [C5bSol.eulerChar_eq_of_nonempty_equiv (ProjSpace.stdCoverPullback ι) hlam.1 hlam.2.1]
  symm
  have key : ∀ (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom φ],
      𝔓.toProj = φ →
      (OModulePresheaf.ofModules (ι ≫ ProjSpace.π k n) (L.tensorPow d)).eulerChar
        (ProjSpace.stdCoverPullback φ) =
        (ProjSpace.twist (ι ≫ ProjSpace.π k n) φ d).eulerChar (ProjSpace.stdCoverPullback φ) := by
    intro φ _ hφ
    subst hφ
    obtain ⟨e, -, hnat, hbij⟩ :=
      Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 𝔓 d
    refine C5bSol.eulerChar_eq_of_natFamily (F := OModulePresheaf.ofModules _ (L.tensorPow d))
      (G := ProjSpace.twist _ 𝔓.toProj d)
      { app := fun U => (e U).toAddMonoidHom
        smul := fun U r x => ?_
        natural := fun h x => hnat _ _ h x } (ProjSpace.stdCoverPullback 𝔓.toProj) ?_
    · let := Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ ProjSpace.π k n) U
      change e U (r • x) = r • e U x
      rw [OModulePresheaf.ofModules_algebraMap_smul]
      erw [(e U).map_smul]
      exact (ProjSpace.twistObj.algebraMap_smul r (e U x)).symm
    · intro i s
      exact hbij _ (s.1 0).down ((ProjSpace.stdCoverPullback 𝔓.toProj).inter_le s 0)
  exact key ι h𝔓

end AlgebraicGeometry.ProjSpace
end ProofImplementation

open PresheafOfModules in
open PresheafOfModules.InternalHom in
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
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
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
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
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulFamilies
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleFamilies
attribute [-simp] AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
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
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec
