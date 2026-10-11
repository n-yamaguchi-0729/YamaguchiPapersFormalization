/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Lagrange
import SchemeTheory.ProjectiveSpace.Basic
import AlgebraicCurves.Hilbert.Functor.Basic
import SchemeTheory.ProjectiveSpace.Cover
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import SchemeTheory.Cohomology.Cech.TwoChartCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
import SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_forall_subsingleton_HSucc_twist
import AlgebraicCurves.Hilbert.exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
import SchemeTheory.ProjectiveSpace.BaseChange
import AlgebraicCurves.Foundations.Algebra.Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion
import AlgebraicCurves.Cohomology.Sheaves.ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import SchemeTheory.Cohomology.Sheaves.OModulePresheaf_d_comp_d

/-!
# Local Hilbert functions for flat closed immersions over Noetherian rings
-/

section ProofImplementation

namespace AlgebraicCurves.Hilbert.Proofs.HilbertNoetherianCover
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

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs6C0

theorem cover {A : Type} [CommRing A] {σ : Type} (v : PrimeSpectrum A → σ) (hv : IsLocallyConstant
  v) :
    ∃ (J : Type) (_ : Fintype J) (r : J → A), Ideal.span (Set.range r) = ⊤ ∧
      ∀ j : J, ∃ P₀ : PrimeSpectrum A, r j ∉ P₀.asIdeal ∧ ∀ P : PrimeSpectrum A, r j ∉ P.asIdeal →
        v P = v P₀ := by
  classical
  have hfin : (Set.range v).Finite := hv.range_finite
  have hclopen : ∀ y : σ, IsClopen (v ⁻¹' {y}) := fun y => hv.isClopen_fiber y
  have hidem : ∀ y : σ, ∃ e : A, (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) = v ⁻¹' {y} :=
    by
    intro y
    obtain ⟨e, -, he⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hclopen y)
    exact ⟨e, he.symm⟩
  choose r hr using hidem
  let : Fintype ↥(Set.range v) := hfin.fintype
  refine ⟨↥(Set.range v), inferInstance, fun y => r y.1, ?_, ?_⟩
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    apply top_le_iff.mp
    intro P _
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨v P, ⟨P, rfl⟩⟩, ?_⟩
    change P ∈ (PrimeSpectrum.basicOpen (r (v P)) : Set (PrimeSpectrum A))
    rw [hr]; rfl
  · rintro ⟨y, ⟨P₀, rfl⟩⟩
    refine ⟨P₀, ?_, ?_⟩
    · have : P₀ ∈ (PrimeSpectrum.basicOpen (r (v P₀)) : Set (PrimeSpectrum A)) := by rw [hr]; rfl
      exact this
    · intro P hP
      have : P ∈ (PrimeSpectrum.basicOpen (r (v P₀)) : Set (PrimeSpectrum A)) := hP
      rw [hr] at this
      exact this

theorem geompt {A : Type} [CommRing A] (P : PrimeSpectrum A) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra A k), RingHom.ker (algebraMap A k)
      = P.asIdeal := by
  refine ⟨AlgebraicClosure P.asIdeal.ResidueField, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsScalarTower.algebraMap_eq A P.asIdeal.ResidueField (AlgebraicClosure
    P.asIdeal.ResidueField),
    ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot (algebraMap P.asIdeal.ResidueField (AlgebraicClosure
      P.asIdeal.ResidueField))).1
      (algebraMap P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField)).injective, ←
        RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

theorem flat_sections {A : Type} [CommRing A] {Z : Scheme.{0}} (πZ : Z ⟶ Spec (CommRingCat.of A))
  [Flat πZ]
    (U : Z.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ U
    Module.Flat A Γ(Z, U) := by
  have h1 : (πZ.appLE ⊤ U le_top).hom.Flat :=
    Flat.flat_appLE πZ (isAffineOpen_top (Spec (.of A))) hU le_top
  have h2 : ((Scheme.ΓSpecIso (.of A)).inv).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)
  exact RingHom.Flat.comp h2 h1

section FromC3
universe u
variable {n : ℕ}

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback in
open P2mWs6C3 renaming inter_le_pullbackChart → baseChange_inter_le_pullbackChart in
theorem inter_le_pullbackChart {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) (t : Fin (i + 1)) :
    (ProjSpace.stdCoverPullback φ).inter s ≤ ProjSpace.pullbackChart φ ((s.1 t).down) := by
  exact baseChange_inter_le_pullbackChart φ s t

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback in
open P2mWs6C3 renaming isAffineOpen_inter → baseChange_isAffineOpen_inter in
theorem isAffineOpen_inter {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) :
    IsAffineOpen ((ProjSpace.stdCoverPullback φ).inter s) := by
  exact baseChange_isAffineOpen_inter φ s

end FromC3

theorem flat_cochain {A : Type} [CommRing A] {n : ℕ} {Z : Scheme.{0}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
    [Flat (ι ≫ ProjSpace.π A n)] (d i : ℕ) :
    Module.Flat A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback
      ι) i) := by
  have : ∀ s : (ProjSpace.stdCoverPullback ι).Idx i,
      Module.Flat A (ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback
        ι).inter s)) := by
    intro s
    obtain ⟨f, -, -⟩ := AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart
      (ι ≫ ProjSpace.π A n) ι d
      (inter_le_pullbackChart ι s 0)
    let := Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ ProjSpace.π A n)
      ((ProjSpace.stdCoverPullback ι).inter s)
    have : IsScalarTower A Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)
        (ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s)) :=
      (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).isScalarTower _
    have := flat_sections (ι ≫ ProjSpace.π A n) ((ProjSpace.stdCoverPullback ι).inter s)
      (isAffineOpen_inter ι s)
    exact Module.Flat.of_linearEquiv (f.restrictScalars A)
  change Module.Flat A (∀ s : (ProjSpace.stdCoverPullback ι).Idx i,
    ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s))
  classical
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype A ((ProjSpace.stdCoverPullback ι).Idx i)
      (fun s => ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter
        s))).symm

open TensorProduct in
theorem finrank_baseChange_eq_rankAtStalk {A : Type} [CommRing A] (M : Type) [AddCommGroup M]
  [Module A M]
    [Module.Finite A M] [Module.Flat A M] (k : Type) [Field k] [Algebra A k] :
    Module.finrank k (k ⊗[A] M) = Module.rankAtStalk M ⟨RingHom.ker (algebraMap A k),
      RingHom.ker_isPrime _⟩ := by
  let P : PrimeSpectrum A := ⟨RingHom.ker (algebraMap A k), RingHom.ker_isPrime _⟩
  have : P.asIdeal.IsPrime := RingHom.ker_isPrime _
  change Module.finrank k (k ⊗[A] M) = Module.rankAtStalk M P
  have hf₂ : P.asIdeal.primeCompl ≤ (IsUnit.submonoid k).comap (algebraMap A k) := by
    intro s hs
    change IsUnit (algebraMap A k s)
    exact isUnit_iff_ne_zero.mpr hs
  let alg : Algebra P.asIdeal.ResidueField k := (Ideal.ResidueField.lift P.asIdeal (algebraMap A k)
    le_rfl hf₂).toAlgebra
  have : IsScalarTower A P.asIdeal.ResidueField k := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap A k a = Ideal.ResidueField.lift P.asIdeal (algebraMap A k) le_rfl hf₂
      (algebraMap A _ a)
    rw [Ideal.ResidueField.lift_algebraMap])
  rw [Module.rankAtStalk_eq, ← Module.finrank_baseChange (R := k) (M' := P.asIdeal.Fiber M)]
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A P.asIdeal.ResidueField k k
    M).finrank_eq.symm

section Pull
universe u
variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
  (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
  (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
  (e : Z' ⟶ Z)

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B

open HomogeneousLocalization

theorem X_eq_mvMapGraded_mul_one (i : Fin (n + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) B) = (ProjSpace.mvMapGraded A B n)
      (MvPolynomial.X i) * 1 := by
  rw [ProjSpace.mvMapGraded_X, mul_one]

theorem one_mem_zero : (1 : MvPolynomial (Fin (n + 1)) B) ∈ (MvPolynomial.homogeneousSubmodule (Fin
  (n + 1)) B) 0 :=
  SetLike.one_mem_graded _

/-- The coordinate localization map induced by the coefficient base change. -/
noncomputable def toB (i : Fin (n + 1)) : Away 𝒜A (MvPolynomial.X i) →+* Away 𝒜B (MvPolynomial.X i)
  :=
  (awayMap 𝒜B (one_mem_zero (n := n) B) (X_eq_mvMapGraded_mul_one (A := A) B i)).comp
    (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))

theorem toB_ratio (i j : Fin (n + 1)) : toB (A := A) B i (ProjSpace.ratio A n i j) =
  ProjSpace.ratio B n i j := by
  apply HomogeneousLocalization.val_injective
  rw [toB, RingHom.comp_apply, ProjSpace.ratio, Away.map_mk]
  rw [Away.mk, val_awayMap_mk, ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp [ProjSpace.mvMapGraded_X]⟩
open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback in
open P2mWs6C3 renaming restrictFun_app_pullAway → baseChange_restrictFun_app_pullAway in
omit [IsAffineHom ι] [IsAffineHom ι'] in
theorem restrictFun_app_pullAway (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i : Fin (n + 1))
    (a : Away 𝒜A (MvPolynomial.X i)) {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom
        ((ι.app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X
          i)).hom a)))
      = ProjSpace.restrictFun h₂ ((ι'.app (Proj.basicOpen 𝒜B (MvPolynomial.X i))).hom
          ((Proj.awayToSection 𝒜B (MvPolynomial.X i)).hom (toB (A := A) B i a))) := by
  exact baseChange_restrictFun_app_pullAway ι B ι' e hcomp i a h₁ h₂
omit [IsAffineHom ι] [IsAffineHom ι'] in
theorem restrictFun_app_frameUnit (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i j : Fin (n + 1))
  {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom (ProjSpace.frameUnit ι i j))
      = ProjSpace.restrictFun h₂ (ProjSpace.frameUnit ι' i j) := by
  rw [ProjSpace.frameUnit, ProjSpace.frameUnit, restrictFun_app_pullAway ι B ι' e hcomp i _ h₁ h₂,
    toB_ratio]

theorem restrictFun_app_eq {U V : Z.Opens} (hVU : V ≤ U) {W' : Z'.Opens} (h₁ : W' ≤ e ⁻¹ᵁ V) (h₂ :
  W' ≤ e ⁻¹ᵁ U)
    (x : Γ(Z, U)) :
    ProjSpace.restrictFun h₁ ((e.app V).hom (ProjSpace.restrictFun hVU x)) = ProjSpace.restrictFun
      h₂ ((e.app U).hom x) := by
  have := congrArg (fun ψ => ψ.hom x) (e.naturality (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  erw [this]
  change (Z'.presheaf.map _ ≫ Z'.presheaf.map _).hom _ = (Z'.presheaf.map _).hom _
  rw [← Functor.map_comp]
  rfl
omit [IsAffineHom ι] [IsAffineHom ι'] in
theorem preimage_pullbackChart (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (j : Fin (n + 1)) :
    e ⁻¹ᵁ ProjSpace.pullbackChart ι j = ProjSpace.pullbackChart ι' j := by
  rw [ProjSpace.pullbackChart_eq, ProjSpace.pullbackChart_eq, ← Scheme.Hom.comp_preimage, hcomp,
    Scheme.Hom.comp_preimage, ProjSpace.map_preimage_basicOpen_X]

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback in
open P2mWs6C3 renaming preimage_inter → baseChange_preimage_inter in
theorem preimage_inter (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) {i : ℕ} (s :
  (ProjSpace.stdCoverPullback ι).Idx i) :
    e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s = (ProjSpace.stdCoverPullback ι').inter s := by
  exact baseChange_preimage_inter ι B ι' e hcomp s

theorem toB_mk (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ 𝒜A d) :
    toB (A := A) B i (HomogeneousLocalization.mk
      ({ deg := d, num := ⟨F, hF⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
           (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜A (Submonoid.powers (MvPolynomial.X i))))
    = HomogeneousLocalization.mk
      ({ deg := d,
         num := ⟨MvPolynomial.map (algebraMap A B) F,
           ((MvPolynomial.mem_homogeneousSubmodule d F).mp hF).map _⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
           (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜B (Submonoid.powers (MvPolynomial.X i))) := by
  have step : Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) (HomogeneousLocalization.mk
      ({ deg := d, num := ⟨F, hF⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
           (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜A (Submonoid.powers (MvPolynomial.X i))))
      = HomogeneousLocalization.mk
        ({ deg := d, num := ⟨(ProjSpace.mvMapGraded A B n) F, Graded.map_mem _ hF⟩,
           den := ⟨(ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) ^ d, by
             rw [ProjSpace.mvMapGraded_X]
             exact (MvPolynomial.mem_homogeneousSubmodule d _).mpr
               (MvPolynomial.isHomogeneous_X_pow i d)⟩,
           den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜B (Submonoid.powers ((ProjSpace.mvMapGraded A B
             n) (MvPolynomial.X i)))) := by
    apply HomogeneousLocalization.val_injective
    rw [Away.map, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [map_pow]⟩
  apply HomogeneousLocalization.val_injective
  rw [toB, RingHom.comp_apply, step, val_awayMap_mk, HomogeneousLocalization.val_mk]
  simp only [one_pow, mul_one]
  rfl

end Pull

theorem subsingleton_HSucc_iff {R : Type} [CommRing R] {V : Scheme.{0}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (i : ℕ) :
    Subsingleton (F.HSucc K i) ↔ LinearMap.ker (F.d K (i + 1)) ≤ LinearMap.range (F.d K i) := by
  constructor
  · intro h x hx
    have : (Submodule.Quotient.mk ⟨x, hx⟩ : F.HSucc K i) = 0 := Subsingleton.elim _ _
    rw [Submodule.Quotient.mk_eq_zero] at this
    exact this
  · intro h
    refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on with | _ a =>
    induction b using Submodule.Quotient.induction_on with | _ b =>
    rw [Submodule.Quotient.eq]
    change (a - b).1 ∈ LinearMap.range (F.d K i)
    exact h (a - b).2

theorem subsingleton_cochain {R : Type} [CommRing R] {n : ℕ} {V : Scheme.{0}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (φ : V ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
      [IsAffineHom φ]
    (i : ℕ) (hi : n + 1 ≤ i) : Subsingleton (F.cochain (ProjSpace.stdCoverPullback φ) i) := by
  have : IsEmpty ((ProjSpace.stdCoverPullback φ).Idx i) := ⟨fun s => by
    have := Fintype.card_le_of_injective _ s.2.injective
    have hc : Fintype.card (ProjSpace.stdCoverPullback φ).ι = n + 1 := by
      change Fintype.card (ULift (Fin (n + 1))) = n + 1
      rw [Fintype.card_ulift, Fintype.card_fin]
    rw [Fintype.card_fin, hc] at this
    omega⟩
  infer_instance

end P2mWs6C0

end AlgebraicCurves.Hilbert.Proofs.HilbertNoetherianCover

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Hilbert.Proofs.HilbertNoetherianCover in
open P2mWs6C0 _root_.AlgebraicGeometry.ProjSpace in
theorem exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing
    (n : ℕ) (A : Type) [CommRing A] [IsNoetherianRing A]
    (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ ProjSpace.π A n)) :
    ∃ (J : Type) (_ : Fintype J) (r : J → A), Ideal.span (Set.range r) = ⊤ ∧
      ∀ j : J, ∃ (P : Polynomial ℚ)
        (_ : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
          (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
          ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ))
        (D₀ : ℕ), ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], IsUnit (algebraMap A k (r
          j)) →
          ∀ (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
            (e : Zk ⟶ Z),
            IsClosedImmersion ιk →
            IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
              (algebraMap A k))) →
            e ≫ ι = ιk ≫ ProjSpace.map A k n →
            ∀ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
              (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) →
              (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
                (F ∈ I ↔ ∀ i : Fin (n + 1),
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                    (MvPolynomial.X i)))
                    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                      (MvPolynomial.X i)
                      (HomogeneousLocalization.mk
                        { deg := d
                          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d
                            _).mpr
                            (MvPolynomial.isHomogeneous_X_pow i d)⟩
                          den_mem := ⟨d, rfl⟩ })) = 0)) →
              ∀ d : ℕ, D₀ ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ) := by
  classical
  have := hι
  have := hfl
  obtain ⟨m₀, hm₀⟩ := AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist ι (ι ≫
    ProjSpace.π A n) rfl
  obtain ⟨d₂, hd₂⟩ :=
    exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion ι
  have core : ∀ d : ℕ, max m₀ d₂ ≤ d →
      (Module.Flat A ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback
        ι)) ∧
        (∀ (B : Type) [CommRing B] [Algebra A B],
          Function.Bijective (TwoChartCech.kerBaseChangeHom ((ProjSpace.twist (ι ≫ ProjSpace.π A n)
            ι d).d (ProjSpace.stdCoverPullback ι) 0) B)) ∧
        (∀ (B : Type) [CommRing B] [Algebra A B] (i : ℕ),
          LinearMap.ker (((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback
            ι) (i + 1)).baseChange B) ≤
            LinearMap.range (((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d
              (ProjSpace.stdCoverPullback ι) i).baseChange B))) ∧
      Module.Finite A ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback
        ι)) := by
    intro d hd
    have hd0 : m₀ ≤ d := le_of_max_le_left hd
    have hd2 : d₂ ≤ d := le_of_max_le_right hd
    have hex : ∀ i : ℕ, LinearMap.ker ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d
      (ProjSpace.stdCoverPullback ι) (i + 1)) ≤ LinearMap.range ((ProjSpace.twist (ι ≫ ProjSpace.π
      A n) ι d).d (ProjSpace.stdCoverPullback ι) i) :=
      fun i => (subsingleton_HSucc_iff _ _ i).1 (hm₀ d hd0 i)
    have : ∀ i : ℕ, Module.Flat A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
      (ProjSpace.stdCoverPullback ι) i) := fun i => flat_cochain ι d i
    have hC1 := Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range (fun i
      => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i)
      (fun i => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) i)
        (fun i => AlgebraicGeometry.OModulePresheaf.d_comp_d (ProjSpace.twist (ι ≫ ProjSpace.π A n)
        ι d) (ProjSpace.stdCoverPullback ι) i) (n + 1)
      (fun i hi => subsingleton_cochain (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d) ι i hi) hex
    refine ⟨hC1, ?_⟩
    obtain ⟨θ, hθval, -⟩ :=
      AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ι d (k
      := A)
    let r0 : ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ⊤ →ₗ[A] (ProjSpace.twist (ι ≫ ProjSpace.π
      A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0 :=
      LinearMap.pi (fun s => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).res (le_top :
        (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤))
    have hsub : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι) ≤
      LinearMap.range (r0 ∘ₗ θ) := by
      intro c hc
      obtain ⟨F, hF, hcF⟩ := hd₂ d hd2 c hc
      refine ⟨⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩, ?_⟩
      funext s
      apply ProjSpace.twistObj.ext
      funext j
      change ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).res (le_top : (ProjSpace.stdCoverPullback
        ι).inter s ≤ ⊤) (θ ⟨F, _⟩)).val j = (c s).val j
      rw [ProjSpace.twist_res_val]
      exact (congrArg (ProjSpace.restrictFun
          (inf_le_inf_right (ProjSpace.pullbackChart ι j)
            (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤))) (hθval F hF j)).trans
        ((ProjSpace.restrictFun_restrictFun
          (inf_le_inf_right (ProjSpace.pullbackChart ι j)
            (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤)) inf_le_right _).trans
          (hcF s j).symm)
    have hle : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d ≤
      MvPolynomial.restrictTotalDegree (Fin (n + 1)) A d := by
      intro p hp
      rw [MvPolynomial.mem_restrictTotalDegree]
      exact ((MvPolynomial.mem_homogeneousSubmodule d p).mp hp).totalDegree_le
    have : Module.Finite A ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) :=
      Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    exact Module.Finite.of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)
  have key : ∃ (D₁ : ℕ) (ρ : ℕ → PrimeSpectrum A → ℕ), (∀ d, D₁ ≤ d → IsLocallyConstant (ρ d)) ∧
      ∀ (d : ℕ), D₁ ≤ d → ∀ (k : Type) [Field k] [Algebra A k]
        (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (e :
          Zk ⟶ Z)
        [IsClosedImmersion ιk],
        IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
          (algebraMap A k))) →
        e ≫ ι = ιk ≫ ProjSpace.map A k n →
        (∀ i : ℕ, Subsingleton ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).HSucc
          (ProjSpace.stdCoverPullback ιk) i)) ∧
        (Module.finrank k ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
          (ProjSpace.stdCoverPullback ιk)) = ρ d ⟨RingHom.ker (algebraMap A k), RingHom.ker_isPrime
          _⟩) ∧
        ∀ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
          (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) →
          (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ I ↔ ∀ i : Fin (n + 1),
          (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
            (MvPolynomial.X i)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
              i)
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                    (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ })) = 0)) →
          Module.finrank k (piece I d) = ρ d ⟨RingHom.ker (algebraMap A k), RingHom.ker_isPrime _⟩
            := by
    refine ⟨max m₀ d₂, fun d P => Module.rankAtStalk (↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι
      d).H0 (ProjSpace.stdCoverPullback ι))) P, ?_, ?_⟩
    · intro d hd
      obtain ⟨⟨hflatH0, -, -⟩, hfin⟩ := core d hd
      have := hflatH0; have := hfin
      have : Module.FinitePresentation A ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0
        (ProjSpace.stdCoverPullback ι)) := Module.finitePresentation_of_finite A _
      exact Module.isLocallyConstant_rankAtStalk
    intro d hd k _ _ Zk ιk e _ hpbk hcompk
    obtain ⟨⟨hflatH0, hbij, hexB⟩, hfin⟩ := core d hd
    have := hflatH0; have := hfin
    have hd2 : d₂ ≤ d := le_of_max_le_right hd
    obtain ⟨θA, hθAval, -⟩ :=
      AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ι d (k
      := A)
    obtain ⟨ε, hεd, hεval⟩ :=
      AlgebraicGeometry.ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback ι k ιk
      e hpbk hcompk d
    have hεd' : ∀ (i : ℕ) (y), ε (i + 1) (((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d
      (ProjSpace.stdCoverPullback ι) i).baseChange k y) = (ProjSpace.twist (ιk ≫ ProjSpace.π k n)
      ιk d).d (ProjSpace.stdCoverPullback ιk) i (ε i y) :=
      fun i y => LinearMap.congr_fun (hεd i) y
    have ha : ∀ i : ℕ, Subsingleton ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).HSucc
      (ProjSpace.stdCoverPullback ιk) i) := by
      intro i
      rw [subsingleton_HSucc_iff]
      intro x hx
      obtain ⟨y, rfl⟩ := (ε (i + 1)).surjective x
      have hy : ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) (i +
        1)).baseChange k y = 0 := by
        apply (ε (i + 2)).injective
        rw [hεd', map_zero]
        exact hx
      obtain ⟨z, rfl⟩ := hexB k i hy
      exact ⟨ε i z, (hεd' i z).symm⟩
    let eK : ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk))
      ≃ₗ[k] k ⊗[A] ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι))
      := by
      refine (LinearEquiv.ofSubmodules (ε 0).symm _ _ ?_).trans
        (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom ((ProjSpace.twist (ι ≫ ProjSpace.π
          A n) ι d).d (ProjSpace.stdCoverPullback ι) 0) k) (hbij k)).symm
      apply le_antisymm
      · rintro y ⟨x, hx, rfl⟩
        change ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι)
          0).baseChange k ((ε 0).symm x) = 0
        apply (ε 1).injective
        rw [hεd', LinearEquiv.apply_symm_apply, map_zero]
        exact hx
      · intro y hy
        refine ⟨ε 0 y, ?_, (ε 0).symm_apply_apply y⟩
        change (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).d (ProjSpace.stdCoverPullback ιk) 0
          (ε 0 y) = 0
        rw [← hεd', show ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback
          ι) 0).baseChange k y = 0 from hy, map_zero]
    have hb : Module.finrank k ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
      (ProjSpace.stdCoverPullback ιk))
        = Module.rankAtStalk (↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0
          (ProjSpace.stdCoverPullback ι))) ⟨RingHom.ker (algebraMap A k), RingHom.ker_isPrime _⟩ :=
          by
      rw [eK.finrank_eq, finrank_baseChange_eq_rankAtStalk]
    refine ⟨ha, hb, ?_⟩
    intro I hIhom hIcl
    obtain ⟨θk, hθkval, hθkiff⟩ :=
      AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ιk d (k
      := k)
    let r0k : ProjSpace.twistObj (ιk ≫ ProjSpace.π k n) ιk d ⊤ →ₗ[k] (ProjSpace.twist (ιk ≫
      ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback ιk) 0 :=
      LinearMap.pi (fun s => (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).res (le_top :
        (ProjSpace.stdCoverPullback ιk).inter s ≤ ⊤))
    let ck : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k] (ProjSpace.twist (ιk ≫
      ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback ιk) 0 := r0k ∘ₗ θk
    have hck : ∀ p s, ck p s = (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).res (le_top :
      (ProjSpace.stdCoverPullback ιk).inter s ≤ ⊤) (θk p) := fun _ _ => rfl
    have hsingle : ∀ j : Fin (n + 1), ∃ s : (ProjSpace.stdCoverPullback ιk).Idx 0,
      ProjSpace.pullbackChart ιk j ≤ (ProjSpace.stdCoverPullback ιk).inter s := by
      intro j
      refine ⟨⟨fun _ => ⟨j⟩, fun a b h => absurd h (by omega)⟩, ?_⟩
      refine le_iInf fun t => ?_
      rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U, ProjSpace.pullbackChart_eq]
    have hr0k_inj : ∀ g, r0k g = 0 → g = 0 := by
      intro g hg
      apply ProjSpace.twistObj.ext
      funext j
      obtain ⟨s, hs⟩ := hsingle j
      have hs0 : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).res (le_top :
        (ProjSpace.stdCoverPullback ιk).inter s ≤ ⊤) g = 0 := congr_fun hg s
      have h1 : ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).res (le_top :
        (ProjSpace.stdCoverPullback ιk).inter s ≤ ⊤) g).val j = 0 := by
        rw [hs0]; rfl
      rw [ProjSpace.twist_res_val] at h1
      have h2 : (⊤ : Zk.Opens) ⊓ ProjSpace.pullbackChart ιk j ≤ (ProjSpace.stdCoverPullback
        ιk).inter s ⊓ ProjSpace.pullbackChart ιk j :=
        le_inf (inf_le_right.trans hs) inf_le_right
      have := congrArg (ProjSpace.restrictFun h2) h1
      rw [ProjSpace.restrictFun_restrictFun, map_zero] at this
      rw [ProjSpace.twistObj.zero_val, Pi.zero_apply, ← this]
      exact (ProjSpace.restrictFun_refl _).symm
    have hker : LinearMap.ker ck = Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      k d).subtype (I.restrictScalars k) := by
      ext p
      obtain ⟨F, hFmem⟩ := p
      have hF : F.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d F).mp hFmem
      rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
        Submodule.restrictScalars_mem]
      change ck ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 ↔ F ∈ I
      rw [hIcl d F hF, ← (hθkiff F hF)]
      constructor
      · intro h; exact hr0k_inj _ h
      · intro h; change r0k (θk _) = 0; rw [h, map_zero]
    have hrange_le : LinearMap.range ck ≤ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
      (ProjSpace.stdCoverPullback ιk) := by
      rintro _ ⟨p, rfl⟩
      change (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).d (ProjSpace.stdCoverPullback ιk) 0
        (ck p) = 0
      funext s
      rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, hck]
      let T := ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d
      let K := ProjSpace.stdCoverPullback ιk
      change T.res (K.inter_le_inter_face s 0) (T.res le_top (θk p)) +
        -T.res (K.inter_le_inter_face s 1) (T.res le_top (θk p)) = (0 : T.obj (K.inter s))
      exact (congrArg₂ (fun x y : T.obj (K.inter s) => x + -y)
        (T.res_res (K.inter_le_inter_face s 0) le_top (θk p))
        (T.res_res (K.inter_le_inter_face s 1) le_top (θk p))).trans
        (add_neg_cancel (T.res (le_top : K.inter s ≤ ⊤) (θk p)))
    have hnat : ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
        ε 0 ((1 : k) ⊗ₜ[A] (fun s => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).res (le_top :
          (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤)
          (θA ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩)))
        = ck ⟨MvPolynomial.map (algebraMap A k) F, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
          (hF.map _)⟩ := by
      intro F hF
      funext s
      apply ProjSpace.twistObj.ext
      funext j
      have hj : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk j ≤ e ⁻¹ᵁ
        ProjSpace.pullbackChart ι j := by
        rw [preimage_pullbackChart ι k ιk e hcompk]; exact inf_le_right
      have h : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk j ≤ e ⁻¹ᵁ
        ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) :=
        show _ ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) from
          le_inf (inf_le_left.trans (preimage_inter ι k ιk e hcompk s).ge) hj
      rw [hεval 0 _ s j h, hck]
      change ProjSpace.restrictFun h ((e.app _) (((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).res
        (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤) (θA ⟨F, _⟩)).val j)) =
        ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).res (le_top : (ProjSpace.stdCoverPullback
          ιk).inter s ≤ ⊤) (θk ⟨MvPolynomial.map (algebraMap A k) F, _⟩)).val j
      let a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
        (MvPolynomial.X j) :=
        HomogeneousLocalization.mk
          { deg := d
            num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
            den := ⟨MvPolynomial.X j ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
              (MvPolynomial.isHomogeneous_X_pow j d)⟩
            den_mem := ⟨d, rfl⟩ }
      let aK : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (MvPolynomial.X j) :=
        HomogeneousLocalization.mk
          { deg := d
            num := ⟨MvPolynomial.map (algebraMap A k) F,
              (MvPolynomial.mem_homogeneousSubmodule d _).mpr (hF.map _)⟩
            den := ⟨MvPolynomial.X j ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
              (MvPolynomial.isHomogeneous_X_pow j d)⟩
            den_mem := ⟨d, rfl⟩ }
      let xA : Γ(Z, ProjSpace.pullbackChart ι j) :=
        (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X
          j)))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X
            j) a)
      let xK : Γ(Zk, ProjSpace.pullbackChart ιk j) :=
        (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
          j)))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
            j) aK)
      have hA : (((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).res
          (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤)
          (θA ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩)).val j) =
          ProjSpace.restrictFun inf_le_right xA :=
        (congrArg (ProjSpace.restrictFun
          (inf_le_inf_right (ProjSpace.pullbackChart ι j)
            (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤))) (hθAval F hF j)).trans
          (ProjSpace.restrictFun_restrictFun
            (inf_le_inf_right (ProjSpace.pullbackChart ι j)
              (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤)) inf_le_right xA)
      have hK : (((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).res
          (le_top : (ProjSpace.stdCoverPullback ιk).inter s ≤ ⊤)
          (θk ⟨MvPolynomial.map (algebraMap A k) F,
            (MvPolynomial.mem_homogeneousSubmodule d _).mpr (hF.map _)⟩)).val j) =
          ProjSpace.restrictFun inf_le_right xK :=
        (congrArg (ProjSpace.restrictFun
          (inf_le_inf_right (ProjSpace.pullbackChart ιk j)
            (le_top : (ProjSpace.stdCoverPullback ιk).inter s ≤ ⊤)))
          (hθkval (MvPolynomial.map (algebraMap A k) F) (hF.map _) j)).trans
            (ProjSpace.restrictFun_restrictFun
              (inf_le_inf_right (ProjSpace.pullbackChart ιk j)
                (le_top : (ProjSpace.stdCoverPullback ιk).inter s ≤ ⊤)) inf_le_right xK)
      have ha : toB (A := A) k j a = aK :=
        toB_mk (A := A) k j d F ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF)
      have hbase : ProjSpace.restrictFun hj ((e.app (ProjSpace.pullbackChart ι j)).hom xA) =
          ProjSpace.restrictFun inf_le_right xK :=
        (restrictFun_app_pullAway ι k ιk e hcompk j a hj inf_le_right).trans
          (congrArg (fun z : HomogeneousLocalization.Away
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X j) =>
            ProjSpace.restrictFun (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓
                ProjSpace.pullbackChart ιk j ≤ ProjSpace.pullbackChart ιk j)
              ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X j)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                  (MvPolynomial.X j) z))) ha)
      exact (congrArg (fun z : Γ(Z, (ProjSpace.stdCoverPullback ι).inter s ⊓
        ProjSpace.pullbackChart ι j) =>
          ProjSpace.restrictFun h ((e.app _).hom z)) hA).trans
        ((restrictFun_app_eq e inf_le_right h hj xA).trans (hbase.trans hK.symm))
    have hrange_ge : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback
      ιk) ≤ LinearMap.range ck := by
      intro x hx
      have hy : ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι)
        0).baseChange k ((ε 0).symm x) = 0 := by
        apply (ε 1).injective
        rw [hεd', LinearEquiv.apply_symm_apply, map_zero]
        exact hx
      obtain ⟨t, ht⟩ := (hbij k).2 ⟨(ε 0).symm x, hy⟩
      have hx' : x = ε 0 ((TwoChartCech.kerBaseChangeHom ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι
        d).d (ProjSpace.stdCoverPullback ι) 0) k t : k ⊗[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n)
        ι d).cochain (ProjSpace.stdCoverPullback ι) 0)) := by
        rw [ht]; exact ((ε 0).apply_symm_apply x).symm
      rw [hx', TwoChartCech.kerBaseChangeHom_apply_coe]
      clear hx' ht hy hx
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
      | tmul c g =>
        rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
        obtain ⟨F, hF, hgF⟩ := hd₂ d hd2 g.1 g.2
        have hg : (g : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
          (ProjSpace.stdCoverPullback ι) 0) = fun s => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι
          d).res (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤)
            (θA ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩) := by
          funext s
          apply ProjSpace.twistObj.ext
          funext j
          rw [ProjSpace.twist_res_val]
          exact ((congrArg (ProjSpace.restrictFun
              (inf_le_inf_right (ProjSpace.pullbackChart ι j)
                (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤))) (hθAval F hF j)).trans
            ((ProjSpace.restrictFun_restrictFun
              (inf_le_inf_right (ProjSpace.pullbackChart ι j)
                (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤)) inf_le_right _).trans
                  (hgF s j).symm)).symm
        have hc : c ⊗ₜ[A] (g : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
          (ProjSpace.stdCoverPullback ι) 0) = c • ((1 : k) ⊗ₜ[A] (g : (ProjSpace.twist (ι ≫
          ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hc, LinearEquiv.map_smul, hg, hnat F hF]
        exact Submodule.smul_mem _ c (LinearMap.mem_range_self ck _)
    have hrange : LinearMap.range ck = (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
      (ProjSpace.stdCoverPullback ιk) := le_antisymm hrange_le hrange_ge
    beta_reduce
    rw [← hb]
    calc Module.finrank k (piece I d)
        = Module.finrank k (↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) ⧸ LinearMap.ker
          ck) :=
          (Submodule.quotEquivOfEq _ _ hker.symm).finrank_eq
      _ = Module.finrank k ↥(LinearMap.range ck) := ck.quotKerEquivRange.finrank_eq
      _ = Module.finrank k ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
        (ProjSpace.stdCoverPullback ιk)) := (LinearEquiv.ofEq _ _ hrange).finrank_eq
  obtain ⟨D₁, ρ, hρlc, hkey⟩ := key
  let v : PrimeSpectrum A → (Fin (n + 1) → ℕ) := fun P i => ρ (D₁ + i) P
  have hv : IsLocallyConstant v := by
    rw [IsLocallyConstant.iff_continuous]
    exact continuous_pi fun i => (IsLocallyConstant.iff_continuous _).1 (hρlc (D₁ + i)
      (Nat.le_add_right _ _))
  obtain ⟨J, hJ, r, hspan, hJv⟩ := cover v hv
  refine ⟨J, hJ, r, hspan, fun j => ?_⟩
  obtain ⟨P₀, hP₀, hvP⟩ := hJv j
  obtain ⟨k₀, _, _, _, hk₀⟩ := geompt P₀
  let Zk₀ : Scheme.{0} := pullback ι (ProjSpace.map A k₀ n)
  let ιk₀ : Zk₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k₀) := pullback.snd ι
    (ProjSpace.map A k₀ n)
  let e₀ : Zk₀ ⟶ Z := pullback.fst ι (ProjSpace.map A k₀ n)
  have hιk₀ : IsClosedImmersion ιk₀ := inferInstance
  have hsq₀ : IsPullback e₀ (ιk₀ ≫ ProjSpace.π k₀ n) (ι ≫ ProjSpace.π A n)
      (Spec.map (CommRingCat.ofHom (algebraMap A k₀))) :=
    (IsPullback.of_hasPullback ι (ProjSpace.map A k₀ n)).paste_vert
      (AlgebraicGeometry.ProjSpace.isPullback_map A k₀ n)
  have hcompat₀ : e₀ ≫ ι = ιk₀ ≫ ProjSpace.map A k₀ n := pullback.condition
  obtain ⟨I₀, hI₀hom, hI₀cl, -⟩ :=
    exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial n k₀ Zk₀ ιk₀ hιk₀
  obtain ⟨Pj, hPjdeg, hPj⟩ :=
    exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
      ιk₀ D₁ (fun d hd => (hkey d hd k₀ Zk₀ ιk₀ e₀ hsq₀ hcompat₀).1)
  have hpt₀ : (⟨RingHom.ker (algebraMap A k₀), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = P₀ := by
    ext1; exact hk₀
  have hρPj : ∀ d : ℕ, D₁ ≤ d → (ρ d P₀ : ℚ) = Pj.eval (d : ℚ) := by
    intro d hd
    rw [← hPj d hd, ← hpt₀, (hkey d hd k₀ Zk₀ ιk₀ e₀ hsq₀ hcompat₀).2.1]
  refine ⟨Pj, ⟨k₀, inferInstance, I₀, hI₀hom, D₁, fun d hd => ?_⟩, D₁, ?_⟩
  · rw [(hkey d hd k₀ Zk₀ ιk₀ e₀ hsq₀ hcompat₀).2.2 I₀ hI₀hom hI₀cl, hpt₀]
    exact hρPj d hd
  intro k _ _ _ hunit Zk ιk e hιk hpbk hcompk I hIhom hIcl d hd
  have := hιk
  have hPt : r j ∉ (⟨RingHom.ker (algebraMap A k), RingHom.ker_isPrime _⟩ : PrimeSpectrum
    A).asIdeal := fun h => by
    have h' : algebraMap A k (r j) = 0 := h
    exact hunit.ne_zero h'
  obtain ⟨Pk, hPkdeg, hPk⟩ :=
    exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
      ιk D₁ (fun d' hd' => (hkey d' hd' k Zk ιk e hpbk hcompk).1)
  have hρPk : ∀ d' : ℕ, D₁ ≤ d' →
      (ρ d' ⟨RingHom.ker (algebraMap A k), RingHom.ker_isPrime _⟩ : ℚ) = Pk.eval (d' : ℚ) := by
    intro d' hd'
    rw [← hPk d' hd', (hkey d' hd' k Zk ιk e hpbk hcompk).2.1]
  have hPkPj : Pk = Pj := by
    have hcard : ((Finset.univ : Finset (Fin (n + 1))).image (fun i : Fin (n + 1) => ((D₁ + (i : ℕ)
      : ℕ) : ℚ))).card
        = n + 1 := by
      rw [Finset.card_image_of_injective _ (fun i j h => by
        have : (D₁ + (i : ℕ) : ℕ) = D₁ + (j : ℕ) := by exact_mod_cast h
        exact Fin.ext (by omega)), Finset.card_univ, Fintype.card_fin]
    have hdeglt : ∀ Q : Polynomial ℚ, Q.natDegree ≤ n →
        Q.degree < ((Finset.univ : Finset (Fin (n + 1))).image (fun i : Fin (n + 1) => ((D₁ + (i :
          ℕ) : ℕ) : ℚ))).card := by
      intro Q hQ
      rw [hcard]
      exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hQ)
        (by exact_mod_cast Nat.lt_succ_self n)
    apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq _ (hdeglt Pk hPkdeg) (hdeglt Pj hPjdeg)
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    have h1 := hρPk (D₁ + i) (Nat.le_add_right _ _)
    have h2 := hρPj (D₁ + i) (Nat.le_add_right _ _)
    have hvv : v ⟨RingHom.ker (algebraMap A k), RingHom.ker_isPrime _⟩ i = v P₀ i :=
      by rw [hvP _ hPt]
    simp only [v] at hvv
    rw [← h1, ← h2]
    exact_mod_cast hvv
  rw [(hkey d hd k Zk ιk e hpbk hcompk).2.2 I hIhom hIcl, hρPk d hd, hPkPj]
end AlgebraicGeometry.HilbertFunctor
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module
open PresheafOfModules in
open PresheafOfModules.InternalHom in
attribute [-instance]
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
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
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
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
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulFamilies
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleFamilies
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq
  AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val
  AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val
  AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
attribute [-simp] PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
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
