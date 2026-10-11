/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_forall_subsingleton_HSucc_twist
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensorPow
import Nyll.AlgebraicCurves.Foundations.Algebra.LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

/-!
# Vanishing of higher cohomology for tensor powers with a finite projective presentation
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
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
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
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
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace L7Head
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} {L : X.Modules}
  {N : ℕ}
  (𝔓 : L.ProjPresentation f N) (m : ℕ)

/-- The map from sections of a tensor power to sections of the associated projective twist. -/
def eK (U : X.Opens) : (OModulePresheaf.ofModules f (L.tensorPow m)).obj U →ₗ[k] (ProjSpace.twist f
  𝔓.toProj m).obj U where
  toFun x :=
    (Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj
    𝔓 m).choose U x
  map_add' x y := map_add _ x y
  map_smul' r x :=
    ((Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj
        𝔓 m).choose U).map_smul
      ((Scheme.TwoAffineOpenCover.algebraOfHom f U).algebraMap r) x

theorem eK_apply (U : X.Opens) (x : (OModulePresheaf.ofModules f (L.tensorPow m)).obj U) :
    eK 𝔓 m U x = (Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj
        𝔓 m).choose U x := rfl

theorem eK_res {U U' : X.Opens} (h : U ≤ U') (x : (OModulePresheaf.ofModules f (L.tensorPow m)).obj
  U') :
    eK 𝔓 m U ((OModulePresheaf.ofModules f (L.tensorPow m)).res h x) = (ProjSpace.twist f 𝔓.toProj
      m).res h (eK 𝔓 m U' x) :=
  (Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓
    m).choose_spec.2.1 U U' h x

theorem eK_bijective_inter [IsAffineHom 𝔓.toProj] {i : ℕ} (s : (ProjSpace.stdCoverPullback
  𝔓.toProj).Idx i) :
    Function.Bijective (eK 𝔓 m ((ProjSpace.stdCoverPullback 𝔓.toProj).inter s)) :=
  (Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓
    m).choose_spec.2.2 _ (s.1 0).down
    (iInf_le (fun j => (ProjSpace.stdCoverPullback 𝔓.toProj).U (s.1 j)) 0)

/--
The cochain equivalence induced by the comparison between a tensor power and the projective
twist.
-/
def cEquiv [IsAffineHom 𝔓.toProj] (i : ℕ) :
    (OModulePresheaf.ofModules f (L.tensorPow m)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i
      ≃ₗ[k] (ProjSpace.twist f 𝔓.toProj m).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i :=
  LinearEquiv.piCongrRight fun s => LinearEquiv.ofBijective (eK 𝔓 m _) (eK_bijective_inter 𝔓 m s)

theorem cEquiv_apply [IsAffineHom 𝔓.toProj] (i : ℕ) (c : (OModulePresheaf.ofModules f (L.tensorPow
  m)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) : cEquiv 𝔓 m i c s = eK 𝔓 m _ (c s) := rfl

theorem cEquiv_comm [IsAffineHom 𝔓.toProj] (i : ℕ) (c : (OModulePresheaf.ofModules f (L.tensorPow
  m)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i) :
    cEquiv 𝔓 m (i + 1) ((OModulePresheaf.ofModules f (L.tensorPow m)).d (ProjSpace.stdCoverPullback
      𝔓.toProj) i c)
      = (ProjSpace.twist f 𝔓.toProj m).d (ProjSpace.stdCoverPullback 𝔓.toProj) i (cEquiv 𝔓 m i c)
        := by
  funext s
  rw [cEquiv_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, eK_res, cEquiv_apply]

theorem nonempty_HSucc_equiv [IsAffineHom 𝔓.toProj] (i : ℕ) :
    Nonempty ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc (ProjSpace.stdCoverPullback
      𝔓.toProj) i
      ≃ₗ[k] (ProjSpace.twist f 𝔓.toProj m).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) :=
  (LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    (C := fun i => (OModulePresheaf.ofModules f (L.tensorPow m)).cochain
      (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (C' := fun i => (ProjSpace.twist f 𝔓.toProj m).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (fun i => (OModulePresheaf.ofModules f (L.tensorPow m)).d (ProjSpace.stdCoverPullback 𝔓.toProj)
      i)
    (fun i => (ProjSpace.twist f 𝔓.toProj m).d (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (cEquiv 𝔓 m) (fun i x => cEquiv_comm 𝔓 m i x)).2 i

end AlgebraicGeometry.L7Head

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry in
theorem
  AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj'
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (N : ℕ) (𝔓 : L.ProjPresentation f N) (hfin : IsFinite 𝔓.toProj) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ 𝒲 : X.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc 𝒲 0) := by
  have := hfin
  have : IsSeparated f := by
    rw [← 𝔓.toProj_π]
    unfold ProjSpace.π
    infer_instance
  obtain ⟨m₀, hm₀⟩ := AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist 𝔓.toProj f
    𝔓.toProj_π
  refine ⟨m₀, fun m hm 𝒲 => ?_⟩
  have : Subsingleton ((ProjSpace.twist f 𝔓.toProj m).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj)
    0) := hm₀ m hm 0
  obtain ⟨e⟩ := AlgebraicGeometry.L7Head.nonempty_HSucc_equiv 𝔓 m 0
  have h0 : Subsingleton ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc
    (ProjSpace.stdCoverPullback 𝔓.toProj) 0) :=
    e.toEquiv.subsingleton
  exact AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton f
    (L.tensorPow m)
    (hL.tensorPow m).exists_trivialization (ProjSpace.stdCoverPullback 𝔓.toProj) 𝒲 h0

end
end Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry.Scheme.Modules

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open
  Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj.AlgebraicGeometry
    renaming Scheme.Modules.exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj'
      → tensorPowVanishes in
theorem exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (N : ℕ) (𝔓 : L.ProjPresentation f N) (hfin : IsFinite 𝔓.toProj) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ 𝒲 : X.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc 𝒲 0) :=
  tensorPowVanishes k
    f L hL N 𝔓 hfin


end AlgebraicGeometry.Scheme.Modules
end ProofImplementation

open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup
  AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module
  AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
  ProjSpaceCech.GradedModule.H.module
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
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
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
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val
  AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val
  AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val
  AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
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
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
