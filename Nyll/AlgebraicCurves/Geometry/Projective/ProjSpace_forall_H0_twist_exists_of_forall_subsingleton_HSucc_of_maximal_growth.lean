/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero
import Nyll.AlgebraicCurves.Foundations.Polynomial.Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow

/-!
# Proj Space forall H0 twist exists of forall subsingleton HSucc of maximal growth
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

namespace RM4Sol

/-- The largest index up to `a + d + 1` whose binomial coefficient of order `d + 1` is at most
`a`. -/
def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) +
      Nat.macaulayPow d (a - (top d a).choose (d + 1)) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem one_le_macaulayPow {e a : ℕ} (he : 1 ≤ e) (ha : 1 ≤ a) : 1 ≤ Nat.macaulayPow e a := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  rw [macaulayPow_succ]
  have h1 : d < top d a := d_lt_top_of_pos d a ha
  have h2 : 1 ≤ (top d a + 1).choose (d + 2) := Nat.choose_pos (by omega)
  omega

section Theta

variable {n : ℕ} {k : Type} [Field k] {Zk : Scheme.{0}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk] (d :
    ℕ)

/-- The section on a pulled-back projective chart obtained from the homogeneous polynomial. -/
noncomputable def chartVal (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n
  + 1)) :
    Γ(Zk, ProjSpace.pullbackChart ιk i) :=
  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ }))

theorem isHomogeneous_of_mem (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    (F : MvPolynomial (Fin (n + 1)) k).IsHomogeneous d :=
  (MvPolynomial.mem_homogeneousSubmodule d _).mp F.2

/-- The degree-zero Cech index corresponding to the selected standard projective chart. -/
def vertex (i : Fin (n + 1)) : (ProjSpace.stdCoverPullback ιk).Idx 0 :=
  ⟨fun _ => ULift.up i, fun a b hab => absurd (Fin.lt_def.mp hab)
    (by have := a.isLt; have := b.isLt; omega)⟩

theorem chart_le_inter_vertex (i : Fin (n + 1)) :
    ProjSpace.pullbackChart ιk i ≤ (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓
      ProjSpace.pullbackChart ιk i :=
  le_inf (le_iInf fun _ => le_rfl) le_rfl

theorem exists_theta :
    ∃ Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)),
      ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback
          ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i
              ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i) := by
  obtain ⟨θ, hθ, -⟩ := ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ιk d
  let T := ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d
  let K := ProjSpace.stdCoverPullback ιk
  let Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k] T.cochain K 0 :=
    LinearMap.pi fun s => (T.res (le_top : K.inter s ≤ ⊤)).comp θ
  have hΘ₀ : ∀ F s, Θ₀ F s = T.res (le_top : K.inter s ≤ ⊤) (θ F) := fun F s => rfl
  have hcoc : ∀ F, Θ₀ F ∈ T.H0 K := by
    intro F
    rw [LinearMap.mem_ker]
    funext s
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, hΘ₀]
    change T.res (K.inter_le_inter_face s 0) (T.res le_top (θ F)) +
      -T.res (K.inter_le_inter_face s 1) (T.res le_top (θ F)) = (0 : T.obj (K.inter s))
    exact (congrArg₂ (fun x y : T.obj (K.inter s) => x + -y)
      (T.res_res (K.inter_le_inter_face s 0) le_top (θ F))
      (T.res_res (K.inter_le_inter_face s 1) le_top (θ F))).trans
      (add_neg_cancel (T.res (le_top : K.inter s ≤ ⊤) (θ F)))
  refine ⟨LinearMap.codRestrict (T.H0 K) Θ₀ hcoc, fun F s i => ?_⟩
  rw [LinearMap.codRestrict_apply, hΘ₀]
  change (ProjSpace.twistRes (ιk ≫ ProjSpace.π k n) ιk d (le_top : K.inter s ≤ ⊤) (θ F)).val i = _
  rw [ProjSpace.twistRes_val]
  have hF : (θ F).val i =
      ProjSpace.restrictFun (inf_le_right : (⊤ : Zk.Opens) ⊓ ProjSpace.pullbackChart ιk i ≤
        ProjSpace.pullbackChart ιk i) (chartVal ιk d F (isHomogeneous_of_mem d F) i) :=
    hθ F.1 (isHomogeneous_of_mem d F) i
  exact (congrArg (ProjSpace.restrictFun
      (inf_le_inf_right (ProjSpace.pullbackChart ιk i) (le_top : K.inter s ≤ ⊤))) hF).trans
    (ProjSpace.restrictFun_restrictFun
      (inf_le_inf_right (ProjSpace.pullbackChart ιk i) (le_top : K.inter s ≤ ⊤))
      inf_le_right (chartVal ιk d F (isHomogeneous_of_mem d F) i))

variable {ιk d}

theorem theta_eq_zero_iff
    (Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)))
    (hΘ : ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback
          ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i
              ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i))
    (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    Θ F = 0 ↔ ∀ i : Fin (n + 1), chartVal ιk d F (isHomogeneous_of_mem d F) i = 0 := by
  constructor
  · intro h i
    have h1 := hΘ F (vertex ιk i) i
    rw [h] at h1
    have h2 : ProjSpace.restrictFun (chart_le_inter_vertex ιk i)
        (ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓
            ProjSpace.pullbackChart ιk i ≤
            ProjSpace.pullbackChart ιk i)
          (chartVal ιk d F (isHomogeneous_of_mem d F) i)) = chartVal ιk d F (isHomogeneous_of_mem d
            F) i := by
      rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl _
    rw [← h2, ← h1]
    have hz : (((0 : ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback
      ιk))) :
        (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback ιk) 0)
          (vertex ιk i)).val i
        = 0 := rfl
    rw [hz, map_zero]
  · intro h
    apply Subtype.ext
    funext s
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hΘ, h i, map_zero]
    rfl

end Theta

end RM4Sol

end ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth
end AlgebraicCurves.Geometry.Projective.Proofs

namespace AlgebraicGeometry.ProjSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Projective.Proofs in
open ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth in
theorem forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth
    (n m : ℕ) (hm : 1 ≤ m) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank k (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J m)))
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
      [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin
          (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)))
    (hvan : ∀ d : ℕ, m ≤ d → (∀ i : ℕ, Subsingleton
          ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).HSucc (ProjSpace.stdCoverPullback ιk) i)))
            :
    ∀ d : ℕ, m ≤ d →
      (∀ c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk),
          ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
            ∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
              (c s).val i =
                ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart
                    ιk i ≤
                    ProjSpace.pullbackChart ιk i)
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                    (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) := by
  classical
  intro d hd c hc
  rcases Nat.eq_zero_or_pos (Module.finrank k (piece J m)) with ha0 | hapos
  · exact ((forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero
      n m k J ha0 Zk ιk hZ) d hd).2 c hc
  have hpers :=
    MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow n m
    hm k J hJ hmax
  obtain ⟨Q, hQ⟩ := Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
    (fun e => Module.finrank k (piece J e)) m hm hpers
  have hpos : ∀ e, m ≤ e → 1 ≤ Module.finrank k (piece J e) := by
    intro e he
    induction e, he using Nat.le_induction with
    | base => exact hapos
    | succ e he ih => rw [hpers e he]; exact RM4Sol.one_le_macaulayPow (hm.trans he) ih
  obtain ⟨P, -, hP⟩ :=
    exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
      ιk m hvan
  choose Θ hΘ using fun e => RM4Sol.exists_theta ιk e
  have hker : ∀ e, m ≤ e → LinearMap.ker (Θ e) =
      Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k e).subtype
        (J.restrictScalars k) := by
    intro e he
    ext F
    rw [LinearMap.mem_ker, RM4Sol.theta_eq_zero_iff (Θ e) (hΘ e) F, Submodule.mem_comap,
      Submodule.restrictScalars_mem]
    exact (hZ e he F.1 (RM4Sol.isHomogeneous_of_mem e F)).symm
  have hrank : ∀ e, m ≤ e → Module.finrank k (LinearMap.range (Θ e)) = Module.finrank k (piece J e)
    := by
    intro e he
    exact ((Θ e).quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ (hker e he))).finrank_eq
  have htop_of : ∀ e, (∀ c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk e).H0
    (ProjSpace.stdCoverPullback ιk),
        ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous e),
          ∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart
                  ιk i ≤
                  ProjSpace.pullbackChart ιk i)
                (RM4Sol.chartVal ιk e F hF i)) → LinearMap.range (Θ e) = ⊤ := by
    intro e hsurj
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨F, hF, hform⟩ := hsurj y hy
    refine ⟨⟨F, (MvPolynomial.mem_homogeneousSubmodule e F).mpr hF⟩, Subtype.ext (funext fun s =>
      ?_)⟩
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hΘ]
    exact (hform s i).symm
  obtain ⟨d₂, hd₂⟩ :=
    exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion ιk
  have hQP : Q = P := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => ((max m d₂ + j : ℕ) : ℚ))
      (fun a b h => by simpa using h) fun j => ?_
    have hm' : m ≤ max m d₂ + j := (le_max_left _ _).trans (Nat.le_add_right _ _)
    have hd' : d₂ ≤ max m d₂ + j := (le_max_right _ _).trans (Nat.le_add_right _ _)
    change Q.eval _ = P.eval _
    rw [← hQ _ hm', ← hP _ hm', ← hrank _ hm', htop_of _ (hd₂ _ hd'), finrank_top]
  have hfin : Module.finrank k (LinearMap.range (Θ d)) =
      Module.finrank k ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
        (ProjSpace.stdCoverPullback ιk)) := by
    have h1 := hQ d hd
    rw [hQP, ← hP d hd] at h1
    rw [hrank d hd]
    exact_mod_cast h1
  have : Module.Finite k ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
    (ProjSpace.stdCoverPullback ιk)) :=
    Module.finite_of_finrank_pos (by rw [← hfin, hrank d hd]; exact hpos d hd)
  have htop : LinearMap.range (Θ d) = ⊤ := Submodule.eq_top_of_finrank_eq hfin
  have hmem : (⟨c, hc⟩ : ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0
    (ProjSpace.stdCoverPullback ιk))) ∈
      LinearMap.range (Θ d) := htop ▸ Submodule.mem_top
  obtain ⟨F, hFc⟩ := hmem
  refine ⟨F.1, RM4Sol.isHomogeneous_of_mem d F, fun s i => ?_⟩
  have := hΘ d F s i
  rw [hFc] at this
  exact this
end AlgebraicGeometry.ProjSpace
end ProofImplementation
