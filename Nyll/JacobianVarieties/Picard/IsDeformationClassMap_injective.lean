/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.LinearCombination
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.JacobianVarieties.Picard.RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul

/-!
# Injectivity of deformation classes from changes of local frames.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DeformationInjectivity
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
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
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Spec
  Scheme
  Scheme.Modules
  Scheme.Modules.map_smul
  Scheme.TwoAffineOpenCover
  Scheme.Modules.IsFrameOn
  Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  dualNumberThickening
  oneAddEpsMul
  H1StructureSheaf
  IsDeformationClassMap
  RigKerDualNumber
  RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul)

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

/-- Multiplication by a unit preserves a local frame. -/
theorem isFrameOn_smul_of_isUnit {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (hs : Scheme.Modules.IsFrameOn s V) {u : Γ(X, U)} (hu : IsUnit u) :
    Scheme.Modules.IsFrameOn (u • s) V := by
  intro W hWU hWV
  have hb := hs hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op (u • s) =
      X.presheaf.map (homOfLE hWU).op u • M.presheaf.map (homOfLE hWU).op s :=
    Scheme.Modules.map_smul M (homOfLE hWU) u s
  simp only [e]
  have hu' : IsUnit (X.presheaf.map (homOfLE hWU).op u) := hu.map _
  have : (fun g : Γ(X, W) => g • (X.presheaf.map (homOfLE hWU).op u • M.presheaf.map (homOfLE
    hWU).op s)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘ (fun g => g * X.presheaf.map
        (homOfLE hWU).op u) := by
    funext g
    simp only [Function.comp_apply, mul_smul]
  rw [this]
  exact hb.comp (hu'.unit.mulRight_bijective)

variable (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

/-- The transition unit sends addition of coefficients to multiplication. -/
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

/-- The zero coefficient gives the identity transition unit. -/
theorem oneAddEpsMul_zero : oneAddEpsMul A 𝒱 c 0 = 1 := by
  erw [oneAddEpsMul, map_zero, mul_zero, add_zero]

/-- The transition units of opposite coefficients are multiplicative inverses. -/
theorem oneAddEpsMul_mul_neg (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c (-f) = 1 := by
  rw [← oneAddEpsMul_add, add_neg_cancel, oneAddEpsMul_zero]

/-- The transition units of opposite coefficients are inverse in the reverse order. -/
theorem oneAddEpsMul_neg_mul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    oneAddEpsMul A 𝒱 c (-f) * oneAddEpsMul A 𝒱 c f = 1 := by
  rw [mul_comm, oneAddEpsMul_mul_neg]

/-- The first chart restriction preserves the transition unit of a section. -/
theorem ρ0_one_add_eps_map0 (a : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0
        (1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map0 a) =
      oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) := by
  simp only [oneAddEpsMul, map_add, map_one, map_mul, AlgHom.commutes, HomOver.map01_ρ0]

/-- The second chart restriction preserves the transition unit of a section. -/
theorem ρ1_one_add_eps_map1 (a : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1
        (1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map1 a) =
      oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 a) := by
  simp only [oneAddEpsMul, map_add, map_one, map_mul, AlgHom.commutes, HomOver.map01_ρ1]

end AlgebraicGeometry.RelPicard

open _root_.AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard in
/-- Two rigidified deformations with the same deformation class are isomorphic. -/
theorem _root_.AlgebraicGeometry.RelPicard.IsDeformationClassMap.injective
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec
      (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    Function.Injective δ := by
  intro x y hxy
  induction x using Quotient.ind with
  | _ M =>
  induction y using Quotient.ind with
  | _ N =>
  obtain ⟨e₀, e₁, f, h₀, h₁, hM⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 M
  obtain ⟨e₀', e₁', f', h₀', h₁', hN⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 N
  rw [hδ M e₀ e₁ f h₀ h₁ hM, hδ N e₀' e₁' f' h₀' h₁' hN] at hxy
  obtain ⟨p, hp⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq _).1 hxy)
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r0_apply,
    TwoChartCech.Cover.lineBundle_r1_apply, Units.val_one, one_mul] at hp
  let u₀ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0 :=
    1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map0 p.1
  let u₁ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1 :=
    1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map1 p.2
  have hεnil : ∀ {S : Type u} [CommRing S] [Algebra (DualNumber A) S] (s : S),
      IsNilpotent (algebraMap (DualNumber A) S DualNumber.eps * s) := by
    intro S _ _ s
    refine ⟨2, ?_⟩
    rw [mul_pow, ← map_pow, pow_two, DualNumber.eps_mul_eps, map_zero, zero_mul]
  have hu₀ : IsUnit u₀ := (hεnil _).isUnit_one_add
  have hu₁ : IsUnit u₁ := (hεnil _).isUnit_one_add
  have h₀'' : Scheme.Modules.IsFrameOn ((show Γ(Limits.pullback c (specMap R (DualNumber A)),
      (𝒱.pullback c (DualNumber A)).U0) from u₀) • e₀') (𝒱.pullback c (DualNumber A)).U0 :=
    isFrameOn_smul_of_isUnit h₀' hu₀
  have h₁'' : Scheme.Modules.IsFrameOn ((show Γ(Limits.pullback c (specMap R (DualNumber A)),
      (𝒱.pullback c (DualNumber A)).U1) from u₁) • e₁') (𝒱.pullback c (DualNumber A)).U1 :=
    isFrameOn_smul_of_isUnit h₁' hu₁
  have hr₀ : (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
        (homOfLE (inf_le_left : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1
          ≤ _)).op
        (show Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U0)
          from u₀) =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
        oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 p.1)) :=
    ρ0_one_add_eps_map0 A 𝒱 c p.1
  have hr₁ : (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
        (homOfLE (inf_le_right : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber
          A)).U1 ≤ _)).op
        (show Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U1)
          from u₁) =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
        oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 p.2)) :=
    ρ1_one_add_eps_map1 A 𝒱 c p.2
  have hN' : N.1.L.presheaf.map (homOfLE inf_le_right).op ((show Γ(Limits.pullback c (specMap R
    (DualNumber A)),
        (𝒱.pullback c (DualNumber A)).U1) from u₁) • e₁') =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A
            𝒱 c f) •
        N.1.L.presheaf.map (homOfLE inf_le_left).op ((show Γ(Limits.pullback c (specMap R
          (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0) from u₀) • e₀') := by
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, hN, smul_smul, smul_smul, hr₀, hr₁]
    congr 1
    change oneAddEpsMul A 𝒱 c _ * oneAddEpsMul A 𝒱 c f' = oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c
      _
    rw [← oneAddEpsMul_add, ← oneAddEpsMul_add]
    congr 1
    linear_combination hp
  have flip : ∀ {L : (Limits.pullback c (specMap R (DualNumber A))).Modules}
      (s₀ : Γ(L, (𝒱.pullback c (DualNumber A)).U0)) (s₁ : Γ(L, (𝒱.pullback c (DualNumber A)).U1)),
      L.presheaf.map (homOfLE inf_le_right).op s₁ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul
              A 𝒱 c f) •
          L.presheaf.map (homOfLE inf_le_left).op s₀ →
      L.presheaf.map (homOfLE (inf_le_left : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c
        (DualNumber A)).U1 ≤ _)).op s₀ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul
              A 𝒱 c (-f)) •
          L.presheaf.map (homOfLE (inf_le_right : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c
            (DualNumber A)).U1 ≤ _)).op s₁ := by
    intro L s₀ s₁ h
    rw [h, smul_smul]
    have h1 : (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul
              A 𝒱 c (-f)) *
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul
              A 𝒱 c f) = 1 :=
      oneAddEpsMul_neg_mul A 𝒱 c f
    rw [h1, one_smul]
  obtain ⟨iso⟩ := Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul
    (𝒱.pullback c (DualNumber A)).sup_eq_top h₀ h₁ h₀'' h₁'' _ (flip e₀ e₁ hM) (flip _ _ hN')
  exact Quotient.sound ⟨iso⟩
end JacobianVarieties.Picard.Proofs.DeformationInjectivity
end ProofImplementation
