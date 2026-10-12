/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.JacobianVarieties.Picard.nonempty_pullback_sectionTwist_iso_of_range_subset
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Nyll.AlgebraicCurves.Geometry.Picard.isInvertible_sectionIdeal_of_range_subset
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I_of_supportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso

/-!
# Supported Cartier divisors realizing a section twist
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SupportedTwistedDivisor
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
attribute [-simp]
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst

universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  SmoothOfRelativeDimension
  Scheme.Modules.pullback
  Scheme.Hom
  LocallyOfFiniteType
  Spec
  Scheme
  IsSeparated
  Scheme.Modules.pullbackCongr
  Scheme.Opens.ι_apply
  Scheme.Modules
  Scheme.Opens
  Scheme.Hom.comp_apply
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.IdealSheafData.module
  Scheme.IdealSheafData.invModule
  RelEffCartierDiv
  mapOnProdOver
  RelEffCartierDiv.pullbackAlong_comp
  Scheme.TwoAffineOpenCover
  RelEffCartierDiv.twistModule_def
  Scheme.Modules.rigidify
  Scheme.Modules.rigidifyMapIso
  Scheme.Modules.zeroSchemeIdeal
  Scheme.Modules.tensorTensorTensorComm
  Scheme.Modules.pullbackTensorObjIso
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
  Scheme.IdealSheafData.IsInvertible
  RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn
  Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  rigSection
  RigidifiedLineBundle
  fibreAt
  FibrewiseAlgEquivZero
  sectionIdeal
  sectionTwist
  fibreModule
  rigSection_snd
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
  nonempty_pullback_sectionTwist_iso_of_range_subset
  isInvertible_sectionIdeal_of_range_subset)

namespace K5bExistSS

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry



open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.JacobianVarieties.Picard.Proofs.SupportedTwistedDivisor.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.JacobianVarieties.Picard.Proofs.SupportedTwistedDivisor.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra


variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated
  c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))

include hεU in
/-- The section ideal is invertible over the smooth open containing the section. -/
theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  isInvertible_sectionIdeal_of_range_subset c ε U hεU u

include hεU in
/-- Every section twist is an invertible module. -/
theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε U hεU u).pow n).isInvertible_invModule

include hεU in
/-- Cancel the auxiliary divisor and the section twist after rigidification. -/
theorem nonempty_twistModule_iso
    {g e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LU : RigidifiedLineBundle c ε u) (DγU : RelEffCartierDiv c e u) (hDγU : DγU.SupportedIn U)
    (D₀ : RelEffCartierDiv c g u) (hD₀U : D₀.SupportedIn U) (D : RelEffCartierDiv c (g + e) u) (hD
      : D.I = D₀.I * DγU.I)
    (N : V.Modules) (hN : Scheme.Modules.IsInvertible N)
    (e₀ : D₀.lineBundle ≅ (LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) :
    Nonempty (D.twistModule c ε ≅ LU.L) := by
  have hsIr : ((sectionIdeal c ε u) ^ (g + e)).IsInvertible := (isInvertible_sectionIdeal R c ε U
    hεU u).pow _
  have hD₀ : D₀.I.IsInvertible := D₀.isInvertible_I_of_supportedIn U hD₀U
  have hDγ : DγU.I.IsInvertible := DγU.isInvertible_I_of_supportedIn U hDγU
  have i1 : D.lineBundle ≅ D₀.lineBundle ⊗ DγU.lineBundle :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ≪≫ (hD₀.nonempty_mul_invModule_iso_tensor
      hDγ).some
  have cST : sectionTwist c ε u (g + e) ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hsIr.isInvertible_module.dual).2.some
  have cγ : DγU.lineBundle ⊗ DγU.idealModule ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hDγ.isInvertible_module.dual).2.some
  have i3 : (((LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) ⊗ DγU.lineBundle) ⊗
        ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    (α_ _ _ _) ≪≫ ((β_ _ _) ⊗ᵢ (β_ _ _)) ≪≫ (α_ _ _ _) ≪≫
      (Iso.refl _ ⊗ᵢ ((α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ
        (Scheme.Modules.tensorTensorTensorComm _ _ _ _ ≪≫ (cST ⊗ᵢ ((β_ _ _) ≪≫ cγ)) ≪≫ (λ_ _))) ≪≫
          (ρ_ _)))
  have i4 : D.lineBundle ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    ((i1 ≪≫ (e₀ ⊗ᵢ Iso.refl _)) ⊗ᵢ Iso.refl _) ≪≫ i3
  have i5 : Scheme.Modules.rigidify (rigSection c u ε) (pullback.snd c u) LU.L ≅ LU.L :=
    (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified LU).some
  rw [RelEffCartierDiv.twistModule_def]
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ i4 ≪≫
    (Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso (rigSection_snd ε u) hN
      LU.isInvertible).some ≪≫
    i5⟩

include hεU in
/-- Transport vanishing of H1 and one-dimensional H0 to the restricted base. -/
theorem hfib_of_hU
    (r e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε
      t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t)
        s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H0 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H1)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (W.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
        ((L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L ⊗
          (sectionTwist c ε (W.ι ≫ t) r ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id
            _)).idealModule)))).H1 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
        ((L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L ⊗
          (sectionTwist c ε (W.ι ≫ t) r ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id
            _)).idealModule)))).H0 = 1 := by
  let ψ : SchemeHomOver (W.ι ≫ t) t := ⟨W.ι, rfl⟩
  set Mt : (pullback c t).Modules :=
    L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule) with hMt
  set Mu : (pullback c (W.ι ≫ t)).Modules := (L.pullbackAlong ψ).L ⊗
    (sectionTwist c ε (W.ι ≫ t) r ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule)
      with hMu
  have hβ : baseChangeSnd c ψ = pullback.lift (pullback.fst c (W.ι ≫ t) ≫ 𝟙 C) (pullback.snd c (W.ι
    ≫ t) ≫ W.ι)
      (by simp only [Category.comp_id, Category.assoc, pullback.condition]) := rfl
  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong W.ι ψ.2 =
      Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _) :=
    RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _
  have hI : (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id
    t)).idealModule ≅
      (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule := by
    have := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      ((Dγ.pullbackAlong t (Category.comp_id t)).isInvertible_I_of_supportedIn U (hDγ.pullbackAlong
        t _))
      (hI ▸ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).isInvertible_I_of_supportedIn U
        (hDγ.pullbackAlong _ _))
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison
      (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm
  have iM : Mu ≅ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj Mt :=
    (Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hεU ψ r).some.symm
      ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm
  let φ : pullback (pullback.snd c t) (s ≫ W.ι) ≅ pullback (pullback.snd c (W.ι ≫ t)) s :=
    pullbackLeftPullbackSndIso c t (s ≫ W.ι) ≪≫ pullback.congrHom rfl (Category.assoc s W.ι t) ≪≫
      (pullbackLeftPullbackSndIso c (W.ι ≫ t) s).symm
  have hφsnd : φ.hom ≫ fibreAt c (W.ι ≫ t) s = fibreAt c t (s ≫ W.ι) := by
    simp only [φ, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  have hφfst : φ.hom ≫ pullback.fst (pullback.snd c (W.ι ≫ t)) s ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s ≫ W.ι) := by
    rw [hβ]
    apply pullback.hom_ext
    · simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst,
        Category.comp_id,
        pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom,
          pullbackLeftPullbackSndIso_hom_fst]
    · simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc,
        pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
        Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]
  have eφ : fibreModule c t (s ≫ W.ι) Mt ≅ (Scheme.Modules.pullback φ.hom).obj (fibreModule c (W.ι
    ≫ t) s Mu) :=
    ((Scheme.Modules.pullbackCongr hφfst).app Mt).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.hom
      (pullback.fst (pullback.snd c (W.ι ≫ t)) s ≫ baseChangeSnd c ψ)).app Mt).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (W.ι ≫ t)) s) (baseChangeSnd c
        ψ)).app Mt).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)
  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s ≫ W.ι)) (fibreAt c (W.ι ≫ t) s) φ hφsnd 𝒲 (fibreModule c (W.ι ≫ t) s Mu)
      (fibreModule c t (s ≫ W.ι) Mt) eφ
  have hrange : Set.range ⇑(s ≫ W.ι) ⊆ (W : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply s W.ι x, Scheme.Opens.ι_apply (X := T) W (s x)]
    exact (s x).2
  have h1 : Subsingleton (𝒱.sectionsOf (fibreAt c t (s ≫ W.ι)) (fibreModule c t (s ≫ W.ι) Mt)).H1
    := hW k (s ≫ W.ι) hrange 𝒱
  have := h1
  refine ⟨e1.symm.toEquiv.subsingleton, ?_⟩
  rw [← hH0one t L hL k (s ≫ W.ι) 𝒱 h1]
  exact e0.symm.finrank_eq

include hεU in
/-- Construct the supported divisor from the fibrewise section and vanishing hypotheses. -/
theorem EXIST'
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ :
      Dγ.SupportedIn U)
    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M :
      (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u)
        s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x
          rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧
          Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N'
          → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I
            = D₀.I)
    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))),
            σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧
          Dx.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε
      t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t)
        s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H0 = 1)
    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) ∧
      D₀.SupportedIn U := by
  subst hr
  let ψ : SchemeHomOver (W.ι ≫ t) t := ⟨W.ι, rfl⟩
  have hfib := hfib_of_hU R c ε U hεU (g + e) e Dγ hDγ hH0one t L hL W hW
  have hM : Scheme.Modules.IsInvertible ((L.pullbackAlong ψ).L ⊗
      (sectionTwist c ε (W.ι ≫ t) (g + e) ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id
        _)).idealModule)) :=
    (L.pullbackAlong _).isInvertible.tensor ((isInvertible_sectionTwist R c ε U hεU (W.ι ≫ t) (g +
      e)).tensor
      ((Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).isInvertible_I_of_supportedIn U
        (hDγ.pullbackAlong _ _)).isInvertible_module)
  obtain ⟨D₀, N, hN, ⟨e₀⟩, -⟩ := hsect (W.ι ≫ t) _ hM hfib (hZfibγ (W.ι ≫ t) (L.pullbackAlong ψ)
    (hL.pullback ψ))
  have hD₀U : D₀.SupportedIn U := havoid (W.ι ≫ t) (L.pullbackAlong ψ) (hL.pullback ψ) D₀ N hN ⟨e₀⟩
  obtain ⟨D, hD, -⟩ := RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U D₀
    (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)) hD₀U (hDγ.pullbackAlong _ _)
  exact ⟨D, D₀, hD, nonempty_twistModule_iso R c ε U hεU (W.ι ≫ t) _ _ (hDγ.pullbackAlong _ _) D₀
    hD₀U D hD N hN e₀, hD₀U⟩

end AlgebraicGeometry.RelPicard.K5bExistSS


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.JacobianVarieties.Picard.Proofs.SupportedTwistedDivisor.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.JacobianVarieties.Picard.Proofs.SupportedTwistedDivisor.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra


end JacobianVarieties.Picard.Proofs.SupportedTwistedDivisor

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra

universe u

open JacobianVarieties.Picard.Proofs.SupportedTwistedDivisor.AlgebraicGeometry.RelPicard in
/-- Realize the restricted rigidified bundle by the twist module of a supported divisor. -/
theorem
exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ :
      Dγ.SupportedIn U)
    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M :
      (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u)
        s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x
          rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧
          Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N'
          → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I
            = D₀.I)
    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))),
            σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧
          Dx.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε
      t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t)
        s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H0 = 1)
    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id
            t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) ∧
      D₀.SupportedIn U :=
  K5bExistSS.EXIST' R c ε U hεU g e r hr Dγ hDγ hsect hZfibγ hH0one havoid t L hL W hW
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
