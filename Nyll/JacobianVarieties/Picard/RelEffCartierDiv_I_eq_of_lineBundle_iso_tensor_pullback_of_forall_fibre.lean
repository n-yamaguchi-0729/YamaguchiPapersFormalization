/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.JacobianVarieties.Picard.IsLocallyFreeOfRank_pushforward_of_forall_fibre
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesPushforwardRestrict
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Mathlib.Util.WithWeakNamespace

/-!
# Relative Picard varieties and fibre cohomology

Identify the effective divisor ideal determined by a line-bundle isomorphism and fibrewise
triviality.
-/

section ProofImplementation


namespace JacobianVarieties.Picard.Proofs
namespace RelEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve

namespace K5aUnitWs13

open Opposite TopologicalSpace

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_app_unit (φ : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : U ⟶ V)
    (m : Γ(𝟙_ X.Modules, V)) :
    M.presheaf.map i.op (φ.app V m) = φ.app U ((𝟙_ X.Modules).presheaf.map i.op m) := by
  have h := (Scheme.Modules.Hom.mapPresheaf φ).naturality i.op
  have h2 := ConcreteCategory.congr_hom h m
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at h2
  exact h2.symm

theorem map_toUnitSection_one {U V : X.Opens} (i : U ⟶ V) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection V 1) =
      Scheme.Modules.toUnitSection U 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem app_one_eq_map (φ : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    φ.app U (Scheme.Modules.toUnitSection U 1) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ.app ⊤
        (Scheme.Modules.toUnitSection ⊤ 1)) := by
  rw [map_app_unit, map_toUnitSection_one]

/-- The module morphism from the tensor unit determined by the given global section. -/
noncomputable def homOfGlobal (M : X.Modules) (m : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm
    (PresheafOfModules.sectionsMk (fun U => M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m)
      (by
        intro U V f
        change (M.presheaf.map (homOfLE _).op ≫ M.presheaf.map f) m = _
        rw [← Functor.map_comp]
        rfl))

theorem homOfGlobal_app_top (M : X.Modules) (m : Γ(M, ⊤)) :
    (homOfGlobal M m).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = m := by
  have hS : ∀ ⦃U V : (X.Opens)ᵒᵖ⦄ (f : U ⟶ V),
      M.presheaf.map f (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m) =
        M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op m := by
    intro U V f
    change (M.presheaf.map (homOfLE _).op ≫ M.presheaf.map f) m = _
    rw [← Functor.map_comp]
    rfl
  have h := congrArg (fun s : M.val.sections => s.val (op ⊤))
    ((SheafOfModules.unitHomEquiv M).apply_symm_apply
      (PresheafOfModules.sectionsMk (fun U => M.presheaf.map (homOfLE (le_top :
        U.unop ≤ ⊤)).op m) hS))
  change ((SheafOfModules.unitHomEquiv M) (homOfGlobal M m)).val (op ⊤) =
    M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m at h
  have hm : M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m := by
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]; rfl
  have h2 : ∀ σ : 𝟙_ X.Modules ⟶ M,
      ((SheafOfModules.unitHomEquiv M) σ).val (op ⊤) =
        σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) := by
    intro σ
    simp only [SheafOfModules.unitHomEquiv]
    erw [PresheafOfModules.unitHomEquiv_apply_coe]
    rfl
  rw [← h2]
  exact h.trans hm

theorem coeff_eq_mul_coeff (s s' : 𝟙_ X.Modules ⟶ M) (u : Γ(X, ⊤))
    (h : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • s'.app ⊤
      (Scheme.Modules.toUnitSection ⊤ 1))
    (U : X.Opens) (τ : M.restrict U.ι ≅ 𝟙_ ((U : Scheme.{u})).Modules) :
    Scheme.Modules.coeff s U τ.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op u * Scheme.Modules.coeff s' U τ.hom := by
  set W : X.Opens := U.ι ''ᵁ ⊤ with hW
  have hres : s.app W (Scheme.Modules.toUnitSection W 1) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u • s'.app W
        (Scheme.Modules.toUnitSection W 1) := by
    rw [app_one_eq_map s W, app_one_eq_map s' W, h, Scheme.Modules.map_smul]
  set r : Γ((U : Scheme.{u}), ⊤) := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u with hr
  have hres' : Scheme.Modules.restrictSection s U = r • Scheme.Modules.restrictSection s' U := by
    change s.app W (Scheme.Modules.toUnitSection W 1) =
      (U.ι.appIso ⊤).inv r • s'.app W (Scheme.Modules.toUnitSection W 1)
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact hres
  have key : Scheme.Modules.coeff s U τ.hom = U.topIso.hom r * Scheme.Modules.coeff s' U τ.hom := by
    change U.topIso.hom (Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤
      (Scheme.Modules.restrictSection s U))) = _
    rw [hres', Scheme.Modules.Hom.app_smul, Scheme.Modules.ofUnitSection_smul, map_mul]
    rfl
  rw [key, hr, Scheme.Opens.topIso_hom]
  congr 1
  change (X.presheaf.map _ ≫ X.presheaf.map _) u = _
  erw [← Functor.map_comp]
  rfl

theorem isUnit_coord_of_forall_fibre {T : Scheme.{u}} (q : X ⟶ T) (hM :
  Scheme.Modules.IsInvertible M)
    (τ : (Scheme.Modules.pushforward q).obj M ≅ 𝟙_ T.Modules) (s : 𝟙_ X.Modules ⟶ M)
    (hs : ∀ x : T, ∃ y : X, q.base y = x ∧ y ∉ (Scheme.Modules.zeroSchemeIdeal s).support) :
    IsUnit (Scheme.Modules.ofUnitSection ⊤
      (τ.hom.app ⊤ (show Γ((Scheme.Modules.pushforward q).obj M, ⊤) from
        s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)))) := by
  classical
  set m : Γ((Scheme.Modules.pushforward q).obj M, ⊤) := s.app ⊤
    (Scheme.Modules.toUnitSection ⊤ 1) with hm
  set a : Γ(T, ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ m) with ha
  set e : Γ((Scheme.Modules.pushforward q).obj M, ⊤) := τ.inv.app ⊤
    (Scheme.Modules.toUnitSection ⊤ 1) with he
  have h1 : τ.hom.app ⊤ m = a • Scheme.Modules.toUnitSection ⊤ 1 := by
    apply Scheme.Modules.ofUnitSection_injective
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  have h2 : m = τ.inv.app ⊤ (τ.hom.app ⊤ m) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    rfl
  have hme : m = a • e := by
    calc m = τ.inv.app ⊤ (τ.hom.app ⊤ m) := h2
      _ = τ.inv.app ⊤ (a • Scheme.Modules.toUnitSection ⊤ 1) := by rw [h1]
      _ = a • e := by rw [Scheme.Modules.Hom.app_smul]
  have hme' : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = q.appTop a • (show Γ(M, ⊤) from e) := hme
  apply RingedSpace.isUnit_of_isUnit_germ
  intro x _
  obtain ⟨y, hyx, hy⟩ := hs x
  obtain ⟨U, hyU, -, ⟨τU⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := y) trivial
  have hZU := ((Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s).2 U
    τU).1
  have hyb : y ∈ X.basicOpen (Scheme.Modules.coeff s U.1 τU.hom) := by
    by_contra hyb
    apply hy
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyU, hZU, Scheme.zeroLocus_span,
      Scheme.mem_zeroLocus_iff]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    rw [hf]; exact hyb
  have hunit := (X.mem_basicOpen _ y hyU).mp hyb
  have hcmp := coeff_eq_mul_coeff s (homOfGlobal M (show Γ(M, ⊤) from e)) (q.appTop a)
    (by rw [homOfGlobal_app_top]; exact hme') U.1 τU
  rw [hcmp, map_mul] at hunit
  have hu1 := isUnit_of_mul_isUnit_left hunit
  rw [TopCat.Presheaf.germ_res_apply] at hu1
  have hq : X.presheaf.germ ⊤ y trivial (q.appTop a) =
      q.stalkMap y (T.presheaf.germ ⊤ (q.base y) trivial a) :=
    (Scheme.Hom.germ_stalkMap_apply q ⊤ y trivial a).symm
  rw [hq] at hu1
  rw [← hyx]
  exact (isUnit_map_iff (q.stalkMap y).hom _).mp hu1

end K5aUnitWs13

open RelEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {d₁ d₂ : ℕ} (D₁ : RelEffCartierDiv c d₁ t) (D₂ : RelEffCartierDiv c d₂ t)
    (N₁ N₂ : T.Modules) (hN₁ : Scheme.Modules.IsInvertible N₁) (hN₂ :
      Scheme.Modules.IsInvertible N₂)
    (e₁ : D₁.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N₁)
    (e₂ : D₂.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N₂) :
    D₁.I = D₂.I := by
  classical
  have : IsSeparated c := inferInstance
  set q := pullback.snd c t with hq
  set s₁ : 𝟙_ (pullback c t).Modules ⟶ M ⊗ (Scheme.Modules.pullback q).obj N₁ :=
    D₁.I.invModuleSection ≫ e₁.hom with hs₁
  set s₂ : 𝟙_ (pullback c t).Modules ⟶ M ⊗ (Scheme.Modules.pullback q).obj N₂ :=
    D₂.I.invModuleSection ≫ e₂.hom with hs₂
  have hZ₁ : Scheme.Modules.zeroSchemeIdeal s₁ = D₁.I := by
    rw [hs₁, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      (RelEffCartierDiv.isInvertible_I D₁).zeroSchemeIdeal_invModuleSection]
  have hZ₂ : Scheme.Modules.zeroSchemeIdeal s₂ = D₂.I := by
    rw [hs₂, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      (RelEffCartierDiv.isInvertible_I D₂).zeroSchemeIdeal_invModuleSection]
  have key : ∀ z : ↥(pullback c t), ∃ V : T.Opens, q.base z ∈ V ∧
      (Scheme.Modules.zeroSchemeIdeal s₁).comap (q ⁻¹ᵁ V).ι =
        (Scheme.Modules.zeroSchemeIdeal s₂).comap (q ⁻¹ᵁ V).ι := by
    intro z
    set x : T := q.base z with hxdef
    have hP : Scheme.Modules.IsInvertible ((Scheme.Modules.pushforward q).obj M) :=
      (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
        (isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t M hM 1 hfib)
    obtain ⟨U₁, hxU₁, -, ⟨τ₁⟩⟩ := hN₁.exists_restrict_iso (V := ⊤) (x := x) trivial
    obtain ⟨U₂, hxU₂, h₂₁, ⟨τ₂⟩⟩ := hN₂.exists_restrict_iso (V := U₁.1) (x := x) hxU₁
    obtain ⟨U₃, hxU₃, h₃₂, ⟨τP⟩⟩ := hP.exists_restrict_iso (V := U₂.1) (x := x) hxU₂
    set V : T.Opens := U₃.1 with hVdef
    have trivN : ∀ {N : T.Modules} {U : T.Opens} (hle : V ≤ U) (τ : N.restrict U.ι ≅ 𝟙_ ((U :
      Scheme.{u})).Modules),
        Nonempty ((Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V : Scheme.{u})).Modules) := by
      intro N U hle τ
      refine ⟨((Scheme.Modules.pullbackCongr (T.homOfLE_ι hle).symm).app N) ≪≫
        ((Scheme.Modules.pullbackComp (T.homOfLE hle) U.ι).app N).symm ≪≫
        (Scheme.Modules.pullback (T.homOfLE hle)).mapIso
          (((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app N) ≪≫ τ) ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback (T.homOfLE hle))).symm⟩
    obtain ⟨eN₁⟩ := trivN (h₃₂.trans h₂₁) τ₁
    obtain ⟨eN₂⟩ := trivN h₃₂ τ₂
    set W : (pullback c t).Opens := q ⁻¹ᵁ V with hWdef
    obtain ⟨φ₁⟩ := Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open q V M
      N₁ eN₁
    obtain ⟨φ₂⟩ := Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open q V M
      N₂ eN₂
    refine ⟨V, hxU₃, ?_⟩
    have hMN₁ : Scheme.Modules.IsInvertible (M ⊗ (Scheme.Modules.pullback q).obj N₁) :=
      hM.tensor (hN₁.pullback q)
    have hMN₂ : Scheme.Modules.IsInvertible (M ⊗ (Scheme.Modules.pullback q).obj N₂) :=
      hM.tensor (hN₂.pullback q)
    rw [hMN₁.comap_zeroSchemeIdeal W.ι s₁, hMN₂.comap_zeroSchemeIdeal W.ι s₂,
      ← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (Scheme.Modules.pullbackSection W.ι s₁)
        φ₁.hom,
      ← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (Scheme.Modules.pullbackSection W.ι s₂)
        φ₂.hom]
    set t₁ := Scheme.Modules.pullbackSection W.ι s₁ ≫ φ₁.hom with ht₁
    set t₂ := Scheme.Modules.pullbackSection W.ι s₂ ≫ φ₂.hom with ht₂
    suffices hu : ∃ u : Γ((W : Scheme.{u}), ⊤), IsUnit u ∧
        t₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • t₁.app ⊤
          (Scheme.Modules.toUnitSection ⊤ 1) by
      obtain ⟨u, hu, h⟩ := hu
      exact Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul
        (hM.pullback W.ι) t₁ t₂ u hu h
    let τ' : (Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι) ≅ 𝟙_ ((V :
      Scheme.{u})).Modules :=
      ((Scheme.Modules.pushforwardRestrictIso q V).app M) ≪≫ τP
    let θ : (Scheme.Modules.pullback W.ι).obj M ≅ M.restrict W.ι :=
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm
    have hMW : Scheme.Modules.IsInvertible (M.restrict W.ι) := by
      refine ⟨fun w => ?_⟩
      obtain ⟨O, hwO, ⟨τO⟩⟩ := (hM.pullback W.ι).exists_trivialization w
      exact ⟨O, hwO, ⟨(Scheme.Modules.pullback O.ι).mapIso θ.symm ≪≫ τO⟩⟩
    have hs' : ∀ {L : (pullback c t).Modules} (sL : 𝟙_ _ ⟶ L) {dd : ℕ} (DD :
      RelEffCartierDiv c dd t)
        (hZ : Scheme.Modules.zeroSchemeIdeal sL = DD.I) (hL : Scheme.Modules.IsInvertible L)
        (φ : (Scheme.Modules.pullback W.ι).obj L ≅ (Scheme.Modules.pullback W.ι).obj M),
        ∀ v : ↥V, ∃ w : ↥W, (q ∣_ V).base w = v ∧
          w ∉ (Scheme.Modules.zeroSchemeIdeal ((Scheme.Modules.pullbackSection W.ι sL ≫ φ.hom) ≫
            θ.hom)).support := by
      intro L sL dd DD hZ hL φ v
      obtain ⟨y, hy, hyD⟩ := RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support c t DD (v : T)
      have hyW : y ∈ W := by
        change q.base y ∈ V
        rw [show q.base y = (v : T) from hy]; exact v.2
      refine ⟨⟨y, hyW⟩,
        Subtype.ext ((morphismRestrict_base_coe q V ⟨y, hyW⟩).trans hy), ?_⟩
      rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
        Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
        ← hL.comap_zeroSchemeIdeal W.ι sL, hZ]
      intro hw
      apply hyD
      have := hw
      rw [Scheme.IdealSheafData.support_comap] at this
      exact this
    have hs'₁ := hs' s₁ D₁ hZ₁ hMN₁ φ₁
    have hs'₂ := hs' s₂ D₂ hZ₂ hMN₂ φ₂
    have hu₁ := K5aUnitWs13.isUnit_coord_of_forall_fibre (q ∣_ V) hMW τ' (t₁ ≫ θ.hom) hs'₁
    have hu₂ := K5aUnitWs13.isUnit_coord_of_forall_fibre (q ∣_ V) hMW τ' (t₂ ≫ θ.hom) hs'₂
    let m₁ : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤) :=
      (t₁ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
    let m₂ : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤) :=
      (t₂ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
    let a₁ : Γ((V : Scheme.{u}), ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m₁)
    let a₂ : Γ((V : Scheme.{u}), ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m₂)
    let e' : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤) :=
      τ'.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
    have hcoord : ∀ m : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤),
        m = Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m) • e' := by
      intro m
      have h1 : τ'.hom.app ⊤ m = Scheme.Modules.ofUnitSection ⊤
        (τ'.hom.app ⊤ m) • Scheme.Modules.toUnitSection ⊤ 1 := by
        apply Scheme.Modules.ofUnitSection_injective
        rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
      have h2 : m = τ'.inv.app ⊤ (τ'.hom.app ⊤ m) := by
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
          Scheme.Modules.Hom.id_app]
        rfl
      calc m = τ'.inv.app ⊤ (τ'.hom.app ⊤ m) := h2
        _ = τ'.inv.app ⊤ (Scheme.Modules.ofUnitSection ⊤
          (τ'.hom.app ⊤ m) • Scheme.Modules.toUnitSection ⊤ 1) := by
            rw [← h1]
        _ = _ := by rw [Scheme.Modules.Hom.app_smul]
    have hm₁e : m₁ = a₁ • e' := hcoord m₁
    have hm₂e : m₂ = a₂ • e' := hcoord m₂
    let r : Γ((V : Scheme.{u}), ⊤) := a₂ * ↑(hu₁.unit⁻¹)
    have hr : r = a₂ * ↑(hu₁.unit⁻¹) := rfl
    have hm₂₁ : m₂ = r • m₁ := by
      rw [hm₂e, hm₁e, smul_smul, hr, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have hm₂₁' : (t₂ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
        (q ∣_ V).appTop r • (show Γ(M.restrict W.ι, ⊤) from (t₁ ≫ θ.hom).app ⊤
          (Scheme.Modules.toUnitSection ⊤ 1)) :=
      hm₂₁
    refine ⟨(q ∣_ V).appTop r, (hu₂.mul (Units.isUnit _)).map _, ?_⟩
    have ht : ∀ tt : 𝟙_ _ ⟶ (Scheme.Modules.pullback W.ι).obj M,
        tt.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
          θ.inv.app ⊤ ((tt ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
      intro tt
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Category.assoc,
        Iso.hom_inv_id,
        Category.comp_id]
    rw [ht t₂, ht t₁, hm₂₁', Scheme.Modules.Hom.app_smul]
  choose V hV hloc using key
  let 𝒰 : (pullback c t).OpenCover :=
    Scheme.Cover.mkOfCovers (↥(pullback c t)) (fun z => ((q ⁻¹ᵁ V z : (pullback c t).Opens) :
      Scheme.{u}))
      (fun z => (q ⁻¹ᵁ V z).ι)
      (fun y => ⟨y, ⟨y, hV y⟩, rfl⟩)
      (fun z => inferInstance)
  rw [← hZ₁, ← hZ₂]
  exact Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq 𝒰 fun z => hloc z
end RelEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre
end JacobianVarieties.Picard.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop)
in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop)
in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
attribute [-instance] AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
attribute [-instance] AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ
attribute [-instance] PresheafOfModules.pushforward_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_η
attribute [-instance] PresheafOfModules.free_monoidal
attribute [-instance] PresheafOfModules.restrictScalars_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ_gS
attribute [-instance] PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb)
in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance] PresheafOfModules.pullback_monoidal'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
attribute [-instance] AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
attribute [-instance] AlgebraicGeometry.isClosedImmersion_graphOver
open _root_.AlgebraicCurve.Place
  (instIsScalarTowerSubtypeMemValuationSubringToValuationSubring)
in
attribute [-instance]
  instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
attribute [-instance] AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
attribute [-instance] AlgebraicCurve.Place.instSMulAlgEquiv
open _root_.AlgebraicCurve.Place
  (instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring)
in
attribute [-instance]
  instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
attribute [-instance]
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
attribute [-simp] AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
