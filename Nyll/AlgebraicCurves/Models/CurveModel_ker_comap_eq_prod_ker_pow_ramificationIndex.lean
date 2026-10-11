/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Models.CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap

/-!
# Curve Model ker comap eq prod ker pow ramification Index
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex

section SolBody
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve
open _root_.Topology

universe u v

section H4

namespace HG1b

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

theorem eq_unit_mul_pow_ord (w : Place K F') {ϖ : w.toValuationSubring} (hϖ : Irreducible ϖ)
    {a : w.toValuationSubring} (ha : a ≠ 0) :
    ∃ u : w.toValuationSubringˣ, ∃ n : ℕ, a = u * ϖ ^ n ∧ w.ord (a : F') = n := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨u, n, hu, ?_⟩
  have hcoe : (a : F') = ((u : w.toValuationSubring) : F') * ((ϖ : F') ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, w.ord_unit_smul_zpow u hϖ (n : ℤ)]

theorem mem_maximalIdeal_pow_of_le_ord (w : Place K F') {a : w.toValuationSubring} (ha : a ≠ 0)
    {n : ℕ} (hn : (n : ℤ) ≤ w.ord (a : F')) :
    a ∈ IsLocalRing.maximalIdeal w.toValuationSubring ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, m, hu, hord⟩ := eq_unit_mul_pow_ord w hϖ ha
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hnm : n ≤ m := by rw [hord] at hn; exact_mod_cast hn
  refine ⟨u * ϖ ^ (m - n), ?_⟩
  rw [hu, mul_left_comm, ← pow_add, Nat.add_sub_cancel' hnm]

theorem ord_pos_of_mem_maximalIdeal (w : Place K F') {a : w.toValuationSubring} (ha : a ≠ 0)
    (hmem : a ∈ IsLocalRing.maximalIdeal w.toValuationSubring) : 0 < w.ord (a : F') := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, n, hu, hord⟩ := eq_unit_mul_pow_ord w hϖ ha
  rw [hord]
  rcases n with _ | n
  · exfalso
    rw [pow_zero, mul_one] at hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu] at hmem
    exact hmem u.isUnit
  · exact_mod_cast Nat.succ_pos n

variable [Algebra.IsIntegral F F']

private theorem _root_.HG1b.map_restrictInclusion_maximalIdeal (w : Place K F') :
    (IsLocalRing.maximalIdeal (w.restrict F).toValuationSubring).map (w.restrictInclusion F) =
      IsLocalRing.maximalIdeal w.toValuationSubring ^ w.ramificationIndex F := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [map_zero]; exact Ideal.zero_mem _
    have hf0' : ((f : (w.restrict F).toValuationSubring) : F) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hf0
    have hvord : 0 < (w.restrict F).ord (f : F) := ord_pos_of_mem_maximalIdeal _ hf0 hf
    have himg0 : w.restrictInclusion F f ≠ 0 := by
      intro h0
      have := congrArg Subtype.val h0
      rw [Place.coe_restrictInclusion] at this
      exact hf0' ((map_eq_zero (algebraMap F F')).mp this)
    refine mem_maximalIdeal_pow_of_le_ord w himg0 ?_
    rw [Place.coe_restrictInclusion, w.ord_restrict]
    have hepos : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    nlinarith
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
    have hepos : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    have hgw : algebraMap F F' g ∈ w.toValuationSubring := by
      obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow ((map_ne_zero (algebraMap F F')).mpr hg0) hϖ
      rw [hu, hge, zpow_natCast]
      exact mul_mem (u : w.toValuationSubring).2 (pow_mem (ϖ : w.toValuationSubring).2 _)
    have hgv : g ∈ (w.restrict F).toValuationSubring := (w.mem_restrict_iff (F := F)).mpr hgw
    have hordv : (w.restrict F).ord g = 1 := by
      have h := w.ord_restrict (F := F) g
      rw [hge] at h
      have : (w.ramificationIndex F : ℤ) * 1 = (w.ramificationIndex F : ℤ) * (w.restrict F).ord g
        := by
        linarith
      exact (mul_left_cancel₀ (by exact_mod_cast hepos.ne') this).symm
    have hgmax : (⟨g, hgv⟩ : (w.restrict F).toValuationSubring) ∈
        IsLocalRing.maximalIdeal (w.restrict F).toValuationSubring := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h0 := (w.restrict F).ord_coe_unit hu.unit
      rw [IsUnit.unit_spec] at h0
      change (w.restrict F).ord g = 0 at h0
      omega
    have himg : w.restrictInclusion F ⟨g, hgv⟩ = ⟨algebraMap F F' g, hgw⟩ := Subtype.ext rfl
    have hne : (⟨algebraMap F F' g, hgw⟩ : w.toValuationSubring) ≠ 0 := by
      intro h0
      exact ((map_ne_zero (algebraMap F F')).mpr hg0) (congrArg Subtype.val h0)
    obtain ⟨u, n, hu, hord⟩ := eq_unit_mul_pow_ord w hϖ hne
    have hn : n = w.ramificationIndex F := by
      have : (n : ℤ) = w.ramificationIndex F := by rw [← hord]; exact hge
      exact_mod_cast this
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe]
    have hmem : (⟨algebraMap F F' g, hgw⟩ : w.toValuationSubring) ∈
        (IsLocalRing.maximalIdeal (w.restrict F).toValuationSubring).map (w.restrictInclusion F) :=
          by
      rw [← himg]; exact Ideal.mem_map_of_mem _ hgmax
    rw [hu, hn] at hmem
    have := Ideal.mul_mem_left _ (↑u⁻¹ : w.toValuationSubring) hmem
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this

open HG1b
end HG1b

end H4

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_of_forall_ideal_preimage_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (J : Y.IdealSheafData) (P : X.IdealSheafData)
    (h : ∀ U : Y.affineOpens,
      P.ideal ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ = (J.ideal U).map (f.app U.1).hom) :
    J.comap f = P := by
  apply le_antisymm
  · refine Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_
    rw [Scheme.IdealSheafData.le_def]
    intro U
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, h U]
    exact Ideal.le_comap_map
  · refine Scheme.IdealSheafData.le_of_iSup_eq_top
      (fun U : Y.affineOpens => (⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ : X.affineOpens)) ?_ fun U => ?_
    · apply top_le_iff.mp
      rw [← Scheme.Hom.preimage_top f, ← iSup_affineOpens_eq_top Y, Scheme.Hom.preimage_iSup]
    · have hle := Scheme.IdealSheafData.le_map_comap J f
      rw [Scheme.IdealSheafData.le_def] at hle
      have hU := hle U
      rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, ← Ideal.map_le_iff_le_comap] at hU
      rw [h U]
      exact hU

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
private theorem _root_.AlgebraicCurve.Place.map_restrictInclusion_maximalIdeal
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') :
    (IsLocalRing.maximalIdeal (w.restrict F).toValuationSubring).map (w.restrictInclusion F) =
      IsLocalRing.maximalIdeal w.toValuationSubring ^ w.ramificationIndex F :=
  HG1b.map_restrictInclusion_maximalIdeal w

end AlgebraicCurve.Place
end SolBody

section StalkVal
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve

universe u v

namespace HG1b

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The homomorphism from a stalk to the modeled function field. -/
noncomputable def stalkToField (M : CurveModel K L) (z : M.C) : M.C.presheaf.stalk z →+* L :=
  (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
    (algebraMap (M.C.presheaf.stalk z) M.C.functionField)

theorem stalkToField_apply (M : CurveModel K L) (z : M.C) (s : M.C.presheaf.stalk z) :
    stalkToField M z s = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk z) M.C.functionField s) :=
      rfl

theorem stalkToField_injective (M : CurveModel K L) (z : M.C) : Function.Injective (stalkToField M
  z) :=
  M.ffEquiv.symm.injective.comp (FaithfulSMul.algebraMap_injective _ _)

/-- The stalk equivalence with a valuation ring having the same image in the function field. -/
noncomputable def stalkEquivOfRange (M : CurveModel K L) (z : M.C) (P : Place K L)
    (hr : (stalkToField M z).range = P.toValuationSubring.toSubring) :
    M.C.presheaf.stalk z ≃+* P.toValuationSubring :=
  RingEquiv.ofBijective
    ((stalkToField M z).codRestrict P.toValuationSubring fun s => by
      have : stalkToField M z s ∈ (stalkToField M z).range := ⟨s, rfl⟩
      rw [hr] at this
      exact this)
    ⟨fun a b h => stalkToField_injective M z (congrArg Subtype.val h), fun t => by
      have ht : (t : L) ∈ (stalkToField M z).range := by rw [hr]; exact t.2
      obtain ⟨s, hs⟩ := ht
      exact ⟨s, Subtype.ext hs⟩⟩

@[scoped simp] theorem coe_stalkEquivOfRange (M : CurveModel K L) (z : M.C) (P : Place K L)
    (hr : (stalkToField M z).range = P.toValuationSubring.toSubring) (s : M.C.presheaf.stalk z) :
    ((stalkEquivOfRange M z P hr s : P.toValuationSubring) : L) = stalkToField M z s := rfl

end HG1b

theorem HG1b.map_stalkMap_maximalIdeal_eq_pow
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F]
      [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}) :
    (IsLocalRing.maximalIdeal (M.C.presheaf.stalk (π.base (pointEquivClosedPoint M'.toBase
      y).1))).map
        (π.stalkMap (pointEquivClosedPoint M'.toBase y).1).hom =
      IsLocalRing.maximalIdeal (M'.C.presheaf.stalk (pointEquivClosedPoint M'.toBase y).1) ^
        ((M'.pointEquivPlace y).ramificationIndex F) := by
  set ypt := (pointEquivClosedPoint M'.toBase y) with hypt
  set w : Place k F' := M'.pointEquivPlace y with hw
  let x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨y.1 ≫ π, by rw [Category.assoc, hπ]; exact y.2⟩
  have hxpt : ((pointEquivClosedPoint M.toBase x) : M.C) = π.base ypt.1 := by
    rw [pointEquivClosedPoint_apply_coe, hypt, pointEquivClosedPoint_apply_coe]
    rfl
  have hclosed : IsClosed ({π.base ypt.1} : Set M.C) := hxpt ▸ (pointEquivClosedPoint M.toBase x).2
  have hv : w.restrict F = M.placeOfPoint ⟨π.base ypt.1, hclosed⟩ := by
    rw [hplace y x rfl, CurveModel.pointEquivPlace_apply]
    congr 1
  have hry : (HG1b.stalkToField M' ypt.1).range = w.toValuationSubring.toSubring :=
    M'.range_stalk_eq ypt
  have hrx : (HG1b.stalkToField M (π.base ypt.1)).range = (w.restrict
    F).toValuationSubring.toSubring := by
    rw [hv]; exact M.range_stalk_eq ⟨π.base ypt.1, hclosed⟩
  let θy := HG1b.stalkEquivOfRange M' ypt.1 w hry
  let θx := HG1b.stalkEquivOfRange M (π.base ypt.1) (w.restrict F) hrx
  have hsq : θy.toRingHom.comp (π.stalkMap ypt.1).hom = (w.restrictInclusion F).comp θx.toRingHom
    := by
    refine RingHom.ext fun s => Subtype.ext ?_
    change ((θy (π.stalkMap ypt.1 s) : w.toValuationSubring) : F') =
      ((w.restrictInclusion F (θx s) : w.toValuationSubring) : F')
    rw [Place.coe_restrictInclusion, HG1b.coe_stalkEquivOfRange, HG1b.coe_stalkEquivOfRange,
      HG1b.stalkToField_apply, HG1b.stalkToField_apply]
    exact AlgebraicCurve.CurveModel.ffEquiv_symm_stalkMap_eq_algebraMap M M' π hπ hplace ypt.1 s
  have key : ((IsLocalRing.maximalIdeal _).map (π.stalkMap ypt.1).hom).map θy.toRingHom =
      ((IsLocalRing.maximalIdeal (M'.C.presheaf.stalk ypt.1)) ^ (w.ramificationIndex F)).map
        θy.toRingHom := by
    rw [Ideal.map_map, hsq, ← Ideal.map_map, Ideal.map_pow]
    erw [IsLocalRing.map_ringEquiv_maximalIdeal θx, IsLocalRing.map_ringEquiv_maximalIdeal θy]
    exact w.map_restrictInclusion_maximalIdeal (F := F)
  have hinj : Function.Injective (Ideal.map θy.toRingHom) := by
    intro I J h
    have := congrArg (Ideal.map θy.symm.toRingHom) h
    rwa [Ideal.map_map, Ideal.map_map, show θy.symm.toRingHom.comp θy.toRingHom = RingHom.id _ from
      RingHom.ext fun a => θy.symm_apply_apply a, Ideal.map_id, Ideal.map_id] at this
  exact hinj key

end StalkVal

section Plumb
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Topology

universe u

namespace HG1bPlumbing

theorem map_germ_primeIdealOf {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (z : U) :
    (hU.primeIdealOf z).asIdeal.map (X.presheaf.germ U z.1 z.2).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk z.1) := by
  have := hU.isLocalization_stalk z
  exact IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf z).asIdeal (X.presheaf.stalk
    z.1)

theorem map_germ_eq_top_of_not_le {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (z : U)
    {I : Ideal Γ(X, U)} (hI : ¬ I ≤ (hU.primeIdealOf z).asIdeal) :
    I.map (X.presheaf.germ U z.1 z.2).hom = ⊤ := by
  have := hU.isLocalization_stalk z
  rw [IsConcreteLE.not_le_iff_exists] at hI
  obtain ⟨f, hfI, hfp⟩ := hI
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk z.1) f) :=
    IsLocalization.map_units (M := (hU.primeIdealOf z).asIdeal.primeCompl) (X.presheaf.stalk z.1)
      ⟨f, hfp⟩
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hfI) hu

theorem comap_germ_maximalIdeal {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (z : U) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk z.1)).comap (X.presheaf.germ U z.1 z.2).hom =
      (hU.primeIdealOf z).asIdeal := by
  have := hU.isLocalization_stalk z
  exact IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk z.1) (hU.primeIdealOf z).asIdeal

theorem maximalIdeal_stalk_eq_bot_of_isField {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
  (z : U)
    (hF : IsField Γ(X, U)) : IsLocalRing.maximalIdeal (X.presheaf.stalk z.1) = ⊥ := by
  have := hU.isLocalization_stalk z
  let : Field Γ(X, U) := hF.toField
  have hP : (hU.primeIdealOf z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have hbij : Function.Bijective (algebraMap Γ(X, U) (X.presheaf.stalk z.1)) := by
    refine IsField.localization_map_bijective (M := (hU.primeIdealOf z).asIdeal.primeCompl) ?_ hF
    exact fun h0 => h0 (Ideal.zero_mem _)
  have hF' : IsField (X.presheaf.stalk z.1) :=
    MulEquiv.isField hF (RingEquiv.ofBijective _ hbij).toMulEquiv.symm
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hF'

theorem ker_ideal_eq_top_of_not_mem {X : Scheme.{u}} {K : Type u} [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X) [QuasiCompact p] (U : X.affineOpens)
    (h : p.base (IsLocalRing.closedPoint K) ∉ (U : X.Opens)) :
    p.ker.ideal U = ⊤ := by
  rw [Scheme.Hom.ker_apply]
  have hempty : p ⁻¹ᵁ (U : X.Opens) = ⊥ := by
    ext q
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    have hq : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hq]; exact h
  have : Subsingleton Γ(Spec (CommRingCat.of K), p ⁻¹ᵁ (U : X.Opens)) := by
    rw [hempty]; infer_instance
  exact RingHom.ker_eq_top_of_subsingleton _

theorem ker_eq_maximalIdeal_of_isLocalHom {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
  [IsLocalRing S]
    (hS : IsLocalRing.maximalIdeal S = ⊥) (φ : R →+* S) [IsLocalHom φ] :
    RingHom.ker φ = IsLocalRing.maximalIdeal R := by
  ext a
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    exact (hu.map φ).ne_zero h
  · intro h
    have hn : φ a ∈ IsLocalRing.maximalIdeal S := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => h (IsLocalHom.map_nonunit a hu)
    rwa [hS, Ideal.mem_bot] at hn

theorem isField_ΓSpec_top (K : Type u) [Field K] : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

theorem isField_ΓSpec (K : Type u) [Field K] (V : (Spec (CommRingCat.of K)).Opens)
    (hV : IsLocalRing.closedPoint K ∈ V) : IsField Γ(Spec (CommRingCat.of K), V) := by
  have hVtop : V = ⊤ := by
    ext q; simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
    rw [Subsingleton.elim q (IsLocalRing.closedPoint K)]; exact hV
  subst hVtop
  exact isField_ΓSpec_top K

theorem maximalIdeal_stalk_Spec_field_eq_bot (K : Type u) [Field K] :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of K)).presheaf.stalk
      (show ↥(Spec (CommRingCat.of K)) from IsLocalRing.closedPoint K)) = ⊥ :=
  maximalIdeal_stalk_eq_bot_of_isField (isAffineOpen_top _) ⟨IsLocalRing.closedPoint K, trivial⟩
    (isField_ΓSpec_top K)

theorem ker_ideal_eq_primeIdealOf {X : Scheme.{u}} {K : Type u} [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X) [QuasiCompact p] (U : X.affineOpens)
    (h : p.base (IsLocalRing.closedPoint K) ∈ (U : X.Opens)) :
    p.ker.ideal U = (U.2.primeIdealOf ⟨_, h⟩).asIdeal := by
  rw [Scheme.Hom.ker_apply]
  set pt : ↥(Spec (CommRingCat.of K)) := IsLocalRing.closedPoint K
  let : Field Γ(Spec (CommRingCat.of K), p ⁻¹ᵁ (U : X.Opens)) := (isField_ΓSpec K _ h).toField
  have hinj : Function.Injective ((Spec (CommRingCat.of K)).presheaf.germ (p ⁻¹ᵁ (U : X.Opens)) pt
    h).hom :=
    RingHom.injective _
  have h1 : RingHom.ker (p.app (U : X.Opens)).hom =
      RingHom.ker (((Spec (CommRingCat.of K)).presheaf.germ (p ⁻¹ᵁ (U : X.Opens)) pt h).hom.comp
        (p.app (U : X.Opens)).hom) := by
    ext a; simp only [RingHom.mem_ker, RingHom.comp_apply]
    exact ⟨fun ha => by rw [ha, map_zero], fun ha => hinj (by rw [ha, map_zero])⟩
  have h2 : ((Spec (CommRingCat.of K)).presheaf.germ (p ⁻¹ᵁ (U : X.Opens)) pt h).hom.comp (p.app (U
    : X.Opens)).hom
      = (p.stalkMap pt).hom.comp (X.presheaf.germ (U : X.Opens) (p.base pt) h).hom := by
    have := p.germ_stalkMap (U : X.Opens) pt h
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, this]
  rw [h1, h2, ← RingHom.comap_ker, ker_eq_maximalIdeal_of_isLocalHom
    (maximalIdeal_stalk_Spec_field_eq_bot K)]
  exact comap_germ_maximalIdeal U.2 ⟨p.base pt, h⟩

theorem ideal_eq_of_forall_isClosed_map_germ_eq {X : Scheme.{u}} [JacobsonSpace X] {U : X.Opens}
    (hU : IsAffineOpen U) {I J : Ideal Γ(X, U)}
    (h : ∀ z : U, IsClosed ({z.1} : Set X) →
      I.map (X.presheaf.germ U z.1 z.2).hom = J.map (X.presheaf.germ U z.1 z.2).hom) : I = J := by
  refine Ideal.eq_of_localization_maximal fun P hP => ?_
  let q : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
  change Ideal.map (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal)) I =
    Ideal.map (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal)) J
  let z : U := hU.isoSpec.inv.base q
  have hzq : hU.primeIdealOf z = q := by
    change (hU.isoSpec.inv ≫ hU.isoSpec.hom).base q = q
    rw [Iso.inv_hom_id]; rfl
  have hq : IsClosed ({q} : Set (PrimeSpectrum Γ(X, U))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hP
  have hzclosed : IsClosed ({z.1} : Set X) := by
    have hsub := hU.fromSpec.closePoints_subset_preimage_closedPoints
    have hmem : hU.fromSpec.base q ∈ closedPoints X := hsub hq
    exact hmem
  have hst := h z hzclosed
  have : IsLocalization.AtPrime (X.presheaf.stalk z.1) q.asIdeal := by
    have hloc := hU.isLocalization_stalk z
    rwa [hzq] at hloc
  let e := IsLocalization.algEquiv q.asIdeal.primeCompl (X.presheaf.stalk z.1)
    (Localization.AtPrime q.asIdeal)
  have halg : (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal)) =
      (e : X.presheaf.stalk z.1 →+* Localization.AtPrime q.asIdeal).comp (X.presheaf.germ U z.1
        z.2).hom := by
    ext a
    exact (e.commutes a).symm
  rw [halg, ← Ideal.map_map, ← Ideal.map_map, hst]

end HG1bPlumbing

end Plumb

section H2proof
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve
open _root_.Topology

universe u v

theorem HG1b.map_app_ideal_ker_eq_prod_pow
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F]
      [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (U : M.C.affineOpens) :
    ((x.1.ker).ideal U).map (π.app U.1).hom =
      ∏ w ∈ (M.pointEquivPlace x).fiber F',
        (((M'.pointEquivPlace.symm w).1.ker).ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) ^
          (w.ramificationIndex F) := by
  classical
  set pt : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k with hpt
  set V : M'.C.affineOpens := ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ with hV
  set fib := (M.pointEquivPlace x).fiber F' with hfib
  have : JacobsonSpace M'.C := LocallyOfFiniteType.jacobsonSpace M'.toBase
  have hyc : ∀ (z : V.1) (hz : IsClosed ({z.1} : Set M'.C)),
      ((pointEquivClosedPoint M'.toBase).symm ⟨z.1, hz⟩).1.base pt = z.1 := fun z hz => by
    erw [pointEquivClosedPoint_symm_apply_coe, pointOfClosedPoint_apply]
  refine HG1bPlumbing.ideal_eq_of_forall_isClosed_map_germ_eq V.2 fun z hz => ?_
  set y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} :=
    (pointEquivClosedPoint M'.toBase).symm ⟨z.1, hz⟩ with hy
  have hyz : y.1.base pt = z.1 := hyc z hz
  let x' : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨y.1 ≫ π, by rw [Category.assoc, hπ]; exact y.2⟩
  have hx'pt : x'.1.base pt = π.base z.1 := by
    change (y.1 ≫ π).base pt = π.base z.1
    change π.base (y.1.base pt) = π.base z.1
    rw [hyz]
  have hπzU : π.base z.1 ∈ (U : M.C.Opens) := z.2
  have hw : (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x' := hplace y x' rfl
  have hLHS : (((x.1.ker).ideal U).map (π.app U.1).hom).map (M'.C.presheaf.germ V.1 z.1 z.2).hom =
      (((x.1.ker).ideal U).map (M.C.presheaf.germ U.1 (π.base z.1) hπzU).hom).map (π.stalkMap
        z.1).hom := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    have := π.germ_stalkMap U.1 z.1 hπzU
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, this]
  have hRHS : (∏ w ∈ fib, (((M'.pointEquivPlace.symm w).1.ker).ideal V) ^ (w.ramificationIndex
    F)).map
        (M'.C.presheaf.germ V.1 z.1 z.2).hom =
      ∏ w ∈ fib, ((((M'.pointEquivPlace.symm w).1.ker).ideal V).map (M'.C.presheaf.germ V.1 z.1
        z.2).hom) ^
        (w.ramificationIndex F) := by
    rw [← Ideal.mapHom_apply, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_pow, Ideal.mapHom_apply]
  have hfactor : ∀ w ∈ fib,
      ((((M'.pointEquivPlace.symm w).1.ker).ideal V).map (M'.C.presheaf.germ V.1 z.1 z.2).hom) =
        if w = M'.pointEquivPlace y then IsLocalRing.maximalIdeal (M'.C.presheaf.stalk z.1) else ⊤
          := by
    intro w _
    set yw := M'.pointEquivPlace.symm w with hyw
    by_cases hwy : w = M'.pointEquivPlace y
    · rw [ite_eq_left hwy]
      have hyw' : yw = y := by rw [hyw, hwy, Equiv.symm_apply_apply]
      have hmem : yw.1.base pt ∈ (V : M'.C.Opens) := by rw [hyw', hyz]; exact z.2
      rw [HG1bPlumbing.ker_ideal_eq_primeIdealOf yw.1 V hmem]
      have : (⟨yw.1.base pt, hmem⟩ : V.1) = z := Subtype.ext
        (by change yw.1.base pt = z.1; rw [hyw', hyz])
      rw [this]
      exact HG1bPlumbing.map_germ_primeIdealOf V.2 z
    · rw [ite_eq_right hwy]
      by_cases hmem : yw.1.base pt ∈ (V : M'.C.Opens)
      · rw [HG1bPlumbing.ker_ideal_eq_primeIdealOf yw.1 V hmem]
        refine HG1bPlumbing.map_germ_eq_top_of_not_le V.2 z fun hle => hwy ?_
        have hmax : (V.2.primeIdealOf ⟨yw.1.base pt, hmem⟩).asIdeal.IsMaximal :=
          V.2.primeIdealOf_isMaximal_of_isClosed _ (pointEquivClosedPoint M'.toBase yw).2
        have heq := hmax.eq_of_le (V.2.primeIdealOf z).isPrime.ne_top hle
        have hpts : (⟨yw.1.base pt, hmem⟩ : V.1) = z :=
          (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso V.2.isoSpec)).injective
            (PrimeSpectrum.ext heq)
        have hyy : yw = y := by
          apply (pointEquivClosedPoint M'.toBase).injective
          apply Subtype.ext
          rw [pointEquivClosedPoint_apply_coe, pointEquivClosedPoint_apply_coe]
          change yw.1.base pt = y.1.base pt
          rw [hyz]; exact congrArg Subtype.val hpts
        rw [← hyy, hyw, Equiv.apply_symm_apply]
      · rw [HG1bPlumbing.ker_ideal_eq_top_of_not_mem yw.1 V hmem, Ideal.map_top]
  have hRHS' : (∏ w ∈ fib, (((M'.pointEquivPlace.symm w).1.ker).ideal V) ^ (w.ramificationIndex
    F)).map
        (M'.C.presheaf.germ V.1 z.1 z.2).hom =
      if M'.pointEquivPlace y ∈ fib then
        IsLocalRing.maximalIdeal (M'.C.presheaf.stalk z.1) ^ ((M'.pointEquivPlace
          y).ramificationIndex F)
      else ⊤ := by
    rw [hRHS]
    split_ifs with hin
    · rw [Finset.prod_eq_single_of_mem _ hin]
      · rw [hfactor _ hin, ite_eq_left rfl]
      · intro b hb hne
        rw [hfactor b hb, ite_eq_right hne, Ideal.top_pow, Ideal.one_eq_top]
    · rw [← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun b hb => ?_
      have hne : b ≠ M'.pointEquivPlace y := fun h => hin (h ▸ hb)
      rw [hfactor b hb, ite_eq_right hne, Ideal.top_pow, Ideal.one_eq_top]
  have hin_iff : M'.pointEquivPlace y ∈ fib ↔ π.base z.1 = x.1.base pt := by
    rw [hfib, Place.mem_fiber, hw]
    constructor
    · intro h
      have hxx : x' = x := M.pointEquivPlace.injective h
      rw [← hx'pt, hxx]
    · intro h
      have hxx : x' = x := by
        apply (pointEquivClosedPoint M.toBase).injective
        apply Subtype.ext
        rw [pointEquivClosedPoint_apply_coe, pointEquivClosedPoint_apply_coe]
        change x'.1.base pt = x.1.base pt
        rw [hx'pt, h]
      rw [hxx]
  rw [hLHS, hRHS']
  by_cases hcase : π.base z.1 = x.1.base pt
  · rw [ite_eq_left (hin_iff.mpr hcase)]
    have hxU : x.1.base pt ∈ (U : M.C.Opens) := hcase ▸ hπzU
    rw [HG1bPlumbing.ker_ideal_eq_primeIdealOf x.1 U hxU]
    have hptsU : (⟨x.1.base pt, hxU⟩ : U.1) = ⟨π.base z.1, hπzU⟩ := Subtype.ext hcase.symm
    rw [hptsU, HG1bPlumbing.map_germ_primeIdealOf U.2 ⟨π.base z.1, hπzU⟩]
    have key := HG1b.map_stalkMap_maximalIdeal_eq_pow M M' π hπ hplace y
    have hyz' : (pointEquivClosedPoint M'.toBase y) = ⟨z.1, hz⟩ := by
      rw [hy, Equiv.apply_symm_apply]
    rw [hyz'] at key
    exact key
  · rw [ite_eq_right (fun h => hcase (hin_iff.mp h))]
    suffices hm : ((x.1.ker).ideal U).map (M.C.presheaf.germ U.1 (π.base z.1) hπzU).hom = ⊤ by
      rw [hm, Ideal.map_top]
    by_cases hxU : x.1.base pt ∈ (U : M.C.Opens)
    · rw [HG1bPlumbing.ker_ideal_eq_primeIdealOf x.1 U hxU]
      refine HG1bPlumbing.map_germ_eq_top_of_not_le U.2 ⟨π.base z.1, hπzU⟩ fun hle => hcase ?_
      have hmax : (U.2.primeIdealOf ⟨x.1.base pt, hxU⟩).asIdeal.IsMaximal :=
        U.2.primeIdealOf_isMaximal_of_isClosed _ (pointEquivClosedPoint M.toBase x).2
      have heq := hmax.eq_of_le (U.2.primeIdealOf ⟨π.base z.1, hπzU⟩).isPrime.ne_top hle
      have hpts : (⟨x.1.base pt, hxU⟩ : U.1) = ⟨π.base z.1, hπzU⟩ :=
        (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso U.2.isoSpec)).injective (PrimeSpectrum.ext
          heq)
      exact (congrArg Subtype.val hpts).symm
    · rw [HG1bPlumbing.ker_ideal_eq_top_of_not_mem x.1 U hxU, Ideal.map_top]

end H2proof

section Head
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve

universe u v

open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
theorem AlgebraicGeometry.Scheme.IdealSheafData.ideal_finset_prod_pow {X : Scheme.{u}} {ι : Type*}
    (s : Finset ι) (I : ι → X.IdealSheafData) (n : ι → ℕ) (V : X.affineOpens) :
    (∏ i ∈ s, I i ^ n i).ideal V = ∏ i ∈ s, (I i).ideal V ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.one_eq_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ih]
open
  CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex.AlgebraicGeometry.Scheme.IdealSheafData in
theorem _root_.AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F]
      [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    (x.1.ker).comap π =
      ∏ w ∈ (M.pointEquivPlace x).fiber F', ((M'.pointEquivPlace.symm w).1.ker) ^
        (w.ramificationIndex F) := by
  refine comap_eq_of_forall_ideal_preimage_eq π _ _ fun U => ?_
  rw [ideal_finset_prod_pow]
  exact (HG1b.map_app_ideal_ker_eq_prod_pow M M' π hπ hplace x U).symm

end Head
end AlgebraicCurves.Models.Proofs.CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
end ProofImplementation
