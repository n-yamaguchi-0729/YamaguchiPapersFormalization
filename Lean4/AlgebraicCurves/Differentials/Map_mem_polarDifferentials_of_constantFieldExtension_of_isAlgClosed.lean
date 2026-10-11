/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_map_mem_polarDifferentials_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Polar
import AlgebraicCurves.Places.Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import AlgebraicCurves.Places.Place_exists_toValuationSubring_eq_comap_of_ne_top
import AlgebraicCurves.Places.Exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
import AlgebraicCurves.Places.Place_isRegularAt_D_algebraMap_of_forall_algebraMap_mem_of_isAlgClosed
import AlgebraicCurves.FunctionFields.Exists_separating_transcendental_of_perfectField

/-!
# Map mem polar Differentials of constant Field Extension of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs
namespace Map_mem_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open _root_.AlgebraicCurve
open _root_.KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace PolarBC
open _root_.AlgebraicCurve

section Ord
variable {L E : Type*} [Field L] [Field E] [Algebra L E] (v : Place L E)

theorem ord_nonneg_of_mem {f : E} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hf' : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
    have := congrArg (fun z : v.toValuationSubring => (z : E)) hu
    simpa [zpow_natCast] using this
  rw [hf', v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : E} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, ← Int.toNat_of_nonneg h, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem mem_of_ord_nonneg' {f : E} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact mem_of_ord_nonneg v hf h

end Ord

section CaseA

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [SMulCommClass K' F F']

theorem map_smul_D (f g : F) :
    KaehlerDifferential.map K K' F F' (f • D K F g) = algebraMap F F' f • D K' F' (algebraMap F F'
      g) := by
  have : IsScalarTower F F' Ω[F'⁄K'] := KaehlerDifferential.isScalarTower_of_tower K' F'
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, algebraMap_smul]

variable [IsAlgClosed K'] [IsCurveOver K' F'] [Algebra.EssFiniteType K' F']

theorem caseA (v : Place K F) (w : Place K' F')
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔ algebraMap F F' f ∈ w.toValuationSubring)
    (hord : ∀ f : F, w.ord (algebraMap F F' f) = v.ord f) (ω : Ω[F⁄K]) :
    (v.IsRegularAt ω → w.IsRegularAt (KaehlerDifferential.map K K' F F' ω)) ∧
      (v.HasSimplePoleAt ω → w.HasSimplePoleAt (KaehlerDifferential.map K K' F F' ω)) := by
  have h1 : w.ord (algebraMap F F' v.uniformizer) = 1 := by rw [hord, v.ord_uniformizer]
  obtain ⟨u, hu0, hu⟩ := AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver w
    w.uniformizer
    (algebraMap F F' v.uniformizer) w.ord_uniformizer h1
  have humem : u ∈ w.toValuationSubring := mem_of_ord_nonneg' w (le_of_eq hu0.symm)
  have key : ∀ f : F, KaehlerDifferential.map K K' F F' (f • v.dCoord) = (algebraMap F F' f * u) •
    w.dCoord := by
    intro f
    rw [v.dCoord_eq, map_smul_D, hu, w.dCoord_eq, smul_smul]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨algebraMap F F' f * u, mul_mem ((hmem f).mp hf) humem, key f⟩
  · rintro ⟨f, hπf, rfl⟩
    refine ⟨algebraMap F F' f * u, ?_, key f⟩
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [map_zero, zero_mul, mul_zero]; exact zero_mem _
    rcases eq_or_ne u 0 with rfl | hu0'
    · rw [mul_zero, mul_zero]; exact zero_mem _
    apply mem_of_ord_nonneg' w
    have hvf : 0 ≤ 1 + v.ord f := by
      have := ord_nonneg_of_mem v hπf
      rwa [v.ord_mul v.uniformizer_ne_zero hf0, v.ord_uniformizer] at this
    rw [w.ord_mul w.uniformizer_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hf0) hu0'),
      w.ord_mul ((map_ne_zero _).mpr hf0) hu0', w.ord_uniformizer, hord, hu0]
    omega

end CaseA

end AlgebraicCurve.PolarBC

open _root_.AlgebraicCurve AlgebraicCurve AlgebraicCurve.PolarBC KaehlerDifferential in
theorem _root_.AlgebraicCurve.map_mem_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
      [SMulCommClass K' F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K' F']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (_hdK : ∀ v : Place K F, v.DCoordGenerates) (_hdK' : ∀ w : Place K' F', w.DCoordGenerates)
    (S : Set (Place K F)) :
    ∀ ω ∈ polarDifferentials K F S,
        KaehlerDifferential.map K K' F F' ω ∈ polarDifferentials K' F'
          {w : Place K' F' | ∃ v ∈ S, w.toValuationSubring.comap (algebraMap F F') =
            v.toValuationSubring} := by
  intro ω hω w
  by_cases htop : w.toValuationSubring.comap (algebraMap F F') = ⊤
  · have hall : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f => by
      have : f ∈ w.toValuationSubring.comap (algebraMap F F') := by rw [htop]; trivial
      exact this
    have hwS : w ∉ {w : Place K' F' | ∃ v ∈ S, w.toValuationSubring.comap (algebraMap F F') =
      v.toValuationSubring} := by
      rintro ⟨v, -, hv⟩
      exact v.ne_top' (hv ▸ htop)
    refine ⟨fun _ => ?_, fun h => absurd h hwS⟩
    clear hω
    obtain ⟨x, hxtr, hxfd⟩ := hfg
    obtain ⟨t, ht, htfd, htsep⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField
      hxtr hxfd
    have hB1 : ∀ g : F, w.IsRegularAt (D K' F' (algebraMap F F' g)) := fun g =>
      AlgebraicCurve.Place.isRegularAt_D_algebraMap_of_forall_algebraMap_mem_of_isAlgClosed K F K'
        F'
        ⟨t, ht, htfd, htsep⟩ hfg' hgen w hall g
    have hmemω : ω ∈ Submodule.span F (Set.range (D K F)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hmemω using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨g, rfl⟩ := hy
        rw [KaehlerDifferential.map_D]
        exact hB1 g
    | zero => rw [map_zero]; exact w.isRegularAt_zero
    | add y z _ _ hy hz => rw [map_add]; exact hy.add hz
    | smul f y _ hy =>
        obtain ⟨g, hg, hgy⟩ := hy
        have : IsScalarTower F F' Ω[F'⁄K'] := KaehlerDifferential.isScalarTower_of_tower K' F'
        refine ⟨algebraMap F F' f * g, mul_mem (hall f) hg, ?_⟩
        rw [LinearMap.map_smul, hgy, ← smul_smul, algebraMap_smul]
  · obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top (algebraMap
      F F') w
      (fun a => by
        have e : algebraMap F F' (algebraMap K F a) = algebraMap K' F' (algebraMap K K' a) := by
          rw [← IsScalarTower.algebraMap_apply K F F' a, IsScalarTower.algebraMap_apply K K' F' a]
        rw [e]; exact w.algebraMap_mem' _) htop
    obtain ⟨w₀, hw₀c, hw₀ord, hw₀u⟩ :=
      AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed K F
        K' F' hfg hfg' hgen v
    have hww : w = w₀ := hw₀u w hv.symm
    subst hww
    have hmem : ∀ f : F, f ∈ v.toValuationSubring ↔ algebraMap F F' f ∈ w.toValuationSubring := fun
      f => by
      rw [hv]; rfl
    have hS : (w ∈ {w : Place K' F' | ∃ v ∈ S, w.toValuationSubring.comap (algebraMap F F') =
      v.toValuationSubring}) ↔ v ∈ S := by
      constructor
      · rintro ⟨v₁, hv₁S, hv₁⟩
        have : v₁ = v := Place.ext (by rw [← hv₁, hv])
        rwa [← this]
      · exact fun h => ⟨v, h, hv.symm⟩
    have hA := caseA (K := K) v w hmem hw₀ord ω
    obtain ⟨hreg, hpole⟩ := hω v
    refine ⟨fun hn => hA.1 (hreg fun hvS => hn (hS.mpr hvS)), fun hy => hA.2 (hpole (hS.mp hy))⟩

end Map_mem_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
end AlgebraicCurves.Differentials.Proofs
end ProofImplementation
