/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_serrePairing_eq_of_cechH1ToH1_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Differentials.Regular
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Cohomology.SerrePairing
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.WeilOfKaehler_mem_omegaSpace_of_residueTheorem

/-!
# Serre Pairing eq of cech H1To H1 eq
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.SerrePairingCechH1ToH1

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
open _root_.AlgebraicCurve.Place
end Place
namespace Place
open scoped _root_.AlgebraicCurve.Place in
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_t0 (v : Place K F) {f : F} (hf : f ∈
  v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [v.ord_zero]
  · exact ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

end Place
open _root_.AlgebraicCurve
section Generic

variable [HasCanonicalLocalResidueKStar K F] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial
  Ω[F⁄K]]
  [HasCanonicalDivisor (K := K) (F := F)] [HasPrincipalDivisors K F]

omit [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F] in
theorem canonicalDivisorOf_nonneg_of_mem_regularDifferentials_t0 {ω : Ω[F⁄K]} (hω0 : ω ≠ 0)
    (hω : ω ∈ regularDifferentials K F) : 0 ≤ canonicalDivisorOf hω0 := by
  refine Finsupp.le_def.mpr fun v => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, canonicalDivisorOf_apply]
  obtain ⟨g, hg, hωg⟩ := hω v
  change 0 ≤ v.ord (v.differentialCoeff ω)
  rw [v.differentialCoeff_unique hωg]
  exact v.ord_nonneg_of_mem_t0 hg

theorem serrePairing_apply_mk_eq_weilOfKaehler_t0 (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K
  F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0)
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) :
    serrePairing hRT hcover ω (Submodule.Quotient.mk f)
      = weilOfKaehler K F hω ⟨((extendOffChart K S₀ (f : F) : ↥(repartitions K F)) : Place K F → F),
          coe_extendOffChart_mem_adeleSpace S₀ (f : F)⟩ := by
  rw [serrePairing_apply_mk, residueSumOffChart_def, weilOfKaehler_apply]
omit [HasCanonicalLocalResidueKStar K F] [∀ (v : Place K F), v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]] [HasCanonicalDivisor (K := K) (F := F)] in
theorem omegaSpace_zero_apply_eq_of_mk_eq {μ : Module.Dual K ↥(adeleSpace K F)}
    (hμ : μ ∈ omegaSpace (K := K) (F := F) (0 : Divisor K F))
    (a b : ↥(repartitions K F)) (ha : (a : Place K F → F) ∈ adeleSpace K F)
    (hb : (b : Place K F → F) ∈ adeleSpace K F)
    (h : (Submodule.Quotient.mk a : H1 (0 : Divisor K F)) = Submodule.Quotient.mk b) :
    μ ⟨(a : Place K F → F), ha⟩ = μ ⟨(b : Place K F → F), hb⟩ := by
  rw [← sub_eq_zero, ← map_sub]
  rw [Submodule.Quotient.eq] at h
  obtain ⟨r, hr, p, hp, hrp⟩ := Submodule.mem_sup.mp h
  obtain ⟨f₀, hf₀⟩ := mem_principalRepartitions_iff.mp hp
  have hrA : (r : Place K F → F) ∈ adeleSpace K F := adeleBdd_le_adeleSpace (D := 0) hr
  have hpA : (p : Place K F → F) ∈ adeleSpace K F := by
    rw [hf₀]
    exact diagonal_mem_adeleSpace f₀
  have hsum : (⟨(a : Place K F → F), ha⟩ - ⟨(b : Place K F → F), hb⟩ : ↥(adeleSpace K F))
      = ⟨(r : Place K F → F), hrA⟩ + ⟨(p : Place K F → F), hpA⟩ := by
    apply Subtype.ext
    have h' := congrArg (fun x : ↥(repartitions K F) => (x : Place K F → F)) hrp
    simp only [Subalgebra.coe_add, Subalgebra.coe_sub] at h'
    simpa using h'.symm
  rw [hsum]
  refine (Submodule.mem_dualAnnihilator μ).mp hμ _ (Submodule.add_mem_sup ?_ ?_)
  · exact hr
  · change (p : Place K F → F) ∈ globalSub K F
    rw [hf₀]
    exact diagonal_mem_globalSub f₀

theorem serrePairing_eq_of_cechH1ToH1_eq' (hRT : ResidueTheorem K F) {S₀ S₁ T₀ T₁ : Set (Place K F)}
    (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (ω : ↥(regularDifferentials K F)) (x : cechH1 S₀ S₁ (0 : Divisor K F)) (y : cechH1 T₀ T₁ (0 :
      Divisor K F))
    (h : cechH1ToH1 hS 0 x = cechH1ToH1 hT 0 y) :
    serrePairing hRT hS ω x = serrePairing hRT hT ω y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [cechH1ToH1_mk, cechH1ToH1_mk] at h
  rcases eq_or_ne (ω : Ω[F⁄K]) 0 with hω | hω
  · have hω' : ω = 0 := Subtype.ext hω
    rw [hω', map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  · rw [serrePairing_apply_mk_eq_weilOfKaehler_t0 hRT hS ω hω,
      serrePairing_apply_mk_eq_weilOfKaehler_t0 hRT hT ω hω]
    have hmem : weilOfKaehler K F hω ∈ omegaSpace (K := K) (F := F) (0 : Divisor K F) :=
      omegaSpace_antitone (canonicalDivisorOf_nonneg_of_mem_regularDifferentials_t0 hω ω.2)
        (weilOfKaehler_mem_omegaSpace_of_residueTheorem hRT hω)
    exact omegaSpace_zero_apply_eq_of_mk_eq hmem _ _ _ _ h

end Generic

end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Cohomology.Proofs.SerrePairingCechH1ToH1.AlgebraicCurve in
theorem _root_.AlgebraicCurve.serrePairing_eq_of_cechH1ToH1_eq {K : Type*} {F : Type*} [Field K]
  [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalDivisor (K := K) (F := F)] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {S₀ S₁ T₀ T₁ : Set (Place K F)}
    (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (ω : ↥(regularDifferentials K F)) (x : cechH1 S₀ S₁ (0 : Divisor K F)) (y : cechH1 T₀ T₁ (0 :
      Divisor K F))
    (h : cechH1ToH1 hS 0 x = cechH1ToH1 hT 0 y) :
    serrePairing hRT hS ω x = serrePairing hRT hT ω y :=
  serrePairing_eq_of_cechH1ToH1_eq' hRT hS hT ω x y h
end AlgebraicCurves.Cohomology.Proofs.SerrePairingCechH1ToH1
end ProofImplementation
