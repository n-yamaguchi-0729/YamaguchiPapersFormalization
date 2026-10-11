/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Place_exists_comap_eq_toValuationSubring
import Nyll.AlgebraicCurves.Places.Place_exists_toValuationSubring_eq_comap_of_ne_top
import Nyll.AlgebraicCurves.Places.Place_ord_algebraMap_eq_mul_ord_of_constant_extension
import Nyll.AlgebraicCurves.Places.Place_ord_algebraMap

/-!
# Place exists place comap eq and ord eq mul ord of forall smul maximal Ideal map eq pow
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Pic.baseChange_mk
  AlgebraicCurve.Place.forgetConstants_toValuationSubring
  AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants
  AlgebraicCurve.Place.extendConstants_toValuationSubring
  AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring
  AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open _root_.AlgebraicCurve
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace ConjugateCore
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section OrdHelper
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_eq_of_span_eq_pow' (v : Place K F) {f : ↥v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {f} = IsLocalRing.maximalIdeal ↥v.toValuationSubring ^ n) : v.ord (f : F) = n
      := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥v.toValuationSubring
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
  have h1 : (f : ↥v.toValuationSubring) = ϖ ^ n * ((u⁻¹ : (↥v.toValuationSubring)ˣ) :
    ↥v.toValuationSubring) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have h2 := congrArg (fun x : ↥v.toValuationSubring => (x : F)) h1
  simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h2
  rw [h2, mul_comm, ← zpow_natCast, v.ord_unit_smul_zpow _ hϖ]

end OrdHelper

end AlgebraicCurve.Place.ConjugateCore

end Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow
end AlgebraicCurves.Places.Proofs

namespace AlgebraicCurve.Place

open AlgebraicCurve
open scoped Pointwise

open _root_.AlgebraicCurves.Places.Proofs in
open Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow in
open AlgebraicCurve.Place.ConjugateCore in
theorem exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow
    {κ k F 𝓕 F' : Type*} [Field κ] [Field k] [Field F] [Field 𝓕] [Field F']
    [Algebra κ k] [Algebra.IsAlgebraic κ k] [Algebra.IsSeparable κ k] [Algebra κ F] [Algebra k 𝓕]
      [Algebra k F']
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (hGκ : ∀ (g : G) (c : κ), g • algebraMap κ F c = algebraMap κ F c)
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P] (hκP : ∀ c : κ, algebraMap κ F c ∈ P)
    (n : ℕ)
    [IsDiscreteValuationRing ↥(P.comap (FixedPoints.subfield G F).subtype)]
    (hcoreG : ∀ (g : G) (Q : ValuationSubring F), Q = g • P →
      ∀ (j : ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥Q),
      (∀ r, ((j r : ↥Q) : F) = ((r : ↥(FixedPoints.subfield G F)) : F)) →
      Ideal.map j (IsLocalRing.maximalIdeal ↥(P.comap (FixedPoints.subfield G F).subtype))
        = IsLocalRing.maximalIdeal ↥Q ^ n)
    (htrans : ∀ Q : ValuationSubring F, Q ≠ ⊤ →
      (∀ e : ↥(FixedPoints.subfield G F), (e : F) ∈ Q ↔ (e : F) ∈ P) → ∃ g : G, Q = g • P)
    (θE : ↥(FixedPoints.subfield G F) →+* 𝓕) (φ : F →+* F') (ι : 𝓕 →+* F')
    (hsq : ∀ e : ↥(FixedPoints.subfield G F), ι (θE e) = φ (e : F))
    (hθEκ : ∀ c : κ, θE ⟨algebraMap κ F c, fun g => hGκ g c⟩ = algebraMap k 𝓕 (algebraMap κ k c))
    (hφκ : ∀ c : κ, φ (algebraMap κ F c) = algebraMap k F' (algebraMap κ k c))
    (hιk : ∀ c : k, ι (algebraMap k 𝓕 c) = algebraMap k F' c)
    (hgen𝓕 : Algebra.adjoin k (Set.range θE) = ⊤)
    (hgenF' : Algebra.adjoin k (Set.range φ) = ⊤)
    (hfinsep : letI := ι.toAlgebra; FiniteDimensional 𝓕 F' ∧ Algebra.IsSeparable 𝓕 F')
    (w : Place k 𝓕) (hw : ∀ e : ↥(FixedPoints.subfield G F), θE e ∈ w.toValuationSubring ↔ (e : F)
      ∈ P) :
    ∃ x' : Place k F',
      (∀ f : 𝓕, ι f ∈ x'.toValuationSubring ↔ f ∈ w.toValuationSubring) ∧
      ∀ f : 𝓕, x'.ord (ι f) = n * w.ord f := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let Pb : ValuationSubring ↥(FixedPoints.subfield G F) := P.comap (FixedPoints.subfield G
    F).subtype
  have hPbmem : ∀ e : ↥(FixedPoints.subfield G F), e ∈ Pb ↔ (e : F) ∈ P := fun _ => Iff.rfl
  let algι : Algebra 𝓕 F' := ι.toAlgebra
  obtain ⟨hfin, hsep⟩ := hfinsep
  have := hfin; have := hsep
  have : IsScalarTower k 𝓕 F' := IsScalarTower.of_algebraMap_eq (fun c => (hιk c).symm)
  obtain ⟨x', hx'⟩ := AlgebraicCurve.Place.exists_comap_eq_toValuationSubring (K := k) (F := 𝓕) (F'
    := F') w
  have hmem : ∀ f : 𝓕, ι f ∈ x'.toValuationSubring ↔ f ∈ w.toValuationSubring := fun f => by
    rw [← hx', ValuationSubring.mem_comap]; rfl
  refine ⟨x', hmem, ?_⟩
  have hQκ : ∀ c : κ, φ (algebraMap κ F c) ∈ x'.toValuationSubring := fun c => by
    rw [hφκ]; exact x'.algebraMap_mem' _
  have hQE : ∀ e : ↥(FixedPoints.subfield G F), (e : F) ∈ x'.toValuationSubring.comap φ ↔ (e : F) ∈
    P := fun e => by
    rw [ValuationSubring.mem_comap, ← hsq, hmem, hw]
  obtain ⟨ϖb, hϖb⟩ := IsDiscreteValuationRing.exists_irreducible ↥Pb
  have hϖb0 : ((ϖb : ↥(FixedPoints.subfield G F)) : F) ≠ 0 := by
    intro h; apply hϖb.ne_zero; exact Subtype.ext (Subtype.ext h)
  have hϖbP : ((ϖb : ↥(FixedPoints.subfield G F)) : F) ∈ P := (hPbmem _).1 ϖb.2
  have hϖbinv : ((ϖb : ↥(FixedPoints.subfield G F)) : F)⁻¹ ∉ P := by
    intro hinv
    apply hϖb.not_isUnit
    have hinvb : ((ϖb : ↥(FixedPoints.subfield G F))⁻¹ : ↥(FixedPoints.subfield G F)) ∈ Pb :=
      by rw [hPbmem]; simpa using hinv
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinvb⟩, Subtype.ext ?_⟩
    simp only [OneMemClass.coe_one]
    exact mul_inv_cancel₀ (fun h => hϖb0 (by rw [h]; rfl))
  have hQne : x'.toValuationSubring.comap φ ≠ ⊤ := by
    intro htop
    have : ((ϖb : ↥(FixedPoints.subfield G F))⁻¹ : ↥(FixedPoints.subfield G F)).1 ∈
      x'.toValuationSubring.comap φ := by rw [htop]; trivial
    rw [hQE] at this
    exact hϖbinv (by simpa using this)
  obtain ⟨x, hx⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top (K := κ) φ x'
    hQκ hQne
  obtain ⟨g, hg⟩ := htrans x.toValuationSubring x.ne_top' (fun e => by rw [hx]; exact hQE e)
  let jx : ↥Pb →+* ↥x.toValuationSubring :=
    { toFun := fun r => ⟨((r : ↥(FixedPoints.subfield G F)) : F), by
        rw [hx, hQE]
        exact (hPbmem _).1 r.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hjx : ∀ r, ((jx r : ↥x.toValuationSubring) : F) = ((r : ↥(FixedPoints.subfield G F)) : F) :=
    fun _ => rfl
  have hcore := hcoreG g x.toValuationSubring hg jx hjx
  let algκE : Algebra κ ↥(FixedPoints.subfield G F) := ((algebraMap κ F).codRestrict
    (FixedPoints.subfield G F).toSubring (fun c g => hGκ g c)).toAlgebra
  have hκE : ∀ c : κ, ((algebraMap κ ↥(FixedPoints.subfield G F) c : ↥(FixedPoints.subfield G F)) :
    F) = algebraMap κ F c := fun _ => rfl
  have : IsScalarTower κ ↥(FixedPoints.subfield G F) F := IsScalarTower.of_algebraMap_eq (fun c =>
    (hκE c).symm)
  have hPbtop : Pb ≠ ⊤ := by
    intro htop
    have hmemtop : ((ϖb : ↥(FixedPoints.subfield G F))⁻¹ : ↥(FixedPoints.subfield G F)) ∈ (⊤ :
      ValuationSubring ↥(FixedPoints.subfield G F)) :=
      ValuationSubring.mem_top _
    rw [← htop, hPbmem] at hmemtop
    exact hϖbinv (by simpa using hmemtop)
  let y : AlgebraicCurve.Place κ ↥(FixedPoints.subfield G F) :=
    ⟨Pb, fun c => by rw [hPbmem, hκE]; exact hκP c, hPbtop, inferInstance⟩
  have hu : y.ord ((ϖb : ↥Pb) : ↥(FixedPoints.subfield G F)) = 1 := y.ord_coe_irreducible hϖb
  have hn : x.ord (algebraMap ↥(FixedPoints.subfield G F) F ((ϖb : ↥Pb) : ↥(FixedPoints.subfield G
    F))) = n := by
    have h1 : Ideal.span {jx ϖb} = IsLocalRing.maximalIdeal ↥x.toValuationSubring ^ n := by
      rw [← hcore, hϖb.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    exact ord_eq_of_span_eq_pow' x h1
  let algEF : Algebra ↥(FixedPoints.subfield G F) 𝓕 := θE.toAlgebra
  let algFF' : Algebra F F' := φ.toAlgebra
  let algκ𝓕 : Algebra κ 𝓕 := ((algebraMap k 𝓕).comp (algebraMap κ k)).toAlgebra
  let algκF' : Algebra κ F' := ((algebraMap k F').comp (algebraMap κ k)).toAlgebra
  have : IsScalarTower κ k 𝓕 := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower κ k F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower κ ↥(FixedPoints.subfield G F) 𝓕 := IsScalarTower.of_algebraMap_eq (fun c =>
    by
    change algebraMap k 𝓕 (algebraMap κ k c) = θE (algebraMap κ ↥(FixedPoints.subfield G F) c)
    exact (hθEκ c).symm)
  have : IsScalarTower κ F F' := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k F' (algebraMap κ k c) = φ (algebraMap κ F c)
    rw [hφκ])
  have hsq' : ∀ e : ↥(FixedPoints.subfield G F), algebraMap F F' (algebraMap ↥(FixedPoints.subfield
    G F) F e) = algebraMap 𝓕 F' (algebraMap ↥(FixedPoints.subfield G F) 𝓕 e) :=
    fun e => (hsq e).symm
  have hgenE : Algebra.adjoin ↥(FixedPoints.subfield G F) (Set.range (algebraMap k 𝓕)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ (Algebra.adjoin k (Set.range θE)).toSubsemiring := by rw [hgen𝓕]; trivial
    change z ∈ Subsemiring.closure (Set.range (algebraMap k 𝓕) ∪ Set.range θE) at hz
    change z ∈ Subsemiring.closure (Set.range (algebraMap ↥(FixedPoints.subfield G F) 𝓕) ∪
      Set.range (algebraMap k 𝓕))
    rwa [Set.union_comm]
  have hgenF : Algebra.adjoin F (Set.range (algebraMap k F')) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ (Algebra.adjoin k (Set.range φ)).toSubsemiring := by rw [hgenF']; trivial
    change z ∈ Subsemiring.closure (Set.range (algebraMap k F') ∪ Set.range φ) at hz
    change z ∈ Subsemiring.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k F'))
    rwa [Set.union_comm]
  have hxx' : x'.toValuationSubring.comap (algebraMap F F') = x.toValuationSubring := hx.symm
  have hyw : w.toValuationSubring.comap (algebraMap ↥(FixedPoints.subfield G F) 𝓕) =
    y.toValuationSubring := by
    ext e
    rw [ValuationSubring.mem_comap]
    exact (hw e).trans (hPbmem e).symm
  have hx'w : x'.toValuationSubring.comap (algebraMap 𝓕 F') = w.toValuationSubring := hx'
  intro f
  exact AlgebraicCurve.Place.ord_algebraMap_eq_mul_ord_of_constant_extension
    (k := κ) (K := k) (E := ↥(FixedPoints.subfield G F)) (F := F) (E' := 𝓕) (F' := F')
    hsq' hgenE hgenF x y x' w hxx' hyw hx'w n ((ϖb : ↥Pb) : ↥(FixedPoints.subfield G F)) hu hn f
end AlgebraicCurve.Place
end ProofImplementation
