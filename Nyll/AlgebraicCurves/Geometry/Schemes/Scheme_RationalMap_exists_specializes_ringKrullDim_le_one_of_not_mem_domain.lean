/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Nyll.AlgebraicCurves.Geometry.Schemes.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

/-!
# Scheme Rational Map exists specializes ring Krull Dim le one of not mem domain
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain

universe u

open CategoryTheory AlgebraicGeometry Topology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace FltWs29
namespace C4

theorem ringKrullDim_stalk_eq_height {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (a : U) :
    ringKrullDim (X.presheaf.stalk (a : X)) = (hU.primeIdealOf a).asIdeal.height := by
  have := hU.isLocalization_stalk a
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf a).asIdeal (X.presheaf.stalk
    (a : X))

theorem ringKrullDim_stalk_le_of_specializes {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (a b : U) (h : (a : X) ⤳ (b : X)) :
    ringKrullDim (X.presheaf.stalk (a : X)) ≤ ringKrullDim (X.presheaf.stalk (b : X)) := by
  rw [ringKrullDim_stalk_eq_height hU a, ringKrullDim_stalk_eq_height hU b]
  have hab : hU.primeIdealOf a ≤ hU.primeIdealOf b := by
    rw [PrimeSpectrum.le_iff_specializes]
    exact (Topology.IsInducing.subtypeVal.specializes_iff.mp h).map hU.isoSpec.hom.continuous
  exact_mod_cast Ideal.height_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hab)

theorem ringKrullDim_stalk_opens {X : Scheme.{u}} (U : X.Opens) (y : U) :
    ringKrullDim ((U : Scheme.{u}).presheaf.stalk y) = ringKrullDim (X.presheaf.stalk (y : X)) :=
  ringKrullDim_eq_of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv

theorem main
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) [IsAffine Y]
    (u : X ⤏ Y) (x : X) (hx : x ∉ u.domain) :
    ∃ z : X, z ∉ u.domain ∧ z ⤳ x ∧ ringKrullDim (X.presheaf.stalk z) ≤ 1 := by
  classical
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU'⟩
  set E' : Set (PrimeSpectrum Γ(X, U)) := ⇑hU'.fromSpec ⁻¹' ((u.domain : Set X)ᶜ) with hE'
  have hE'cl : IsClosed E' := (u.domain.isOpen.isClosed_compl).preimage hU'.fromSpec.continuous
  set I : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal E' with hIdef
  have hE'eq : PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) = E' := by
    rw [hIdef, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hE'cl.closure_eq]
  have memE' : ∀ w : PrimeSpectrum Γ(X, U), w ∈ E' ↔ I ≤ w.asIdeal := fun w => by
    rw [← hE'eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  set p : PrimeSpectrum Γ(X, U) := hU'.primeIdealOf ⟨x, hxU⟩ with hpdef
  have hfp : hU'.fromSpec p = x := hU'.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hpE' : p ∈ E' := by
    change hU'.fromSpec p ∈ (u.domain : Set X)ᶜ
    rw [hfp]; exact hx
  obtain ⟨q, hqmin, hqp⟩ := Ideal.exists_minimalPrimes_le ((memE' p).mp hpE')
  have hqprime : q.IsPrime := hqmin.1.1
  have hIq : I ≤ q := hqmin.1.2
  set qpt : PrimeSpectrum Γ(X, U) := ⟨q, hqprime⟩ with hqpt
  have hzE' : qpt ∈ E' := (memE' qpt).mpr hIq
  have hz_dom : hU'.fromSpec qpt ∉ u.domain := hzE'
  have hzx : hU'.fromSpec qpt ⤳ x := by
    have h1 : qpt ⤳ p := (PrimeSpectrum.le_iff_specializes qpt p).mp hqp
    have h2 := h1.map hU'.fromSpec.continuous
    rwa [hfp] at h2
  have hfU : ∀ w : PrimeSpectrum Γ(X, U), hU'.fromSpec w ∈ U := fun w => by
    have : hU'.fromSpec w ∈ Set.range ⇑hU'.fromSpec := ⟨w, rfl⟩
    rwa [hU'.range_fromSpec] at this
  refine ⟨hU'.fromSpec qpt, hz_dom, hzx, ?_⟩
  by_contra hdim
  set S : Set (Ideal Γ(X, U)) := I.minimalPrimes \ {q} with hS
  have hSfin : S.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing Γ(X, U) I).subset
    Set.sdiff_subset
  set C : Set (PrimeSpectrum Γ(X, U)) := ⋃ q' ∈ S, PrimeSpectrum.zeroLocus (q' : Set Γ(X, U)) with
    hCdef
  have hC : IsClosed C := hSfin.isClosed_biUnion fun q' _ => PrimeSpectrum.isClosed_zeroLocus _
  set N' : (Spec Γ(X, U)).Opens := ⟨Cᶜ, hC.isOpen_compl⟩ with hN'
  have hqN' : qpt ∈ N' := by
    change qpt ∉ C
    intro hmem
    obtain ⟨q', hq'S, hq'⟩ := Set.mem_iUnion₂.mp hmem
    have hle : q' ≤ q := SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hq')
    have : q' = q := le_antisymm hle (hqmin.2 ⟨hq'S.1.1.1, hq'S.1.1.2⟩ hle)
    exact hq'S.2 this
  have key : ∀ w ∈ N', w ∈ E' → q ≤ w.asIdeal := by
    intro w hwN hwE
    have : w.asIdeal.IsPrime := w.isPrime
    obtain ⟨q'', hq''min, hq''w⟩ := Ideal.exists_minimalPrimes_le ((memE' w).mp hwE)
    by_cases h : q'' = q
    · exact h ▸ hq''w
    · exact absurd (Set.mem_iUnion₂.mpr ⟨q'', ⟨hq''min, h⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr
        hq''w⟩) hwN
  set N : X.Opens := hU'.fromSpec ''ᵁ N' with hNdef
  have hzN : hU'.fromSpec qpt ∈ N := ⟨qpt, hqN', rfl⟩
  have hNdim : ∀ w : X, w ∈ N → w ∉ u.domain → ¬ ringKrullDim (X.presheaf.stalk w) ≤ 1 := by
    rintro _ ⟨w', hw'N, rfl⟩ hw_dom hle
    have hqw : q ≤ w'.asIdeal := key w' hw'N hw_dom
    have hsp : hU'.fromSpec qpt ⤳ hU'.fromSpec w' :=
      ((PrimeSpectrum.le_iff_specializes qpt w').mp hqw).map hU'.fromSpec.continuous
    exact hdim ((ringKrullDim_stalk_le_of_specializes hU' ⟨_, hfU qpt⟩ ⟨_, hfU w'⟩ hsp).trans hle)
  have hT : ∀ y : (N : Scheme.{u}), IsDomain ((N : Scheme.{u}).presheaf.stalk y) ∧
      IsIntegrallyClosed ((N : Scheme.{u}).presheaf.stalk y) := fun y => by
    have := hX y.1
    exact ⟨(N.stalkIso y).commRingCatIsoToRingEquiv.toMulEquiv.isDomain,
      IsIntegrallyClosed.of_equiv (N.stalkIso y).commRingCatIsoToRingEquiv.symm⟩
  set V : (N : Scheme.{u}).Opens := N.ι ⁻¹ᵁ u.domain with hVdef
  have hV : ∀ y : (N : Scheme.{u}), ringKrullDim ((N : Scheme.{u}).presheaf.stalk y) ≤ 1 → y ∈ V :=
    by
    intro y hy
    by_contra hyV
    exact hNdim y.1 y.2 hyV ((ringKrullDim_stalk_opens N y).ge.trans hy)
  have hrange : Set.range ⇑(V.ι ≫ N.ι) ⊆ Set.range ⇑u.domain.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact t.2
  set ι' := IsOpenImmersion.lift u.domain.ι (V.ι ≫ N.ι) hrange with hι'def
  have hι' : ι' ≫ u.domain.ι = V.ι ≫ N.ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, -⟩ :=
    AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
    hT V hV (ι' ≫ u.toPartialMap.hom)
  have hNdense : Dense (N : Set X) := N.isOpen.dense ⟨_, hzN⟩
  set g : X.PartialMap Y := ⟨N, hNdense, φ⟩ with hgdef
  have hequiv : g.equiv u.toPartialMap := by
    have hWdense : Dense ((N ⊓ u.domain : X.Opens) : Set X) :=
      hNdense.inter_of_isOpen_left u.dense_domain N.isOpen
    refine ⟨N ⊓ u.domain, hWdense, inf_le_left, inf_le_right, ?_⟩
    change X.homOfLE (inf_le_left : N ⊓ u.domain ≤ N) ≫ φ =
      X.homOfLE (inf_le_right : N ⊓ u.domain ≤ u.domain) ≫ u.toPartialMap.hom
    have hrangeW : Set.range ⇑(X.homOfLE (inf_le_left : N ⊓ u.domain ≤ N)) ⊆ Set.range ⇑V.ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (X.homOfLE _ ≫ N.ι) t ∈ u.domain
      rw [Scheme.homOfLE_ι]
      exact t.2.2
    set l := IsOpenImmersion.lift V.ι (X.homOfLE (inf_le_left : N ⊓ u.domain ≤ N)) hrangeW with
      hldef
    have hl : l ≫ V.ι = X.homOfLE _ := IsOpenImmersion.lift_fac _ _ _
    change X.homOfLE _ ≫ φ = X.homOfLE _ ≫ u.toPartialMap.hom
    erw [← hl, Category.assoc, hφ, ← Category.assoc]
    congr 1
    erw [← cancel_mono u.domain.ι, Category.assoc, hι', ← Category.assoc, hl, Scheme.homOfLE_ι]
    exact (X.homOfLE_ι _).symm
  have hgu : g.toRationalMap = u := by
    rw [Scheme.PartialMap.toRationalMap_eq_iff.mpr hequiv,
      Scheme.RationalMap.toRationalMap_toPartialMap]
  have hzdom : hU'.fromSpec qpt ∈ g.toRationalMap.domain := g.le_domain_toRationalMap hzN
  rw [hgu] at hzdom
  exact hz_dom hzdom

end FltWs29.C4

end Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain in
theorem exists_specializes_ringKrullDim_le_one_of_not_mem_domain
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) [IsAffine Y]
    (u : X ⤏ Y) (x : X) (hx : x ∉ u.domain) :
    ∃ z : X, z ∉ u.domain ∧ z ⤳ x ∧ ringKrullDim (X.presheaf.stalk z) ≤ 1 :=
  FltWs29.C4.main hX u x hx
end AlgebraicGeometry.Scheme.RationalMap
end ProofImplementation
