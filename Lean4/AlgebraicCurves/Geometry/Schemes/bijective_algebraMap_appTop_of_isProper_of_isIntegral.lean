/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Ext

/-!
# bijective algebra Map app Top of is Proper of is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_algebraMap_appTop_of_isProper_of_isIntegral


universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Polynomial


theorem _root_.AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX] [IsIntegral X] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom := by
  set φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom with hφ
  let _ : Nonempty (⊤ : X.Opens) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨⟨x, trivial⟩⟩
  let _ : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  refine ⟨φ.injective, fun a => ?_⟩
  let ψ : k[X] →+* Γ(X, ⊤) := Polynomial.eval₂RingHom φ a
  let g : X ⟶ Spec (CommRingCat.of k[X]) := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  let π : Spec (CommRingCat.of k[X]) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
  have hψC : ψ.comp (algebraMap k k[X]) = φ := by
    ext x
    simp [ψ, Polynomial.algebraMap_eq]
  have hfX : fX = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h1 := Scheme.toSpecΓ_naturality fX
    rw [← SpecMap_ΓSpecIso_hom] at h1
    calc fX = (fX ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
            rw [Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
      _ = X.toSpecΓ ≫ Spec.map fX.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
            rw [h1, Category.assoc]
      _ = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
            rw [← Spec.map_comp, hφ, CommRingCat.ofHom_hom]
  have hgπ : g ≫ π = fX := by
    rw [hfX]
    change (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k
      k[X])) = _
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψC]
  let _ : IsProper (g ≫ π) := by rw [hgπ]; infer_instance
  let _ : IsProper g := IsProper.of_comp g π
  by_cases hsurj : Function.Surjective g.base
  · exfalso
    let _ : Surjective g := ⟨hsurj⟩
    have hπ : UniversallyClosed π := UniversallyClosed.of_comp_surjective g π
    have hint : IsIntegralHom π :=
      IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hπ, inferInstance⟩
    have hI : (algebraMap k k[X]).IsIntegral := IsIntegralHom.SpecMap_iff.mp hint
    let _ : Algebra.IsIntegral k k[X] := ⟨hI⟩
    exact Polynomial.not_finite (Algebra.IsIntegral.finite (R := k) (A := k[X]))
  · obtain ⟨P, hP⟩ := not_forall.mp hsurj
    have hclosed : IsClosed (Set.range g.base) := g.isClosedMap.isClosed_range
    have hirr : IsIrreducible (Set.range g.base) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ g.base.hom.continuous.continuousOn
    set 𝔭 := PrimeSpectrum.vanishingIdeal (Set.range g.base) with h𝔭def
    have h𝔭 : 𝔭.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hirr
    have hrange : Set.range g.base = PrimeSpectrum.zeroLocus (𝔭 : Set k[X]) := by
      rw [h𝔭def, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact hclosed.closure_eq.symm
    have hne : 𝔭 ≠ ⊥ := by
      intro h
      apply hP
      have : P ∈ Set.range g.base := by
        rw [hrange, h, PrimeSpectrum.zeroLocus_bot]
        exact Set.mem_univ _
      exact this
    obtain ⟨p, hp𝔭, hp⟩ := h𝔭.exists_mem_prime_of_ne_bot hne
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k hp.irreducible
    obtain ⟨c, hc⟩ : ∃ c, p.IsRoot c := Polynomial.exists_root_of_degree_eq_one hdeg
    have hXc : Polynomial.X - Polynomial.C c ∈ 𝔭 := by
      obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot.mpr hc)
      have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hp.ne_zero hq
      rcases h𝔭.mem_or_mem (hq ▸ hp𝔭) with h | h
      · exact h
      · exfalso
        have hnd : p.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
        have h1 := congrArg Polynomial.natDegree hq
        rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero c) hq0,
          Polynomial.natDegree_X_sub_C, hnd] at h1
        have hq0' : q.natDegree = 0 := by omega
        have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq0'
        have hcoeff : q.coeff 0 ≠ 0 := by
          intro h0; apply hq0; rw [hqC, h0, map_zero]
        have hunit : IsUnit q := by
          rw [hqC]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcoeff)
        exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem _ h hunit)
    have hval : ∀ x : X, x ∉ X.basicOpen (a - φ c) := by
      intro x hx
      have hmem : g.base x ∈ PrimeSpectrum.zeroLocus (𝔭 : Set k[X]) := hrange ▸ ⟨x, rfl⟩
      have h2 : Polynomial.X - Polynomial.C c ∈ (g.base x).asIdeal := hmem hXc
      have h3 : (g.base x).asIdeal = Ideal.comap ψ (X.toSpecΓ.base x).asIdeal := rfl
      rw [h3, Ideal.mem_comap] at h2
      have h4 : ψ (Polynomial.X - Polynomial.C c) = a - φ c := by simp [ψ]
      rw [h4] at h2
      have h5 : x ∈ X.toSpecΓ ⁻¹ᵁ (PrimeSpectrum.basicOpen (a - φ c)) := by
        rw [Scheme.toSpecΓ_preimage_basicOpen]; exact hx
      exact (PrimeSpectrum.mem_basicOpen _ _).mp h5 h2
    have hbot : X.basicOpen (a - φ c) = ⊥ :=
      le_bot_iff.mp fun x hx => (hval x hx).elim
    have h0 := (basicOpen_eq_bot_iff _).mp hbot
    exact ⟨c, (sub_eq_zero.mp h0).symm⟩
end AlgebraicCurves.Geometry.Schemes.Proofs.bijective_algebraMap_appTop_of_isProper_of_isIntegral
end ProofImplementation
