/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.JacobsonSpace
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.RationalLocalization
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut

/-!
# Rigidity from algebraic-closure-valued points

Geometric points of the generic fibre are dense in a flat scheme of finite type.
For a reduced separated scheme this density detects equality of endomorphisms,
including over a localization of the rational integers.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.GeometricRigidity

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace RigidityGeomPoints

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K]

local notation "bK" => Spec.map (CommRingCat.ofHom (algebraMap R K))

omit [IsAlgClosed K] in
theorem range_specMap_eq (hinj : Function.Injective (algebraMap R K)) :
    Set.range (bK).base = {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) q.asIdeal = ⊥
    have hq : q.asIdeal = ⊥ := by
      have := q.isPrime
      exact Ideal.eq_bot_of_prime q.asIdeal
    rw [hq, Ideal.comap_bot_of_injective _ hinj]
  · rintro rfl
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj

theorem dense_preimage_genericPoint {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] :
    Dense (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) := by
  intro p
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ t.base p := by
    have hle : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ≤
        (t.base p : PrimeSpectrum R) := bot_le
    exact (PrimeSpectrum.le_iff_specializes
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) (t.base p : PrimeSpectrum R)).mp hle
  obtain ⟨q, hq, htq⟩ := Flat.generalizingMap t hgen
  have hqmem : q ∈ t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := htq
  apply closure_mono (Set.singleton_subset_iff.mpr hqmem)
  exact hq.mem_closure

theorem dense_range_of_points (hinj : Function.Injective (algebraMap R K))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t] :
    Dense (⋃ x : {x : Spec (CommRingCat.of K) ⟶ D // x ≫ t = bK},
      Set.range x.1.base) := by
  let P := pullback t bK
  have : LocallyOfFiniteType (pullback.snd t bK) := inferInstance
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (pullback.snd t bK)
  have hsub : (pullback.fst t bK).base '' closedPoints P ⊆
      ⋃ x : {x : Spec (CommRingCat.of K) ⟶ D // x ≫ t = bK}, Set.range x.1.base := by
    rintro _ ⟨p, hp, rfl⟩
    have hpClosed : IsClosed ({p} : Set P) := mem_closedPoints_iff.mp hp
    let y : {y : Spec (CommRingCat.of K) ⟶ P //
        y ≫ pullback.snd t bK = 𝟙 (Spec (CommRingCat.of K))} :=
      ⟨pointOfClosedPoint (pullback.snd t bK) p hpClosed,
        pointOfClosedPoint_comp (pullback.snd t bK) p hpClosed⟩
    have hy : y.1 ≫ pullback.fst t bK ≫ t = bK := by
      rw [pullback.condition, ← Category.assoc, y.2, Category.id_comp]
    refine Set.mem_iUnion.mpr ⟨⟨y.1 ≫ pullback.fst t bK, by rw [Category.assoc]; exact hy⟩,
      ⟨IsLocalRing.closedPoint K, ?_⟩⟩
    change (pullback.fst t bK).base (y.1.base (IsLocalRing.closedPoint K)) = _
    congr 1
    change (pointOfClosedPoint (pullback.snd t bK) p hpClosed)
      (IsLocalRing.closedPoint K) = p
    exact pointOfClosedPoint_apply (pullback.snd t bK) p hpClosed
      (IsLocalRing.closedPoint K)
  have hdenseP : Dense (closedPoints P) := by
    rw [dense_iff_closure_eq]
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := P) isOpen_univ.isLocallyClosed
    rw [Set.univ_inter, closure_univ] at this
    exact this
  have hrange : Set.range (pullback.fst t bK).base =
      t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
    rw [Scheme.Pullback.range_fst, range_specMap_eq hinj]
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro d
  have h1 : d ∈ closure (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) :=
    dense_preimage_genericPoint t d
  have h2 : t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} ⊆
      closure ((pullback.fst t bK).base '' closedPoints P) := by
    rw [← hrange]
    rintro _ ⟨p, rfl⟩
    have : p ∈ closure (closedPoints P) := hdenseP p
    exact (map_mem_closure (pullback.fst t bK).base.hom.continuous this fun q hq => ⟨q, hq, rfl⟩)
  have h3 := closure_mono h2
  rw [closure_closure] at h3
  exact closure_mono hsub (h3 h1)

theorem ext_of_forall_geometric_point (hinj : Function.Injective (algebraMap R K))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated t] [IsReduced D]
    (φ ψ : D ⟶ D) (hφ : φ ≫ t = t) (hψ : ψ ≫ t = t)
    (h : ∀ x : Spec (CommRingCat.of K) ⟶ D, x ≫ t = bK → x ≫ φ = x ≫ ψ) : φ = ψ := by
  let I := {x : Spec (CommRingCat.of K) ⟶ D // x ≫ t = bK}
  let W : Scheme.{u} := ∐ fun _ : I => Spec (CommRingCat.of K)
  let ι : W ⟶ D := Sigma.desc fun x : I => x.1
  have : IsDominant ι := by
    rw [isDominant_iff]
    have hd := dense_range_of_points (K := K) hinj t
    refine Dense.mono ?_ hd
    intro d hd'
    obtain ⟨x, ⟨p, rfl⟩⟩ := Set.mem_iUnion.mp hd'
    refine ⟨(Sigma.ι (fun _ : I => Spec (CommRingCat.of K)) x).base p, ?_⟩
    change (Sigma.ι (fun _ : I => Spec (CommRingCat.of K)) x ≫ ι).base p = _
    rw [Sigma.ι_comp_desc]
  refine ext_of_isDominant_of_isSeparated t (hφ.trans hψ.symm) ι ?_
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_comp_desc]
  exact h x.1 x.2

end RigidityGeomPoints

section RIGAssembly
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

theorem RigidityGeomPoints.algebraMap_ratLocalizedAt_injective (ℓ : ℕ) :
    Function.Injective (algebraMap ↥(Rat.LocalizationAt ℓ) (AlgebraicClosure ℚ)) := by
  rw [IsScalarTower.algebraMap_eq ↥(Rat.LocalizationAt ℓ) ℚ (AlgebraicClosure ℚ)]
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp Subtype.val_injective

theorem RigidityGeomPoints.rig
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(Rat.LocalizationAt ℓ)))
    (D : RelativePic0Designation ↥(Rat.LocalizationAt ℓ) c)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) [IsReduced D.P]
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(Rat.LocalizationAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  have := hsm
  have := hpr
  apply Subtype.ext
  exact RigidityGeomPoints.ext_of_forall_geometric_point (K := AlgebraicClosure ℚ)
    (RigidityGeomPoints.algebraMap_ratLocalizedAt_injective ℓ) D.toBase φ.1 ψ.1 φ.2 ψ.2
    (fun x hx => h ⟨x, hx⟩)

end RIGAssembly

open RigidityGeomPoints in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(Rat.LocalizationAt ℓ)))
    (D : RelativePic0Designation ↥(Rat.LocalizationAt ℓ) c)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    [IsReduced D.P]
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(Rat.LocalizationAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ :=
  rig ℓ c D hsm hpr φ ψ h
end JacobianVarieties.Picard.Proofs.GeometricRigidity
end ProofImplementation
