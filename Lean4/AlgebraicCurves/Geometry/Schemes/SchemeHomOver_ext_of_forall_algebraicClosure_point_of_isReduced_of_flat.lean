/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.JacobsonSpace
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Scheme Hom Over ext of forall algebraic Closure point of is Reduced of flat
-/

section ProofImplementation


namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

open Topology CategoryTheory.Limits

namespace RigKerGeomPoints

variable {R L : Type u} [CommRing R] [IsDomain R] [Field L] [IsAlgClosed L] [Algebra R L]

local notation "bL" => Spec.map (CommRingCat.ofHom (algebraMap R L))

omit [IsAlgClosed L] in
theorem range_specMap_eq (hinj : Function.Injective (algebraMap R L)) :
    Set.range (bL).base = {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) q.asIdeal = ⊥
    have hq : q.asIdeal = ⊥ := by
      let _ := q.isPrime
      exact Ideal.eq_bot_of_prime q.asIdeal
    rw [hq, Ideal.comap_bot_of_injective _ hinj]
  · rintro rfl
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj
omit [IsAlgClosed L] [Algebra R L] in
theorem dense_preimage_genericPoint {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] :
    Dense (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) := by
  intro p
  let η : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hgen : η ⤳ t.base p :=
    (PrimeSpectrum.le_iff_specializes (R := R) η (t.base p)).mp bot_le
  obtain ⟨q, hq, htq⟩ := Flat.generalizingMap t hgen
  have hqmem : q ∈ t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := htq
  apply closure_mono (Set.singleton_subset_iff.mpr hqmem)
  exact hq.mem_closure

theorem dense_range_of_points (hinj : Function.Injective (algebraMap R L))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t] :
    Dense (⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = bL},
      Set.range x.1.base) := by
  let P := pullback t bL
  let _ : LocallyOfFiniteType (pullback.snd t bL) := inferInstance
  let _ : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (pullback.snd t bL)
  have hsub : (pullback.fst t bL).base '' closedPoints P ⊆
      ⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = bL}, Set.range x.1.base := by
    rintro _ ⟨p, hp, rfl⟩
    let y := (pointEquivClosedPoint (pullback.snd t bL)).symm ⟨p, hp⟩
    have hy : y.1 ≫ pullback.fst t bL ≫ t = bL := by
      rw [pullback.condition, ← Category.assoc, y.2, Category.id_comp]
    refine Set.mem_iUnion.mpr ⟨⟨y.1 ≫ pullback.fst t bL, by rw [Category.assoc]; exact hy⟩,
      ⟨IsLocalRing.closedPoint L, ?_⟩⟩
    change (pullback.fst t bL).base (y.1.base (IsLocalRing.closedPoint L)) = _
    congr 1
    exact congrArg Subtype.val ((pointEquivClosedPoint (pullback.snd t bL)).apply_symm_apply ⟨p,
      hp⟩)
  have hdenseP : Dense (closedPoints P) := by
    rw [dense_iff_closure_eq]
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := P) isOpen_univ.isLocallyClosed
    rw [Set.univ_inter, closure_univ] at this
    exact this
  have hrange : Set.range (pullback.fst t bL).base = t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ :
    PrimeSpectrum R)} := by
    rw [Scheme.Pullback.range_fst, range_specMap_eq hinj]
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro d
  have h1 : d ∈ closure (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) :=
    dense_preimage_genericPoint t d
  have h2 : t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} ⊆
      closure ((pullback.fst t bL).base '' closedPoints P) := by
    rw [← hrange]
    rintro _ ⟨p, rfl⟩
    have : p ∈ closure (closedPoints P) := hdenseP p
    exact (map_mem_closure (pullback.fst t bL).base.hom.continuous this fun q hq => ⟨q, hq, rfl⟩)
  have h3 := closure_mono h2
  rw [closure_closure] at h3
  exact closure_mono hsub (h3 h1)

theorem ext_of_forall_geometric_point (hinj : Function.Injective (algebraMap R L))
    {Y X : Scheme.{u}} (t : Y ⟶ Spec (CommRingCat.of R)) (s : X ⟶ Spec (CommRingCat.of R))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated s] [IsReduced Y]
    (φ ψ : Y ⟶ X) (hφ : φ ≫ s = t) (hψ : ψ ≫ s = t)
    (h : ∀ x : Spec (CommRingCat.of L) ⟶ Y, x ≫ t = bL → x ≫ φ = x ≫ ψ) : φ = ψ := by
  let I := {x : Spec (CommRingCat.of L) ⟶ Y // x ≫ t = bL}
  let W : Scheme.{u} := ∐ fun _ : I => Spec (CommRingCat.of L)
  let ι : W ⟶ Y := Sigma.desc fun x : I => x.1
  let _ : IsDominant ι := by
    rw [isDominant_iff]
    have hd := dense_range_of_points (L := L) hinj t
    refine Dense.mono ?_ hd
    intro d hd'
    obtain ⟨x, ⟨p, rfl⟩⟩ := Set.mem_iUnion.mp hd'
    refine ⟨(Sigma.ι (fun _ : I => Spec (CommRingCat.of L)) x).base p, ?_⟩
    change (Sigma.ι (fun _ : I => Spec (CommRingCat.of L)) x ≫ ι).base p = _
    rw [Sigma.ι_comp_desc]
  refine ext_of_isDominant_of_isSeparated s (hφ.trans hψ.symm) ι ?_
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_comp_desc]
  exact h x.1 x.2

end RigKerGeomPoints

theorem
  _root_.AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar]
      [IsScalarTower R K Kbar]
    {Y X : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of R)} {gX : X ⟶ Spec (CommRingCat.of R)}
    [Flat gY] [LocallyOfFiniteType gY] [IsReduced Y] [IsSeparated gX]
    (φ ψ : SchemeHomOver gY gX)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gY, x.1 ≫ φ.1 = x.1
      ≫ ψ.1) :
    φ = ψ := by
  let _ : IsAlgClosed Kbar := IsAlgClosure.isAlgClosed K
  have hinj : Function.Injective (algebraMap R Kbar) := by
    rw [IsScalarTower.algebraMap_eq R K Kbar]
    exact (algebraMap K Kbar).injective.comp (IsFractionRing.injective R K)
  apply Subtype.ext
  exact RigKerGeomPoints.ext_of_forall_geometric_point (L := Kbar) hinj gY gX φ.1 ψ.1 φ.2 ψ.2
    (fun x hx => h ⟨x, hx⟩)
end SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
