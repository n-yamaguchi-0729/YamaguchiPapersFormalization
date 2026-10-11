/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalization
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalizationEtale
import Nyll.SchemeTheory.FiniteEtale.Henselian.PointedEtale
import Nyll.SchemeTheory.FiniteEtale.Henselian.Strict
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Closed-point local rings of a base-changed geometric stalk

Let `H` be the actual geometric etale stalk of `R`, and let `T` be a
strictly Henselian local `R`-algebra. At any prime of `T ⊗[R] H` over the
closed point of `T`, the map from `T` to the local ring is an isomorphism.

The proof uses actual affine etale representatives of individual germs.
After base change to `T`, the selected local factor of each representative
is finite etale and hence equal to `T`. Tensor induction handles numerators;
localness handles denominators, and faithful flatness gives injectivity.
No local-ring comparison or alternate presentation of the stalk is assumed.

This is the local algebra needed for the double and triple overlaps in
Stacks Project, Lemma 58.10.6 (https://stacks.math.columbia.edu/tag/0BSB).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem etale_hom_exists_base_preimage
    {T E L : Type u} [CommRing T] [CommRing E] [CommRing L]
    [Algebra T E] [Algebra T L] [HenselianLocalRing T] [IsLocalRing L]
    [IsSepClosed (IsLocalRing.ResidueField T)] [Algebra.Etale T E]
    [IsLocalHom (algebraMap T L)] (g : E →ₐ[T] L) (e : E) :
    ∃ t : T, algebraMap T L t = g e := by
  let P : Ideal E := (IsLocalRing.maximalIdeal L).comap g.toRingHom
  have : P.IsPrime := Ideal.comap_isPrime g.toRingHom (IsLocalRing.maximalIdeal L)
  have : P.LiesOver (IsLocalRing.maximalIdeal T) := by
    constructor
    change IsLocalRing.maximalIdeal T =
      ((IsLocalRing.maximalIdeal L).comap g.toRingHom).comap (algebraMap T E)
    rw [Ideal.comap_comap]
    have hcomp : g.toRingHom.comp (algebraMap T E) = algebraMap T L :=
      RingHom.ext g.commutes
    exact ((congrArg (fun f : T →+* L =>
      (IsLocalRing.maximalIdeal L).comap f) hcomp).trans
        (IsLocalRing.maximalIdeal_comap (algebraMap T L))).symm
  let Eₚ := Localization.AtPrime P
  have : Module.Finite T Eₚ :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale P
  have : Algebra.Etale T Eₚ :=
    etale_localizationAtPrime_of_henselian_of_etale P
  have : IsLocalHom (algebraMap T Eₚ) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal P
  have : Module.FaithfullyFlat T Eₚ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hbij : Function.Bijective (algebraMap T Eₚ) :=
    algebraMap_bijective_of_henselian_of_isSepClosed_residue_of_finiteEtale_local
      (R := T) (S := Eₚ)
  have hunit (s : P.primeCompl) : IsUnit (g s) := by
    have hs : g s ∉ IsLocalRing.maximalIdeal L := s.property
    exact not_not.mp hs
  let l : Eₚ →ₐ[T] L := IsLocalization.liftAlgHom hunit
  obtain ⟨t, ht⟩ := hbij.surjective (algebraMap E Eₚ e)
  refine ⟨t, ?_⟩
  calc
    algebraMap T L t = l (algebraMap T Eₚ t) := (l.commutes t).symm
    _ = l (algebraMap E Eₚ e) := congrArg l ht
    _ = g e := IsLocalization.lift_eq hunit e

/-- Any map from the actual geometric stalk into a local algebra of a
strictly Henselian ring takes every germ into the image of that ring.
The compatibility equation is the ordinary base-ring square of the map. -/
theorem geometricStalk_hom_exists_strictHenselian_preimage
    {R Ω T L : Type u} [CommRing R] [Field Ω] [CommRing T] [CommRing L]
    [Algebra R T] [Algebra R L] [Algebra T L] [IsScalarTower R T L]
    [HenselianLocalRing T] [IsLocalRing L]
    [IsSepClosed (IsLocalRing.ResidueField T)]
    [IsLocalHom (algebraMap T L)] (φ : R →+* Ω)
    (g : geometricStalk (Spec.map (CommRingCat.ofHom φ)) →+* L)
    (hg : g.comp (geometricStalkStructureMap φ) = algebraMap R L)
    (a : geometricStalk (Spec.map (CommRingCat.ofHom φ))) :
    ∃ t : T, algebraMap T L t = g a := by
  let s : Spec (.of Ω) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨W, w, z, hz⟩ := geometricStalk_exists_representative s a
  obtain ⟨V, v, j, hVaffine, hj⟩ := geometricStalk_exists_affine_refinement s W w
  have : IsAffine V.left := hVaffine
  let y : Γ(V.left, ⊤) := j.left.appTop z
  have hy : geometricStalkGerm s V v y = a := by
    have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
      j v (etaleSections (Spec (.of R)))
    rw [hj] at h
    exact (ConcreteCategory.congr_hom h z).trans hz
  let E := Γ(V.left, ⊤)
  let β : R →+* E := ((Scheme.ΓSpecIso (.of R)).inv ≫ V.hom.appTop).hom
  let : Algebra R E := β.toAlgebra
  have hβ : β.Etale := by
    change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).Etale
    apply RingHom.Etale.stableUnderComposition
    · exact RingHom.Etale.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (.of R)).inv).mp
          inferInstance)
    · exact HasRingHomProperty.appTop (P := @Etale)
        (show V.left ⟶ Spec (.of R) from V.hom) inferInstance
  have : Algebra.Etale R E := hβ
  let γ : E →ₐ[R] L :=
    { __ := g.comp (geometricStalkGerm s V v).hom
      commutes' r := by
        have hcoeff : geometricStalkGerm s V v (β r) =
            geometricStalkStructureMap φ r :=
          RingHom.congr_fun (geometricStalkGerm_comp_structure φ V v) r
        exact (congrArg g hcoeff).trans (RingHom.congr_fun hg r) }
  let δ : (T ⊗[R] E) →ₐ[T] L := (AlgHom.liftEquiv R T E L) γ
  obtain ⟨t, ht⟩ := etale_hom_exists_base_preimage δ (1 ⊗ₜ[R] y)
  refine ⟨t, ?_⟩
  calc
    algebraMap T L t = δ (1 ⊗ₜ[R] y) := ht
    _ = γ y := by
      rw [AlgHom.liftEquiv_tmul, one_smul]
    _ = g a := congrArg g hy

/-- The actual base-changed geometric stalk has the strictly Henselian
base as local ring at every point above its closed point. -/
theorem geometricStalk_tensor_localizationAtPrime_bijective
    {R Ω T : Type u} [CommRing R] [Field Ω] [CommRing T] [Algebra R T]
    [HenselianLocalRing T] [IsSepClosed (IsLocalRing.ResidueField T)]
    (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    ∀ (q : Ideal (T ⊗[R] H)) [q.IsPrime]
      [q.LiesOver (IsLocalRing.maximalIdeal T)],
      Function.Bijective (algebraMap T (Localization.AtPrime q)) := by
  intro H hH q hq hqover
  let B := T ⊗[R] H
  let L := Localization.AtPrime q
  have : Module.Flat R H := geometricStalkStructureMap_flat φ
  have : IsLocalHom (algebraMap T L) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal q
  have : Module.FaithfullyFlat T L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨FaithfulSMul.algebraMap_injective T L, ?_⟩
  let g : H →+* L := (algebraMap B L).comp
    (Algebra.TensorProduct.includeRight : H →ₐ[R] B).toRingHom
  have hg : g.comp (geometricStalkStructureMap φ) = algebraMap R L := by
    apply RingHom.ext
    intro r
    have hcoeff : (Algebra.TensorProduct.includeRight : H →ₐ[R] B)
        (algebraMap R H r) = algebraMap R B r :=
      (Algebra.TensorProduct.includeRight : H →ₐ[R] B).commutes r
    exact (congrArg (algebraMap B L) hcoeff).trans
      (IsScalarTower.algebraMap_apply R B L r).symm
  have hpreimage (b : B) : ∃ t : T, algebraMap T L t = algebraMap B L b := by
    induction b using TensorProduct.inductionOn with
    | tmul t a =>
      obtain ⟨r, hr⟩ := geometricStalk_hom_exists_strictHenselian_preimage
        (R := R) (Ω := Ω) (T := T) (L := L) φ g hg a
      refine ⟨t * r, ?_⟩
      calc
        algebraMap T L (t * r) = algebraMap T L t * g a := by rw [map_mul, hr]
        _ = algebraMap B L ((t ⊗ₜ[R] (1 : H)) * (1 ⊗ₜ[R] a)) := by
          rw [map_mul]
          change algebraMap T L t * g a =
            algebraMap B L (algebraMap T B t) * g a
          rw [← IsScalarTower.algebraMap_apply]
        _ = algebraMap B L (t ⊗ₜ[R] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add b c hb hc =>
      obtain ⟨t, ht⟩ := hb
      obtain ⟨r, hr⟩ := hc
      exact ⟨t + r, by rw [map_add, ht, hr, map_add]⟩
  intro x
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨t, ht⟩ := hpreimage b
  obtain ⟨d, hd⟩ := hpreimage s
  have hdunit : IsUnit d := IsLocalHom.map_nonunit d
    (hd.symm ▸ IsLocalization.map_units L s)
  obtain ⟨dunit, hdunit⟩ := hdunit
  refine ⟨t * ↑(dunit⁻¹), ?_⟩
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [← hd, ← hdunit, ← map_mul, mul_assoc, Units.inv_mul, mul_one, ht]

end EtaleFundamentalGroups.StrictHenselian
