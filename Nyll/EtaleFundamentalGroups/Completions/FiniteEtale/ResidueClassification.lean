/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.Etale
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-!
# Finite étale local algebras over a complete local ring

Over a Noetherian complete local base, a finite étale local algebra is
complete, hence Henselian, for its own maximal ideal.  Two such algebras with
isomorphic residue extensions are isomorphic over the base.  This is the
finite-residue replacement for imposing a separably closed residue field in
the strict-Henselian splitting argument.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial
open ValuationTheory.DiscreteValuationField

universe u

/-- A finite étale local algebra over a Noetherian complete local ring is
complete for its maximal ideal. -/
theorem isAdicComplete_maximalIdeal_of_finiteEtale_local
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S] :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) S :=
    isAdicComplete_of_moduleFinite
      (I := IsLocalRing.maximalIdeal R) (M := S)
  have hm :
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
        IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← hm]
  exact (isAdicComplete_map_algebraMap_iff
    (R := R) (S := S) (IsLocalRing.maximalIdeal R)).2 hcomplete

/-- A finite étale local algebra over a Noetherian complete local ring is
Henselian local. -/
theorem henselianLocalRing_of_finiteEtale_of_isAdicComplete
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S] :
    HenselianLocalRing S := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal S) S :=
    isAdicComplete_maximalIdeal_of_finiteEtale_local (R := R) (S := S)
  let : HenselianRing S (IsLocalRing.maximalIdeal S) := inferInstance
  refine { is_henselian := ?_ }
  intro f hf x hx hderivative
  exact HenselianRing.is_henselian f hf x hx
    (hderivative.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)))

/-- Finite étale local algebras over a Noetherian complete local ring with
isomorphic residue-field extensions are isomorphic over the base. -/
theorem exists_finiteEtaleLocalAlgEquivOfResidueAlgEquiv
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S]
    [Module.Finite R T] [FaithfulSMul R T] [Algebra.Etale R T]
    (e : IsLocalRing.ResidueField S ≃ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField T) :
    Nonempty (S ≃ₐ[R] T) := by
  let : Module.Free R S := Module.free_of_flat_of_isLocalRing
  let : Module.Free R T := Module.free_of_flat_of_isLocalRing
  let : HenselianLocalRing T :=
    henselianLocalRing_of_finiteEtale_of_isAdicComplete (R := R) (S := T)
  obtain ⟨β, hβ⟩ := IsLocalRing.exists_adjoin_eq_top (R := R) (S := S)
  let f : R[X] := minpoly R β
  let g : T[X] := f.map (algebraMap R T)
  let β₀ : IsLocalRing.ResidueField S := IsLocalRing.residue S β
  let a₀ : IsLocalRing.ResidueField T := e β₀
  have hf_monic : f.Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral β)
  have hg_monic : g.Monic := hf_monic.map (algebraMap R T)
  have hf_residue : f.map (IsLocalRing.residue R) =
      minpoly (IsLocalRing.ResidueField R) β₀ := by
    simpa [f, β₀] using
      IsLocalRing.minpoly_map_residue (R := R) (S := S) hβ
  have hroot_β₀ : aeval β₀ (f.map (IsLocalRing.residue R)) = 0 := by
    rw [hf_residue]
    exact minpoly.aeval _ _
  have haeval_e (p : (IsLocalRing.ResidueField R)[X]) :
      aeval a₀ p = e (aeval β₀ p) := by
    have hmap := Polynomial.map_aeval_eq_aeval_map
      (R := IsLocalRing.ResidueField R)
      (S := IsLocalRing.ResidueField S)
      (T := IsLocalRing.ResidueField R)
      (U := IsLocalRing.ResidueField T)
      (φ := RingHom.id (IsLocalRing.ResidueField R))
      (ψ := e.toRingHom) (by ext; simp) p β₀
    simpa [a₀] using hmap.symm
  have haeval_base_change (p : R[X]) :
      aeval a₀ (p.map (algebraMap R T)) =
        aeval a₀ (p.map (IsLocalRing.residue R)) := by
    have hT : aeval a₀ p =
        aeval a₀ (p.map (algebraMap R T)) :=
      Polynomial.aeval_eq_aeval_map
        (R := R) (S := IsLocalRing.ResidueField T) (T := T)
        (by ext x; exact IsLocalRing.ResidueField.algebraMap_residue x)
        p a₀
    have hk : aeval a₀ p =
        aeval a₀ (p.map (IsLocalRing.residue R)) :=
      Polynomial.aeval_eq_aeval_map
        (R := R) (S := IsLocalRing.ResidueField T)
        (T := IsLocalRing.ResidueField R)
        (by ext x; rfl) p a₀
    exact hT.symm.trans hk
  have hroot_a₀_base : aeval a₀ (f.map (IsLocalRing.residue R)) = 0 := by
    rw [haeval_e, hroot_β₀, map_zero]
  have hroot_a₀ : aeval a₀ g = 0 := by
    change aeval a₀ (f.map (algebraMap R T)) = 0
    rw [haeval_base_change]
    exact hroot_a₀_base
  have hf_derivative_residue :
      aeval β₀ (f.derivative.map (IsLocalRing.residue R)) ≠ 0 := by
    have hderivative_map :
        f.derivative.map (IsLocalRing.residue R) =
          (minpoly (IsLocalRing.ResidueField R) β₀).derivative := by
      simpa [derivative_map] using
        congrArg Polynomial.derivative hf_residue
    rw [hderivative_map]
    exact
      (Algebra.IsSeparable.isSeparable
        (IsLocalRing.ResidueField R) β₀).aeval_derivative_ne_zero
          (minpoly.aeval _ _)
  have hg_derivative_residue : aeval a₀ g.derivative ≠ 0 := by
    intro hzero
    apply hf_derivative_residue
    apply e.injective
    rw [map_zero, ← haeval_e]
    change aeval a₀ (f.map (algebraMap R T)).derivative = 0 at hzero
    rw [derivative_map, haeval_base_change] at hzero
    exact hzero
  have h_hensel := ((HenselianLocalRing.TFAE T).out 1 2).mp
    (inferInstance : HenselianLocalRing T)
  obtain ⟨t, ht_root, ht_residue⟩ :=
    h_hensel g hg_monic a₀ hroot_a₀ hg_derivative_residue
  have hβ₀_gen : Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤ :=
    (IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top β).2 hβ
  have ha₀_gen : Algebra.adjoin (IsLocalRing.ResidueField R) {a₀} = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hβ₀_gen ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨p, hp⟩ := hβ₀_gen x
    refine ⟨p, ?_⟩
    rw [← hp]
    exact haeval_e p
  have ht_gen : Algebra.adjoin R {t} = ⊤ :=
    (IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top t).1 <| by
      simpa [ht_residue] using ha₀_gen
  let hS : IsAdjoinRootMonic S f :=
    IsAdjoinRootMonic.mkOfAdjoinEqTop' hβ
  have ht_root' : aeval t f = 0 := by
    simpa [g, aeval_def] using ht_root
  let φ : S →ₐ[R] T := hS.liftHom t ht_root'
  have hφ_surjective : Function.Surjective φ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at ht_gen
    intro y
    obtain ⟨p, hp⟩ := ht_gen y
    refine ⟨hS.map p, ?_⟩
    simpa [φ] using hp
  have hfinrank : Module.finrank R S = Module.finrank R T := by
    rw [IsLocalRing.finrank_eq_finrank_residueField (R := R) (S := S),
      IsLocalRing.finrank_eq_finrank_residueField (R := R) (S := T)]
    exact e.toLinearEquiv.finrank_eq
  exact ⟨AlgEquiv.ofBijective φ <|
    OrzechProperty.bijective_of_surjective_of_finrank_le
      φ.toLinearMap hφ_surjective hfinrank.le⟩

/-- A chosen algebra equivalence realizing the complete-local finite étale
residue classification. -/
noncomputable def finiteEtaleLocalAlgEquivOfResidueAlgEquiv
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S]
    [Module.Finite R T] [FaithfulSMul R T] [Algebra.Etale R T]
    (e : IsLocalRing.ResidueField S ≃ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField T) :
    S ≃ₐ[R] T :=
  Classical.choice (exists_finiteEtaleLocalAlgEquivOfResidueAlgEquiv e)

end EtaleFundamentalGroups

end
