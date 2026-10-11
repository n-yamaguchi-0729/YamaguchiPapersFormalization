/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ResidueLift
import Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedCompletion

/-!
# Trivializing a chosen finite étale local factor after a finite residue lift

Suppose `R → B` is a local map inducing an isomorphism on residue fields and
`D / B` is finite étale local.  Lift the actual finite separable residue field
`κ(D) / κ(R)` to the explicit finite étale local `R`-algebra constructed in
`CompleteFiniteEtaleResidueLift`.  After base change to `B`, that lift is
isomorphic to `D`.

The proof is concrete.  Hensel's lemma lifts the distinguished residue
generator to a root in `D`; residue generation and Nakayama make the resulting
tensor-product map surjective, and equality of the finite free ranks makes it
an isomorphism.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial
open scoped TensorProduct

universe u

/-- A finite integral algebra with a unique prime over the closed point of a
local base is local.  No separable-closedness hypothesis is involved. -/
theorem isLocalRing_of_unique_prime_over_maximal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q = q) :
    IsLocalRing S := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hq_maximal : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q <| by
      rw [← q.over_def (IsLocalRing.maximalIdeal R)]
      exact IsLocalRing.maximalIdeal.isMaximal R
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq_maximal, ?_⟩
  intro Q hQ_maximal
  let : Q.IsPrime := hQ_maximal.isPrime
  have hQ_under_maximal : (Q.under R).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) Q
  have hQ_over : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
    { over := (IsLocalRing.eq_maximalIdeal hQ_under_maximal).symm }
  exact hunique Q inferInstance hQ_over

/-- The algebra map to the unique chosen factor is local. -/
theorem isLocalHom_of_unique_prime_over_maximal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q = q) :
    letI : IsLocalRing S :=
      isLocalRing_of_unique_prime_over_maximal q hunique
    IsLocalHom (algebraMap R S) := by
  let : IsLocalRing S :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hq_maximal : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q <| by
      rw [← q.over_def (IsLocalRing.maximalIdeal R)]
      exact IsLocalRing.maximalIdeal.isMaximal R
  have hq_eq : q = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hq_maximal
  have hcomap :
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S) =
        IsLocalRing.maximalIdeal R := by
    rw [← hq_eq]
    exact (q.over_def (IsLocalRing.maximalIdeal R)).symm
  exact ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp hcomap

/-- A finite étale unique chosen factor is faithfully flat over the local
base. -/
theorem faithfullyFlat_of_unique_prime_over_maximal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q = q) :
    letI : IsLocalRing S :=
      isLocalRing_of_unique_prime_over_maximal q hunique
    Module.FaithfullyFlat R S := by
  let : IsLocalRing S :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap R S) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A finite étale local factor over a complete local algebra with unchanged
residue field becomes the base change of the explicit finite residue lift.

The finite-dimensionality and separability hypotheses are facts about the
actual residue extension.  The iterated-root-cover consumer below produces
them from finite étaleness and residue preservation. -/
theorem exists_baseChange_finiteEtaleResidueLift_algEquiv_of_residue_bijective
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra B D] [Algebra R D] [IsScalarTower R B D]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing D]
    [IsLocalHom (algebraMap R B)] [IsLocalHom (algebraMap B D)]
    [IsLocalHom (algebraMap R D)]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite B D] [Algebra.Etale B D]
    [FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField D)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField D)]
    (hresidue : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R B))) :
    Nonempty ((B ⊗[R]
      FiniteEtaleResidueLift R (IsLocalRing.ResidueField D)) ≃ₐ[B] D) := by
  let : Module.FaithfullyFlat B D :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let k := IsLocalRing.ResidueField R
  let kB := IsLocalRing.ResidueField B
  let l := IsLocalRing.ResidueField D
  let : FiniteDimensional k l := inferInstanceAs <|
    FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField D)
  let : Algebra.IsSeparable k l := inferInstanceAs <|
    Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField D)
  let pb : PowerBasis k l := finiteEtaleResidueLiftPowerBasis R l
  let f : R[X] := finiteEtaleResidueLiftPolynomial R l
  let C := FiniteEtaleResidueLift R l
  let X := B ⊗[R] C
  let : Module.Free R C :=
    (finiteEtaleResidueLiftPolynomial_monic R l).free_adjoinRoot
  let : Module.Finite R C := moduleFinite_finiteEtaleResidueLift R l
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift R l
  let : FaithfulSMul R C := faithfulSMul_finiteEtaleResidueLift R l
  let : Algebra.Etale R C := etale_finiteEtaleResidueLift R l
  let : Module.Free B D := Module.free_of_flat_of_isLocalRing
  let : HenselianLocalRing D :=
    henselianLocalRing_of_finiteEtale_local_of_isAdicComplete
      (R := B) (S := D)
  let eResidue : k ≃ₐ[k] kB :=
    AlgEquiv.ofBijective (Algebra.ofId k kB) hresidue
  have hgen_kB : Algebra.adjoin kB {pb.gen} = ⊤ := by
    have hgen_k : Algebra.adjoin k {pb.gen} = ⊤ := pb.adjoin_gen_eq_top
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
      at hgen_k
    intro y
    obtain ⟨p, hp⟩ := hgen_k y
    refine ⟨p.map (algebraMap k kB), ?_⟩
    rw [← hp, Polynomial.aeval_map_algebraMap]
  let g : D[X] := f.map (algebraMap R D)
  have hg_monic : g.Monic :=
    (finiteEtaleResidueLiftPolynomial_monic R l).map (algebraMap R D)
  have haeval_base_change (p : R[X]) :
      aeval pb.gen (p.map (algebraMap R D)) =
        aeval pb.gen (p.map (IsLocalRing.residue R)) := by
    have hD : aeval pb.gen p =
        aeval pb.gen (p.map (algebraMap R D)) :=
      Polynomial.aeval_eq_aeval_map
        (R := R) (S := l) (T := D)
        (by ext x; exact IsLocalRing.ResidueField.algebraMap_residue x)
        p pb.gen
    have hk : aeval pb.gen p =
        aeval pb.gen (p.map (IsLocalRing.residue R)) :=
      Polynomial.aeval_eq_aeval_map
        (R := R) (S := l) (T := k)
        (by ext x; exact IsLocalRing.ResidueField.algebraMap_residue x)
        p pb.gen
    exact hD.symm.trans hk
  have hroot_residue : aeval pb.gen g = 0 := by
    change aeval pb.gen (f.map (algebraMap R D)) = 0
    rw [haeval_base_change]
    have hfmap : f.map (IsLocalRing.residue R) = minpoly k pb.gen := by
      simpa [f, pb, k, l] using finiteEtaleResidueLiftPolynomial_map R l
    rw [hfmap]
    exact minpoly.aeval k pb.gen
  have hderivative_residue : aeval pb.gen g.derivative ≠ 0 := by
    change aeval pb.gen (f.map (algebraMap R D)).derivative ≠ 0
    rw [Polynomial.derivative_map, haeval_base_change]
    have hmapDerivative :
        f.derivative.map (IsLocalRing.residue R) =
          (minpoly k pb.gen).derivative := by
      simpa [Polynomial.derivative_map, f, pb, k, l] using
        congrArg Polynomial.derivative
          (finiteEtaleResidueLiftPolynomial_map R l)
    rw [hmapDerivative]
    exact
      (Algebra.IsSeparable.isSeparable k pb.gen).aeval_derivative_ne_zero
        (minpoly.aeval k pb.gen)
  have h_hensel := ((HenselianLocalRing.TFAE D).out 1 2).mp
    (inferInstance : HenselianLocalRing D)
  obtain ⟨t, ht_root, ht_residue⟩ :=
    h_hensel g hg_monic pb.gen hroot_residue hderivative_residue
  have ht_gen : Algebra.adjoin B {t} = ⊤ :=
    (IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top t).1 <| by
      simpa [ht_residue] using hgen_kB
  have ht_root_R : aeval t f = 0 := by
    simpa [g, aeval_def] using ht_root
  let φC : C →ₐ[R] D :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R D) t ht_root_R
  let φR : X →ₐ[R] D :=
    Algebra.TensorProduct.lift
      ((Algebra.ofId B D).restrictScalars R) φC
      (fun _ _ ↦ .all _ _)
  let φ : X →ₐ[B] D :=
    { φR.toRingHom with
      commutes' := by
        intro b
        simp [φR, X] }
  have hφ_root : φ (1 ⊗ₜ[R] AdjoinRoot.root f) = t := by
    simpa [φ, φR, φC, X, C] using
      (AdjoinRoot.liftAlgHom_root f (Algebra.ofId R D) t ht_root_R)
  have hφ_surjective : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← ht_gen]
    apply Algebra.adjoin_le
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨1 ⊗ₜ[R] AdjoinRoot.root f, hφ_root⟩
  have hkB_finrank : Module.finrank k kB = 1 := by
    rw [← eResidue.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hresidue_finrank : Module.finrank k l = Module.finrank kB l := by
    have h := Module.finrank_mul_finrank k kB l
    rw [hkB_finrank, one_mul] at h
    exact h.symm
  have hfinrank : Module.finrank B X = Module.finrank B D := by
    calc
      Module.finrank B X = Module.finrank R C :=
        Module.finrank_baseChange
      _ = f.natDegree :=
        (AdjoinRoot.powerBasis'
          (finiteEtaleResidueLiftPolynomial_monic R l)).finrank
      _ = (minpoly k pb.gen).natDegree :=
        finiteEtaleResidueLiftPolynomial_natDegree R l
      _ = pb.dim := pb.natDegree_minpoly
      _ = Module.finrank k l := pb.finrank.symm
      _ = Module.finrank kB l := hresidue_finrank
      _ = Module.finrank B D :=
        (IsLocalRing.finrank_eq_finrank_residueField
          (R := B) (S := D)).symm
  exact ⟨AlgEquiv.ofBijective φ <|
    OrzechProperty.bijective_of_surjective_of_finrank_le
      φ.toLinearMap hφ_surjective hfinrank.le⟩

/-- A finite étale local algebra over a complete local algebra with unchanged
residue field is obtained by base change from a finite étale algebra over the
original local ring. -/
theorem exists_finiteEtaleResidueLift_of_residue_bijective
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra B D] [Algebra R D] [IsScalarTower R B D]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing D]
    [IsLocalHom (algebraMap R B)] [IsLocalHom (algebraMap B D)]
    [IsLocalHom (algebraMap R D)]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite B D] [Algebra.Etale B D]
    (hresidue : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R B))) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Finite R C) (_ : Algebra.Etale R C),
      Nonempty ((B ⊗[R] C) ≃ₐ[B] D) := by
  let : Module.FaithfullyFlat B D :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let k := IsLocalRing.ResidueField R
  let kB := IsLocalRing.ResidueField B
  let l := IsLocalRing.ResidueField D
  let eResidue : k ≃ₐ[k] kB :=
    AlgEquiv.ofBijective (Algebra.ofId k kB) hresidue
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l :=
    Algebra.IsSeparable.trans k kB l
  let C := FiniteEtaleResidueLift R l
  let : Module.Finite R C := moduleFinite_finiteEtaleResidueLift R l
  let : Algebra.Etale R C := etale_finiteEtaleResidueLift R l
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact exists_baseChange_finiteEtaleResidueLift_algEquiv_of_residue_bijective
    (R := R) (B := B) (D := D) hresidue

/-- Compatibility wrapper for the finite faithfully acted-on base changes
used by the chosen-factor constructions. -/
theorem exists_baseChange_finiteEtaleResidueLift_algEquiv
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra B D] [Algebra R D] [IsScalarTower R B D]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing D]
    [IsLocalHom (algebraMap R B)] [IsLocalHom (algebraMap B D)]
    [IsLocalHom (algebraMap R D)]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite R B] [FaithfulSMul R B]
    [Module.Finite B D] [FaithfulSMul B D] [Algebra.Etale B D]
    [FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField D)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField D)]
    (hresidue : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R B))) :
    Nonempty ((B ⊗[R]
      FiniteEtaleResidueLift R (IsLocalRing.ResidueField D)) ≃ₐ[B] D) :=
  exists_baseChange_finiteEtaleResidueLift_algEquiv_of_residue_bijective
    hresidue

namespace Kummer

/-- For a complete iterated positive root cover whose base maximal ideal is
finitely generated, a uniquely chosen finite étale factor is trivialized
after lifting only its actual finite residue extension to the original
complete base.  No Noetherian-ring or separably-closed-residue instance is
required. -/
theorem exists_baseChange_chosenFactorAlgEquiv_iteratedRadical_of_fg
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B := finite_iteratedRadical n a hn
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a hn
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              hmax n a hn ha
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a hn ha)
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          Nonempty ((B ⊗[A] FiniteEtaleResidueLift A l) ≃ₐ[B] D) := by
  dsimp only
  intro D _ _ _ _ _ _ q _ _ hunique
  let B := iteratedRadical A r n a
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    isAdicComplete_maximalIdeal_iteratedRadical_of_fg hmax n a hn ha
  let : IsLocalRing D :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    infer_instance
  let k := IsLocalRing.ResidueField A
  let kB := IsLocalRing.ResidueField B
  let l := IsLocalRing.ResidueField D
  let eResidue : k ≃ₐ[k] kB :=
    AlgEquiv.ofBijective (Algebra.ofId k kB)
      (residueFieldMap_bijective_iteratedRadical n a hn ha)
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  exact exists_baseChange_finiteEtaleResidueLift_algEquiv
    (R := A) (B := B) (D := D)
    (residueFieldMap_bijective_iteratedRadical n a hn ha)

/-- Noetherian specialization of
`exists_baseChange_chosenFactorAlgEquiv_iteratedRadical_of_fg`. -/
abbrev exists_baseChange_chosenFactorAlgEquiv_iteratedRadical
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :=
  @exists_baseChange_chosenFactorAlgEquiv_iteratedRadical_of_fg
    A _ _ _
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing r n a hn ha

end Kummer

end EtaleFundamentalGroups

end
