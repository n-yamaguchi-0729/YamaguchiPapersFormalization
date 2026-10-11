/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactor
import EtaleFundamentalGroups.Purity.Local.CompleteQuotient

/-!
# Finite étale local algebras over complete local quotients

A finite étale local algebra over a quotient of a complete Noetherian local
ring is the base change of a finite étale algebra over the original ring.
The lift is the explicit monogenic lift of the residue-field extension.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u

/-- A surjective local homomorphism induces an isomorphism on residue fields. -/
theorem residueField_map_bijective_of_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Bijective (ResidueField.map f) := by
  refine ⟨(ResidueField.map f).injective, ?_⟩
  intro y
  obtain ⟨s, rfl⟩ := residue_surjective y
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨residue R r, ResidueField.map_residue f r⟩

/-- The algebra map of a finite extension between local rings is local. -/
theorem isLocalHom_algebraMap_of_moduleFinite_of_isLocalRing
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [Module.Finite R S] :
    IsLocalHom (algebraMap R S) := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hcomapMaximal :
      ((maximalIdeal S).comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) (maximalIdeal S)
  have hcomap :
      (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hcomapMaximal
  exact ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp hcomap

/-- Every finite étale local algebra over a proper quotient of a complete
Noetherian local ring is obtained by base change from an explicit finite
étale algebra over the original ring. -/
theorem exists_finiteEtaleLocal_lift_of_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {D : Type u} [CommRing D] [Algebra (R ⧸ I) D]
    [IsLocalRing D] [Module.Finite (R ⧸ I) D]
    [Algebra.Etale (R ⧸ I) D] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Finite R C) (_ : Algebra.Etale R C),
      Nonempty (((R ⧸ I) ⊗[R] C) ≃ₐ[R ⧸ I] D) := by
  let B := R ⧸ I
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R B) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : Algebra R D :=
    ((algebraMap B D).comp (algebraMap R B)).toAlgebra
  let : IsScalarTower R B D :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_algebraMap_of_moduleFinite_of_isLocalRing
  let : IsLocalHom (algebraMap R D) := by
    rw [IsScalarTower.algebraMap_eq R B D]
    infer_instance
  have hmaximal :
      (maximalIdeal R).map (algebraMap R B) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsAdicComplete (maximalIdeal B) B := by
    rw [← hmaximal]
    exact isAdicComplete_map_maximalIdeal_quotient I
  have hresidue : Function.Bijective
      (ResidueField.map (algebraMap R B)) :=
    residueField_map_bijective_of_surjective
      (algebraMap R B) Ideal.Quotient.mk_surjective
  exact exists_finiteEtaleResidueLift_of_residue_bijective
    (R := R) (B := B) (D := D) hresidue

end EtaleFundamentalGroups

end
