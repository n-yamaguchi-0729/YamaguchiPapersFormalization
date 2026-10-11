/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FiberQuotient
import EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Realization of explicit finite quotients by Galois covers

A continuous homomorphism from an etale fundamental group to a finite
discrete group has open normal kernel.  The Galois-category equivalence
therefore realizes that kernel by a pointed connected finite-etale Galois
cover.  When the homomorphism is surjective, the pointed deck quotient is
canonically isomorphic to the prescribed target group.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u v

variable {X : Scheme.{u}} [ConnectedSpace X]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- A continuous finite discrete representation is realized, at the level
of kernels, by the pointed quotient of an actual connected finite-etale
Galois cover. -/
theorem exists_galoisCover_quotient_ker_eq
    (xi : Spec (.of Omega) ⟶ X)
    (G : Type v) [Finite G] [Group G] [TopologicalSpace G]
    [DiscreteTopology G]
    (phi : π₁ᵉᵗ(xi) →ₜ* G) :
    ∃ (W : FiniteEtale X) (hW : IsGalois W)
      (w : (fiber xi).obj W),
      letI : IsGalois W := hW
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w).ker = phi.ker := by
  let U : OpenNormalSubgroup π₁ᵉᵗ(xi) :=
    ProCGroups.ProC.OpenNormalSubgroup.ker phi
  obtain ⟨W, hW, w, hw⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe
      (C := FiniteEtale X) (fiber xi) U
  let : IsGalois W := hW
  refine ⟨W, hW, w, ?_⟩
  calc
    (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w).ker = MulAction.stabilizer π₁ᵉᵗ(xi) w :=
      EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker
        xi W hW w
    _ = (U : Subgroup π₁ᵉᵗ(xi)) := hw
    _ = phi.ker := rfl

/-- Two surjective group homomorphisms with the same source and kernel have
canonically isomorphic targets. -/
private noncomputable def targetMulEquivOfSurjectiveOfKerEq
    {P A B : Type*} [Group P] [Group A] [Group B]
    (q : P →* A) (phi : P →* B)
    (hq : Function.Surjective q) (hphi : Function.Surjective phi)
    (hker : q.ker = phi.ker) : A ≃* B :=
  (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective phi hphi))

private theorem targetMulEquivOfSurjectiveOfKerEq_comp
    {P A B : Type*} [Group P] [Group A] [Group B]
    (q : P →* A) (phi : P →* B)
    (hq : Function.Surjective q) (hphi : Function.Surjective phi)
    (hker : q.ker = phi.ker) :
    (targetMulEquivOfSurjectiveOfKerEq q phi hq hphi hker).toMonoidHom.comp q = phi := by
  apply MonoidHom.ext
  intro g
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
    Function.comp_apply]
  apply phi.eq_iff.mpr
  rw [← hker]
  apply q.eq_iff.mp
  exact hq.hasRightInverse.choose_spec (q g)

/-- Every continuous surjection from an etale fundamental group to an
explicit finite discrete group is represented by an actual pointed connected
finite-etale Galois cover.  The displayed deck-group equivalence identifies
the pointed-cover quotient with the prescribed homomorphism, not merely its
kernel or its abstract target. -/
theorem exists_galoisCover_quotient_mulEquiv
    (xi : Spec (.of Omega) ⟶ X)
    (G : Type v) [Finite G] [Group G] [TopologicalSpace G]
    [DiscreteTopology G]
    (phi : π₁ᵉᵗ(xi) →ₜ* G) (hphi : Function.Surjective phi) :
    ∃ (W : FiniteEtale X) (hW : IsGalois W)
      (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G),
      letI : IsGalois W := hW
      e.toMonoidHom.comp
          (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
            xi W hW w) = phi.toMonoidHom := by
  obtain ⟨W, hW, w, hker⟩ :=
    exists_galoisCover_quotient_ker_eq xi G phi
  let : IsGalois W := hW
  let q := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
    xi W hW w
  have hq : Function.Surjective q :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective
      xi W hW w
  let e : (Aut W)ᵐᵒᵖ ≃* G :=
    targetMulEquivOfSurjectiveOfKerEq q phi.toMonoidHom hq hphi hker
  refine ⟨W, hW, w, e, ?_⟩
  exact targetMulEquivOfSurjectiveOfKerEq_comp
    q phi.toMonoidHom hq hphi hker

omit [ConnectedSpace X] in
/-- Mapping a deck subgroup through the equivalence in an explicit finite
quotient realization preserves its cardinality. -/
theorem quotientDeckMulEquiv_map_natCard
    {G : Type v} [Group G]
    {W : FiniteEtale X} (e : (Aut W)ᵐᵒᵖ ≃* G)
    (H : Subgroup (Aut W)ᵐᵒᵖ) :
    Nat.card (H.map e.toMonoidHom) = Nat.card H := by
  exact Subgroup.card_map_of_injective e.injective

omit [ConnectedSpace X] in
/-- Coprimality of a deck subgroup is unchanged after transport to an
explicit finite quotient group. -/
theorem quotientDeckMulEquiv_map_coprime_iff
    {G : Type v} [Group G]
    {W : FiniteEtale X} (e : (Aut W)ᵐᵒᵖ ≃* G)
    (H : Subgroup (Aut W)ᵐᵒᵖ) (n : ℕ) :
    Nat.Coprime (Nat.card (H.map e.toMonoidHom)) n ↔
      Nat.Coprime (Nat.card H) n := by
  rw [quotientDeckMulEquiv_map_natCard]

/-- The image of any source subgroup under an explicitly realized finite
quotient is exactly the image of its pointed-cover quotient subgroup under
the deck-group equivalence. -/
theorem quotientDeckMulEquiv_map_quotient_subgroup
    {G : Type v} [Group G]
    (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W)
    (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G)
    (phi : π₁ᵉᵗ(xi) →* G)
    (hcomp : e.toMonoidHom.comp
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w) = phi)
    (K : Subgroup π₁ᵉᵗ(xi)) :
    (K.map
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w)).map e.toMonoidHom = K.map phi := by
  rw [Subgroup.map_map, hcomp]

/-- Under an explicit finite-quotient realization, the image of every
source subgroup has the same cardinality in the prescribed target as in the
pointed deck quotient. -/
theorem quotientDeckMulEquiv_quotient_subgroup_natCard
    {G : Type v} [Group G]
    (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W)
    (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G)
    (phi : π₁ᵉᵗ(xi) →* G)
    (hcomp : e.toMonoidHom.comp
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w) = phi)
    (K : Subgroup π₁ᵉᵗ(xi)) :
    Nat.card (K.map phi) =
      Nat.card (K.map
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w)) := by
  rw [← quotientDeckMulEquiv_map_quotient_subgroup
    xi W hW w e phi hcomp K]
  exact quotientDeckMulEquiv_map_natCard e
    (K.map
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w))

/-- Hence coprimality of every source-subgroup image is equivalent in the
prescribed finite quotient and in its pointed deck-cover realization. -/
theorem quotientDeckMulEquiv_quotient_subgroup_coprime_iff
    {G : Type v} [Group G]
    (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W)
    (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G)
    (phi : π₁ᵉᵗ(xi) →* G)
    (hcomp : e.toMonoidHom.comp
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w) = phi)
    (K : Subgroup π₁ᵉᵗ(xi)) (n : ℕ) :
    Nat.Coprime (Nat.card (K.map phi)) n ↔
      Nat.Coprime
        (Nat.card (K.map
          (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
            xi W hW w))) n := by
  rw [quotientDeckMulEquiv_quotient_subgroup_natCard
    xi W hW w e phi hcomp K]

end AlgebraicGeometry.FiniteEtale

end
