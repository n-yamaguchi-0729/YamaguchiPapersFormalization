/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Trivial inertia gives unramifiedness in every characteristic

The fundamental degree identity and orbit-stabilizer count show that trivial
inertia forces both ramification index one and separability of the residue
extension. No perfectness hypothesis on the residue field is needed.
-/

noncomputable section

open Algebra
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
  (G : Type w) [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

/-- A trivial inertia group forces a separable residue extension and
ramification index one, without a residue-characteristic assumption. -/
theorem residue_isGalois_and_ramificationIdx_eq_one_of_inertia_eq_bot
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hI : q.inertia G = ⊥) :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    IsGalois p.ResidueField q.ResidueField ∧ q.ramificationIdx R = 1 := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  have heq : (algebraMap (S ⧸ q) q.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ q)) =
      (algebraMap p.ResidueField q.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext x
    simp only [RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply]
  let : Algebra (R ⧸ p) q.ResidueField :=
    ((algebraMap (S ⧸ q) q.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ q))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField q.ResidueField := .of_algebraMap_eq' heq
  let rho := IsFractionRing.stabilizerHom G p q p.ResidueField q.ResidueField
  have hrho : Function.Bijective rho := by
    refine ⟨(MonoidHom.ker_eq_bot_iff rho).mp ?_,
      IsFractionRing.stabilizerHom_surjective G p q p.ResidueField q.ResidueField⟩
    rw [IsFractionRing.ker_stabilizerHom]
    change (q.inertia G).subgroupOf (MulAction.stabilizer G q) = ⊥
    rw [hI]
    exact Subgroup.bot_subgroupOf _
  have hc : Nat.card (MulAction.stabilizer G q) =
      Nat.card Gal(q.ResidueField/p.ResidueField) :=
    Nat.card_congr (Equiv.ofBijective rho hrho)
  have horbit : (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G q) = Nat.card G := by
    rw [← IsInvariant.orbit_eq_primesOver R S G p q]
    exact (Nat.card_prod _ _).symm.trans
      (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G q))
  have hcount := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p q G,
    Ideal.inertiaDegIn_eq_inertiaDeg p q G] at hcount
  have hpos : 0 < (p.primesOver S).ncard := by
    exact (Set.ncard_pos (Algebra.QuasiFinite.finite_primesOver p)).mpr
      ⟨q, inferInstance, inferInstance⟩
  have hd : q.ramificationIdx R * q.inertiaDeg R =
      Nat.card Gal(q.ResidueField/p.ResidueField) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    exact hcount.trans (horbit.symm.trans (congrArg ((p.primesOver S).ncard * ·) hc))
  have hfpos : 0 < Module.finrank p.ResidueField q.ResidueField := by
    rw [← Ideal.inertiaDeg_eq p q]
    exact q.inertiaDeg_pos R
  have : Module.Finite p.ResidueField q.ResidueField := Module.finite_of_finrank_pos hfpos
  have hbound : Nat.card Gal(q.ResidueField/p.ResidueField) ≤
      Module.finrank p.ResidueField q.ResidueField :=
    (Nat.card_le_card_of_injective AlgEquiv.toAlgHom AlgEquiv.coe_toAlgHom_injective).trans
      (card_algHom_le_finrank p.ResidueField q.ResidueField q.ResidueField)
  rw [Ideal.inertiaDeg_eq p q] at hd
  have hepos : 0 < q.ramificationIdx R := q.ramificationIdx_pos R
  have he : q.ramificationIdx R = 1 := by
    have hle : q.ramificationIdx R * Module.finrank p.ResidueField q.ResidueField ≤
        1 * Module.finrank p.ResidueField q.ResidueField := by
      rw [hd, one_mul]
      exact hbound
    have h := Nat.le_of_mul_le_mul_right hle hfpos
    omega
  refine ⟨IsGalois.of_card_aut_eq_finrank _ _ ?_, he⟩
  rw [he, one_mul] at hd
  exact hd.symm

/-- A finite flat Galois algebra is unramified over a base prime if every
inertia group over that prime is trivial. Residue separability is derived. -/
theorem isUnramifiedAt_of_inertia_eq_bot
    (p : Ideal R) [p.IsPrime]
    (hI : ∀ (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p], Q.inertia G = ⊥)
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] : Algebra.IsUnramifiedAt R q := by
  have hsep : Algebra.HasSeparableResidueFieldsAt R S p := by
    constructor
    intro Q hQ hQp
    let := Localization.AtPrime.algebraOfLiesOver p Q
    have : IsGalois p.ResidueField Q.ResidueField :=
      (residue_isGalois_and_ramificationIdx_eq_one_of_inertia_eq_bot G p Q (hI Q)).1
    infer_instance
  have : Algebra.HasSeparableResidueFieldsAt R S (q.under R) := by
    simpa only [q.over_def p] using hsep
  exact (Ideal.ramificationIdx_eq_one_iff (q := q) (R := R)).mp
    (residue_isGalois_and_ramificationIdx_eq_one_of_inertia_eq_bot G p q (hI q)).2

end EtaleFundamentalGroups.Inertia
