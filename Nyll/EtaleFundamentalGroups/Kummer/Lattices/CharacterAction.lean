/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Duality
import Nyll.EtaleFundamentalGroups.Kummer.Lattices.Cover

/-!
# Character action on a finite-index lattice cover

Characters of the finite quotient lattice act diagonally on the ambient
lattice algebra.  When the coefficient domain has enough roots of unity,
these characters separate the quotient degrees.  Consequently their common
fixed subalgebra is exactly the image of the subgroup lattice algebra.
-/

namespace EtaleFundamentalGroups.Kummer

universe u v

noncomputable section

private def latticeCharacterWeight
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    Multiplicative L →* k :=
  (Units.coeHom k).comp
    (χ.comp (QuotientAddGroup.mk' H).toMultiplicative)

private def latticeCharacterMonomial
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    Multiplicative L →* AddMonoidAlgebra k L :=
  (AddMonoidAlgebra.singleHom :
      k × Multiplicative L →* AddMonoidAlgebra k L).comp
    ((latticeCharacterWeight H χ).prod
      (MonoidHom.id (Multiplicative L)))

private def latticeCharacterAlgHom
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    AddMonoidAlgebra k L →ₐ[k] AddMonoidAlgebra k L :=
  AddMonoidAlgebra.lift k (AddMonoidAlgebra k L) L
    (latticeCharacterMonomial H χ)

@[simp]
private theorem latticeCharacterAlgHom_single
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ)
    (l : L) (a : k) :
    latticeCharacterAlgHom H χ (AddMonoidAlgebra.single l a) =
      AddMonoidAlgebra.single l
        (a * (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)) := by
  simp [latticeCharacterAlgHom, latticeCharacterMonomial,
    latticeCharacterWeight, Algebra.smul_def]

private def latticeCharacterAlgEquiv
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    AddMonoidAlgebra k L ≃ₐ[k] AddMonoidAlgebra k L :=
  AlgEquiv.ofAlgHom
    (latticeCharacterAlgHom H χ)
    (latticeCharacterAlgHom H χ⁻¹)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro l
        simp [latticeCharacterAlgHom_single]
      · ext)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro l
        simp [latticeCharacterAlgHom_single]
      · ext)

/-- The canonical diagonal action of quotient-lattice characters on the
ambient lattice algebra. -/
def latticeCharacterAction
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) :
    (Multiplicative (L ⧸ H) →* kˣ) →*
      (AddMonoidAlgebra k L ≃ₐ[k] AddMonoidAlgebra k L) where
  toFun := latticeCharacterAlgEquiv H
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AddMonoidAlgebra.algHom_ext
    · intro l
      simp [latticeCharacterAlgEquiv, latticeCharacterAlgHom_single]
    · ext
  map_mul' χ ψ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AddMonoidAlgebra.algHom_ext
    · intro l
      simp [latticeCharacterAlgEquiv, latticeCharacterAlgHom_single,
        AlgEquiv.mul_apply, mul_comm]
    · ext

@[simp]
theorem latticeCharacterAction_single
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ)
    (l : L) (a : k) :
    latticeCharacterAction H χ (AddMonoidAlgebra.single l a) =
      AddMonoidAlgebra.single l
        (a * (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)) := by
  exact latticeCharacterAlgHom_single H χ l a

theorem latticeCharacterAction_coeff
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ)
    (x : AddMonoidAlgebra k L) (l : L) :
    (latticeCharacterAction H χ x).coeff l =
      x.coeff l * (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k) := by
  induction x using AddMonoidAlgebra.induction_on with
  | of m =>
      by_cases h : m = l
      · subst m
        simp [AddMonoidAlgebra.of]
      · simp [AddMonoidAlgebra.of, h]
  | add x y hx hy =>
      rw [map_add]
      change
        (latticeCharacterAction H χ x).coeff l +
            (latticeCharacterAction H χ y).coeff l =
          (x.coeff l + y.coeff l) *
            (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)
      rw [hx, hy]
      ring
  | smul a x hx =>
      rw [map_smul]
      change
        a * (latticeCharacterAction H χ x).coeff l =
          (a * x.coeff l) *
            (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)
      rw [hx]
      ring

/-- The elements fixed by every quotient character are exactly the
degree-zero part for the quotient grading. -/
theorem fixedBy_latticeCharacterAction_eq_gradeZero
    {k : Type u} {L : Type v} [CommRing k] [IsDomain k]
    [AddCommGroup L]
    (H : AddSubgroup L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    {x : AddMonoidAlgebra k L |
        ∀ χ : Multiplicative (L ⧸ H) →* kˣ,
          latticeCharacterAction H χ x = x} =
      (SetLike.GradeZero.subalgebra
        (AddMonoidAlgebra.gradeBy k (QuotientAddGroup.mk' H)) :
        Set (AddMonoidAlgebra k L)) := by
  ext x
  constructor
  · intro hx
    change x ∈ AddMonoidAlgebra.gradeBy k (QuotientAddGroup.mk' H) 0
    intro l hl
    by_contra hq
    have hqMul :
        Multiplicative.ofAdd (QuotientAddGroup.mk' H l) ≠ 1 := by
      intro h
      apply hq
      exact congrArg Multiplicative.toAdd h
    obtain ⟨χ, hχ⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
        (Multiplicative (L ⧸ H)) k hqMul
    have hfix := congrArg
      (fun y : AddMonoidAlgebra k L => y.coeff l) (hx χ)
    rw [latticeCharacterAction_coeff] at hfix
    have hcoeff : x.coeff l ≠ 0 := Finsupp.mem_support_iff.mp hl
    have hχCoe :
        (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k) = 1 :=
      (mul_eq_left₀ hcoeff).mp hfix
    apply hχ
    exact Units.ext hχCoe
  · intro hx χ
    ext l
    rw [latticeCharacterAction_coeff]
    by_cases hcoeff : x.coeff l = 0
    · simp [hcoeff]
    · have hl : l ∈ x.coeff.support := Finsupp.mem_support_iff.mpr hcoeff
      have hdegree : QuotientAddGroup.mk' H l = 0 := hx l hl
      rw [hdegree]
      simp

/-- The common fixed subalgebra of quotient characters is the image of the
subgroup lattice algebra. -/
theorem fixedBy_latticeCharacterAction_eq_range
    {k : Type u} {L : Type v} [CommRing k] [IsDomain k]
    [AddCommGroup L]
    (H : AddSubgroup L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    {x : AddMonoidAlgebra k L |
        ∀ χ : Multiplicative (L ⧸ H) →* kˣ,
          latticeCharacterAction H χ x = x} =
      ((AddMonoidAlgebra.mapDomainAlgHom k k H.subtype).range :
        Set (AddMonoidAlgebra k L)) := by
  rw [fixedBy_latticeCharacterAction_eq_gradeZero,
    range_mapDomainAlgHom_eq_gradeZero_quotient]

end

end EtaleFundamentalGroups.Kummer
