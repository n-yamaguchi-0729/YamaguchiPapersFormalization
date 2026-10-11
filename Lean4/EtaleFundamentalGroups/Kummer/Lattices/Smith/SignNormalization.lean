/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Lattices.Smith.LatticeCover

/-!
# Positive Smith coordinates for a finite-index lattice cover

The Smith coefficients produced for an integer lattice are nonzero integers.
Changing the sign of each negative target coordinate replaces them by their
positive natural absolute values.  Functoriality of additive monoid algebras
preserves the resulting coordinate square.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u v

/--
A finite-index sublattice admits Smith coordinates whose diagonal entries are
positive natural numbers.  The sign changes are produced from the Smith
coefficients themselves, the quotient is identified with the corresponding
product of cyclic groups, and the induced monoid-algebra square remains
commutative.  All three outputs use one canonical Smith choice.
-/
theorem exists_smithNatDiagonal_monoidAlgebra
    {R : Type u} {L : Type v} [CommSemiring R] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)] :
    ∃ (ι : Type v) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 0 < n i) ∧
        ∃ (eH : H ≃+ (ι → ℤ)) (eL : L ≃+ (ι → ℤ))
          (d : (ι → ℤ) →+ (ι → ℤ))
          (_eQ : (L ⧸ H) ≃+ ∀ i, ZMod (n i)),
          (∀ x i, d x i = (n i : ℤ) * x i) ∧
            (AddMonoidAlgebra.domCongr R R eL).toAlgHom.comp
                (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype.toAddMonoidHom) =
              (AddMonoidAlgebra.mapDomainAlgHom R R d).comp
                (AddMonoidAlgebra.domCongr R R eH).toAlgHom := by
  obtain ⟨ι, instι, a, ha, eH, eL, d, eQ, hd, hsquare⟩ :=
    exists_smithDiagonal_monoidAlgebra (R := R) H
  let : Fintype ι := instι
  let n : ι → ℕ := fun i ↦ Int.natAbs (a i)
  let sign : (i : ι) → ℤ ≃+ ℤ := fun i ↦
    if 0 ≤ a i then AddEquiv.refl ℤ else AddEquiv.neg ℤ
  let q : (ι → ℤ) ≃+ (ι → ℤ) := AddEquiv.piCongrRight sign
  let eL' : L ≃+ (ι → ℤ) := eL.trans q
  let d' : (ι → ℤ) →+ (ι → ℤ) :=
    q.toAddMonoidHom.comp d
  have hn : ∀ i, 0 < n i := by
    intro i
    exact Int.natAbs_pos.mpr (ha i)
  have hd' : ∀ x i, d' x i = (n i : ℤ) * x i := by
    intro x i
    rw [show d' x i = sign i (d x i) by rfl, hd]
    by_cases h : 0 ≤ a i
    · rw [show sign i = AddEquiv.refl ℤ by simp [sign, h]]
      have hnat : (n i : ℤ) = a i := by
        simpa [n] using Int.natAbs_of_nonneg h
      rw [hnat]
      rfl
    · have hai : a i ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [show sign i = AddEquiv.neg ℤ by simp [sign, h]]
      have hnat : (n i : ℤ) = -a i := by
        simp only [n]
        rw [Int.natCast_natAbs, abs_of_nonpos hai]
      rw [hnat, neg_mul]
      rfl
  have heLmap :
      AddMonoidAlgebra.mapDomainAlgHom R R eL'.toAddMonoidHom =
        (AddMonoidAlgebra.mapDomainAlgHom R R q.toAddMonoidHom).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R eL.toAddMonoidHom) := by
    rw [← AddMonoidAlgebra.mapDomainAlgHom_comp]
    rfl
  have hdmap :
      AddMonoidAlgebra.mapDomainAlgHom R R d' =
        (AddMonoidAlgebra.mapDomainAlgHom R R q.toAddMonoidHom).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R d) := by
    rw [← AddMonoidAlgebra.mapDomainAlgHom_comp]
  have hsquare' :
      (AddMonoidAlgebra.domCongr R R eL').toAlgHom.comp
          (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainAlgHom R R d').comp
          (AddMonoidAlgebra.domCongr R R eH).toAlgHom := by
    rw [AddMonoidAlgebra.domCongr_toAlgHom,
      AddMonoidAlgebra.domCongr_toAlgHom] at hsquare ⊢
    change
      (AddMonoidAlgebra.mapDomainAlgHom R R eL'.toAddMonoidHom).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainAlgHom R R d').comp
          (AddMonoidAlgebra.mapDomainAlgHom R R eH.toAddMonoidHom)
    change
      (AddMonoidAlgebra.mapDomainAlgHom R R eL.toAddMonoidHom).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainAlgHom R R d).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R eH.toAddMonoidHom) at hsquare
    rw [heLmap, hdmap, AlgHom.comp_assoc, AlgHom.comp_assoc]
    exact congrArg
      (fun g ↦
        (AddMonoidAlgebra.mapDomainAlgHom R R q.toAddMonoidHom).comp g) hsquare
  exact ⟨ι, inferInstance, n, hn, eH, eL', d', eQ, hd', hsquare'⟩

end EtaleFundamentalGroups.Kummer
