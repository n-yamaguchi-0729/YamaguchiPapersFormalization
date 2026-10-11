/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.IteratedRadical.CompletionBaseChange

/-!
# The chosen closed factor after completing an iterated radical

A uniquely chosen closed prime in a finite algebra remains unique after
base change to the maximal-adic completion.  The completed chosen prime is the
exact extension of the original one.  Its maximality is supplied by the
closed-fibre completion theorem; uniqueness follows by contracting any other
closed prime to the original finite algebra and using faithful flatness of the
completion map.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped TensorProduct

universe u

/-- The exact extension of a unique closed prime in a finite algebra remains
the unique closed prime after completing an iterated positive root cover. -/
theorem unique_closedPrime_iteratedRadicalCompletion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let haHat : ∀ i, algebraMap A Ahat (a i) ∈
        IsLocalRing.maximalIdeal Ahat := fun i ↦ by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical n _ hn haHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    ∀ {E : Type u} [CommRing E] [Algebra B E]
      [Module.Finite B E],
      ∀ (q : Ideal E) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        (∀ Q : Ideal E, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q) →
        let Ehat := Bhat ⊗[B] E
        letI : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
        letI : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
        let qhat := q.map (algebraMap E Ehat)
        ∀ Qhat : Ideal Ehat, Qhat.IsPrime →
          Qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) → Qhat = qhat := by
  dsimp only
  intro E _ _ _ q _ _ hunique
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  have haHat : ∀ i, algebraMap A Ahat (a i) ∈
      IsLocalRing.maximalIdeal Ahat := fun i ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical n _ hn haHat
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let : Module.FaithfullyFlat B Bhat :=
    faithfullyFlat_iteratedRadicalCompletion n a
  let Ehat := Bhat ⊗[B] E
  let : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
  let qhat := q.map (algebraMap E Ehat)
  let : Algebra.IsIntegral B E := Algebra.IsIntegral.of_finite B E
  have hqMax : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap B E)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) q <| by
        rw [← Ideal.under_def, ← q.over_def (IsLocalRing.maximalIdeal B)]
        exact IsLocalRing.maximalIdeal.isMaximal B
  let : q.IsMaximal := hqMax
  have hqhatMax : qhat.IsMaximal :=
    tensorProduct_map_isMaximal_of_residueFieldMap_bijective
      (R := B) (R' := Bhat) (S := E) q
      (maximalIdeal_map_iteratedRadicalCompletion n a hn ha)
      (residueFieldMap_bijective_iteratedRadicalCompletion n a hn ha)
  intro Qhat hQhatPrime hQhatOver
  let : Qhat.IsPrime := hQhatPrime
  let : Qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) := hQhatOver
  let Q := Qhat.comap (algebraMap E Ehat)
  have hQPrime : Q.IsPrime := Ideal.IsPrime.comap (algebraMap E Ehat)
  have hQhatComap :
      Qhat.comap (algebraMap Bhat Ehat) =
        IsLocalRing.maximalIdeal Bhat := by
    simpa only [Ideal.under_def] using hQhatOver.over.symm
  have hQOver : Q.LiesOver (IsLocalRing.maximalIdeal B) := by
    apply Ideal.LiesOver.mk
    symm
    change (Qhat.comap (algebraMap E Ehat)).comap (algebraMap B E) =
        IsLocalRing.maximalIdeal B
    rw [Ideal.comap_comap]
    rw [← IsScalarTower.algebraMap_eq B E Ehat]
    rw [IsScalarTower.algebraMap_eq B Bhat Ehat]
    rw [← Ideal.comap_comap]
    rw [hQhatComap]
    rw [← maximalIdeal_map_iteratedRadicalCompletion n a hn ha]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat
      (A := B) (B := Bhat) (IsLocalRing.maximalIdeal B)
  have hQeq : Q = q := hunique Q hQPrime hQOver
  have hqhat_le : qhat ≤ Qhat := by
    rw [Ideal.map_le_iff_le_comap]
    change q ≤ Q
    exact hQeq.symm.le
  exact (hqhatMax.eq_of_le hQhatPrime.ne_top hqhat_le).symm

end EtaleFundamentalGroups.Kummer

end
