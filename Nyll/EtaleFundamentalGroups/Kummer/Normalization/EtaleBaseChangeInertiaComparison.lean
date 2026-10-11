/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.EtaleBaseChangeInertiaCardinality

/-!
# Inertia cardinality across an etale function-field base change

This file combines the selected-component normalization theorem with the
ramification-index square and the normal-Noetherian inertia-cardinality
formula.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

/-- Inertia at compatible normalization primes has the same cardinality
after an etale function-field base change whose canonical product map selects
the target field. -/
theorem normalizationInertia_natCard_eq_of_etaleBaseChangeProductMap_surjective
    {A C F KC L M : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    [CommRing C] [IsDomain C] [IsNoetherianRing C]
    [IsIntegrallyClosed C] [Algebra A C] [Algebra.Etale A C]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field KC] [Algebra C KC] [IsFractionRing C KC]
    [Algebra A KC] [IsScalarTower A C KC]
    [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    [FiniteDimensional F L] [IsGalois F L]
    [Field M] [Algebra KC M] [Algebra C M] [IsScalarTower C KC M]
    [FiniteDimensional KC M] [IsGalois KC M]
    [Algebra L M] [Algebra A M] [IsScalarTower A L M]
    [IsScalarTower A C M]
    (hproduct : Function.Surjective
      (etaleBaseChangeProductMap (A := A) (C := C) (L := L) (M := M)))
    (p : Ideal A) [p.IsPrime] (hpheight : p.height = 1)
    (P : Ideal C) [P.IsPrime] (hPheight : P.height = 1)
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (integralClosure C M)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ p)] [CharZero (C ⧸ P)]
    (hQq : q = Q.comap
      (integralClosureEtaleBaseChangeHom
        (A := A) (C := C) (L := L) (M := M))) :
    Nat.card (Q.toAddSubgroup.inertia Gal(M/KC)) =
      Nat.card (q.toAddSubgroup.inertia Gal(L/F)) := by
  let B := integralClosure A L
  let D := integralClosure C M
  let : Algebra B D := integralClosureEtaleBaseChangeAlgebra
  let : Q.LiesOver q := ⟨by
    change q = Q.comap
      (integralClosureEtaleBaseChangeHom
        (A := A) (C := C) (L := L) (M := M))
    exact hQq⟩
  let : IsScalarTower A B D := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    dsimp only [B, D]
    apply Subtype.ext
    rw [integralClosureEtaleBaseChangeAlgebra_algebraMap_coe]
    simp only [Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply A L M]
  let : Algebra.Etale B D :=
    integralClosure_etale_of_etaleBaseChangeProductMap_surjective hproduct
  have hQcard :
      Nat.card (Q.toAddSubgroup.inertia Gal(M/KC)) =
        Q.ramificationIdx C :=
    normalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
      (K := KC) (L := M) P hPheight Q
  have hqcard :
      Nat.card (q.toAddSubgroup.inertia Gal(L/F)) =
        q.ramificationIdx A :=
    normalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
      (K := F) (L := L) p hpheight q
  exact hQcard.trans
    ((ramificationIdx_eq_of_etale_square q Q).trans hqcard.symm)

end EtaleFundamentalGroups
