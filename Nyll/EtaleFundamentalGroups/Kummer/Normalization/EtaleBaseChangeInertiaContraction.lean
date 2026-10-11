/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.EtaleBaseChangeInertiaComparison

/-!
# Inertia at a contracted normalization prime

An etale base change supplies a canonical map between the two
normalizations.  Thus a prime in the selected base-changed normalization
has a canonical contraction in the original normalization.  This file
packages the corresponding inertia-cardinality comparison without asking
the caller to supply that contraction or its lying-over proof separately.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

/-- A prime in a selected etale base-change normalization and its canonical
contraction to the original normalization have inertia groups of the same
cardinality. -/
theorem normalizationInertia_natCard_eq_at_etaleBaseChange_contraction
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
    [P.LiesOver p]
    (Q : Ideal (integralClosure C M)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ p)] [CharZero (C ⧸ P)] :
    let q := Q.comap
      (integralClosureEtaleBaseChangeHom
        (A := A) (C := C) (L := L) (M := M))
    q.IsPrime ∧ q.LiesOver p ∧
      Nat.card (Q.toAddSubgroup.inertia Gal(M/KC)) =
        Nat.card (q.toAddSubgroup.inertia Gal(L/F)) := by
  let B := integralClosure A L
  let D := integralClosure C M
  let hBD := integralClosureEtaleBaseChangeHom
    (A := A) (C := C) (L := L) (M := M)
  let q : Ideal B := Q.comap hBD
  have hqPrime : q.IsPrime := Ideal.IsPrime.comap hBD
  let : q.IsPrime := hqPrime
  let : Algebra B D := integralClosureEtaleBaseChangeAlgebra
  let : IsScalarTower A B D := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    dsimp only [B, D]
    apply Subtype.ext
    rw [integralClosureEtaleBaseChangeAlgebra_algebraMap_coe]
    simp only [Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply A L M]
  have hQp : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  let : Q.LiesOver p := hQp
  have hqOver : q.LiesOver p := by
    change (Q.comap (algebraMap B D)).LiesOver p
    infer_instance
  let : q.LiesOver p := hqOver
  refine ⟨hqPrime, hqOver, ?_⟩
  exact normalizationInertia_natCard_eq_of_etaleBaseChangeProductMap_surjective
    hproduct p hpheight P hPheight q Q rfl

end EtaleFundamentalGroups

end
