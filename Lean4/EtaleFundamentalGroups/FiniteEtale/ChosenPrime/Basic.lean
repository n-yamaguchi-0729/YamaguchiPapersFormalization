/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Ideal.GoingDown
import SchemeTheory.RingTheory.Ramification.Etale.BaseChange

/-!
# A chosen prime below the étale factor of Tag 00UJ

Tag 00UJ chooses an étale base change and a prime in one finite idempotent factor above a
specified prime `q`.  For the one-point inertia argument we also have a smaller, height-one prime
`r ≤ q`.  Flat going down produces a prime below the chosen Tag 00UJ prime and the étale
ramification-index comparison identifies its ramification index with that of `r`.

The right tensor-factor algebra and its flatness are proof-local.  In particular this module does
not register a second global algebra structure on a tensor product.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v

/-- Tag 00UJ may be chosen together with a prime above every specified smaller prime, without
changing its ramification index.

The data before `Q` are the finite chosen factor supplied by Tag 00UJ.  The additional prime `Q`
is obtained by going down from `P'` along the right tensor-factor map.  Its explicit contraction
equality is the input expected by `ramificationIdx_tensorProduct_eq_of_etale`.
-/
theorem exists_etale_factor_prime_le_ramificationIdx_eq
    {R : Type u} {B : Type v}
    [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime]
    (q : Ideal B) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    (r : Ideal B) [r.IsPrime] (hrq : r ≤ q) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (P : Ideal C) (_ : P.IsPrime) (_ : P.LiesOver p)
      (e : TensorProduct R C B) (_ : IsIdempotentElem e)
      (P' Q : Ideal (TensorProduct R C B))
      (_ : P'.IsPrime) (_ : P'.LiesOver P) (_ : Q.IsPrime),
        P'.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧
        Q ≤ P' ∧
        Q.comap Algebra.TensorProduct.includeRight.toRingHom = r ∧
        Q.ramificationIdx C = r.ramificationIdx R ∧
        e ∉ Q ∧
        e ∉ P' ∧
        Function.Bijective
          (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
        Module.Finite C (Localization.Away e) ∧
        ∀ P'' : Ideal (TensorProduct R C B),
          P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P' := by
  obtain ⟨C, _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hres, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let T := TensorProduct R C B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R B T := Algebra.TensorProduct.right_isScalarTower
  let commB : AlgEquiv B (TensorProduct R B C) T :=
    { toRingEquiv := (Algebra.TensorProduct.comm R B C).toRingEquiv
      commutes' := by
        intro b
        exact (Algebra.TensorProduct.right_algebraMap_apply b).symm }
  let : Algebra.Etale B T := Algebra.Etale.of_equiv commB
  have hP'_over_q : P'.LiesOver q :=
    { over := by
        simpa [Ideal.under_def,
          Algebra.TensorProduct.algebraMap_eq_includeRight] using hP'q.symm }
  let : P'.LiesOver q := hP'_over_q
  obtain ⟨Q, hQP', hQprime, hQover⟩ :=
    P'.exists_ideal_le_liesOver_of_le (p := r) (q := q) hrq
  let : Q.IsPrime := hQprime
  have hQr : Q.comap Algebra.TensorProduct.includeRight.toRingHom = r := by
    simpa [Ideal.under_def,
      Algebra.TensorProduct.algebraMap_eq_includeRight] using hQover.over.symm
  have hram : Q.ramificationIdx C = r.ramificationIdx R :=
    ramificationIdx_tensorProduct_eq_of_etale r Q hQr
  have heQ : e ∉ Q := fun he ↦ heP' (hQP' he)
  exact ⟨C, inferInstance, inferInstance, inferInstance,
    P, inferInstance, inferInstance, e, he, P', Q,
    inferInstance, inferInstance, inferInstance,
    hP'q, hQP', hQr, hram, heQ, heP', hres, hfinite, hunique⟩

end EtaleFundamentalGroups

end
