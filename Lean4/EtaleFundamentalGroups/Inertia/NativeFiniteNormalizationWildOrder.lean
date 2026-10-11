/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import EtaleFundamentalGroups.Inertia.FiniteIdealWildPrimary
import EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Wild order from a native finite field normalization

Only the original finite separable field supplies normalization finiteness
and torsion freeness. The field environment is closed before the prime and
its residue field enter the principal-unit order proof.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Native finite separable normalization has residue-primary wild order. -/
theorem nativeFiniteNormalizationWildOrder_exists_expChar_pow
    (A : Type u) [rA : CommRing A] [dedA : IsDedekindDomain A]
    (K : Type v) [fK : Field K] [aAK : Algebra A K] [frAK : IsFractionRing A K]
    (C : CommAlgCat.{w} A) (hC : IsField C.carrier)
    [aKC : Algebra K C.carrier] [tAKC : IsScalarTower A K C.carrier]
    [fKC : FiniteDimensional K C.carrier] [sKC : Algebra.IsSeparable K C.carrier] :
    let : Field C.carrier := hC.toField
    let : IsDedekindDomain (normalizationCommAlgCat A C.carrier).carrier :=
      integralClosure.isDedekindDomain A K C.carrier
    ∀ (Q : Ideal (normalizationCommAlgCat A C.carrier).carrier) [Q.IsPrime] (hQ : Q ≠ ⊥),
      ∃ n : ℕ, commAlgIdealWildOrder A (normalizationCommAlgCat A C.carrier) Q hQ =
        (ringExpChar Q.ResidueField) ^ n := by
  intro fC dB
  let B : CommAlgCat.{w} A := normalizationCommAlgCat A C.carrier
  change IsDedekindDomain B.carrier at dB
  have tfAB : Module.IsTorsionFree A B.carrier :=
    nativeFieldNormalization_isTorsionFree A K C.carrier
  have finAB : Module.Finite A B.carrier := nativeNormalization_finite A K C hC
  change ∀ (Q : Ideal B.carrier) [Q.IsPrime] (hQ : Q ≠ ⊥),
    ∃ n : ℕ, commAlgIdealWildOrder A B Q hQ = (ringExpChar Q.ResidueField) ^ n
  clear_value dB
  clear_value B
  clear sKC fKC tAKC aKC fC hC C frAK aAK fK K
  intro Q qPrime hQ
  exact finiteIdealWildOrder_exists_expChar_pow A B.carrier Q hQ

end EtaleFundamentalGroups.Inertia

end
