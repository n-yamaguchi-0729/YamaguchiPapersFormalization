/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Formally étale maps into adically complete rings

Formal smoothness lifts a map from the first infinitesimal quotient to an
adically complete target.  Adic separatedness and formal unramifiedness make
that lift unique.  Thus reduction modulo the ideal is bijective on maps from
a formally étale algebra.
-/

namespace Algebra.FormallyEtale

universe u v w

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S]

/-- Maps from a formally étale algebra to an adically complete algebra are
uniquely determined by, and uniquely lift from, their reduction modulo the
ideal of definition. -/
theorem comp_bijective_of_isAdicComplete [FormallyEtale R A]
    (I : Ideal S) [IsAdicComplete I S] :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R I).comp :
        (A →ₐ[R] S) → A →ₐ[R] S ⧸ I) := by
  constructor
  · intro f g hfg
    apply FormallyUnramified.ext_of_iInf (I := I) (g₁ := f) (g₂ := g)
    · simpa only [smul_eq_mul, Ideal.mul_top] using
        IsHausdorff.iInf_pow_smul
          (inferInstance : IsHausdorff I S)
    · intro a
      exact AlgHom.congr_fun hfg a
  · exact FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete

end Algebra.FormallyEtale
