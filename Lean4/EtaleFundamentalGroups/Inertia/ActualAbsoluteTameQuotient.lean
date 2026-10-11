/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualAbsoluteTameCharacter
import EtaleFundamentalGroups.Inertia.ActualTameQuotientEquiv
import EtaleFundamentalGroups.Inertia.ActualTameRootsSeparableEquiv
import EtaleFundamentalGroups.Inertia.ActualTameRootsSeparableMap
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The SAME tame quotient is the full separable roots limit

Compose the existing continuous quotient equivalence with the actual
separable-roots equivalence. The representative law retains the original
quotient projection and the literal postcomposed character.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]

/-- The quotient's actual function, before joining its quotient topology. -/
def actualAbsoluteTameQuotient_apply
    (x : (actualTameQuotientGroup A K Ω Q).carrier) :
    (normalizationSeparableRootsGroup A Ω Q).carrier :=
  (actualTameRootsSeparableMap A K Ω Q).hom'.toFun
    ((actualTameQuotientMulEquiv A K Ω Q).toFun x)

/-- The actual function retains the SAME representative computation. -/
theorem actualAbsoluteTameQuotient_apply_projection
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    actualAbsoluteTameQuotient_apply A K Ω Q
        ((actualTameQuotientProjection A K Ω Q).hom'.toFun σ) =
      (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun σ :=
  congrArg (actualTameRootsSeparableMap A K Ω Q).hom'.toFun
    (actualTameQuotientMulEquiv_projection A K Ω Q σ)

/-- The original I/P with its quotient topology is the full separable roots limit. -/
def actualAbsoluteTameQuotientEquiv :
    (actualTameQuotientGroup A K Ω Q).carrier ≃ₜ*
      (normalizationSeparableRootsGroup A Ω Q).carrier :=
  (actualTameQuotientEquiv A K Ω Q).trans (actualTameRootsSeparableEquiv A K Ω Q)

/-- The continuous equivalence retains the previously computed actual function. -/
theorem actualAbsoluteTameQuotientEquiv_toFun :
    (actualAbsoluteTameQuotientEquiv A K Ω Q).toMulEquiv.toFun =
      actualAbsoluteTameQuotient_apply A K Ω Q := rfl

/-- A representative maps to the SAME canonical absolute tame character. -/
theorem actualAbsoluteTameQuotientEquiv_projection
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    (actualAbsoluteTameQuotientEquiv A K Ω Q).toMulEquiv.toFun
        ((actualTameQuotientProjection A K Ω Q).hom'.toFun σ) =
      (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun σ :=
  actualAbsoluteTameQuotient_apply_projection A K Ω Q σ

end EtaleFundamentalGroups.Inertia

end
