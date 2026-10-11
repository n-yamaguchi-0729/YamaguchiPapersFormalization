/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExact
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticMap
import Nyll.EtaleFundamentalGroups.GeometricFiber.SeparableInjectivity

/-!
# Arithmetic Exact Sequence

The arithmetic short exact sequence over a separable closure. Both maps
are the actual continuous maps on geometric fiber automorphism groups.
-/

noncomputable section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.FiniteEtale

/-- The arithmetic short exact sequence over a separable closure. Both maps
are the actual continuous maps on geometric fiber automorphism groups. -/
theorem arithmetic_exactSequence_of_isSepClosure
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    let geometric := fundamentalGroupHom (Limits.pullback.snd _ f) xi
    let arithmetic := arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f)
    Function.Injective geometric ∧ Function.Surjective arithmetic ∧
      arithmetic.toMonoidHom.ker = geometric.toMonoidHom.range := by
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  refine ⟨fundamentalGroupHom_injective_of_separable_constant_extension k L X f xi,
    arithmeticFundamentalGroupHom_surjective_of_connected_constantField k L L f
      (xi ≫ Limits.pullback.snd _ f), ?_⟩
  exact (arithmeticFundamentalGroupHom_ker k L f (xi ≫ Limits.pullback.snd _ f)).trans
    (fundamentalGroupHom_constantField_ker_eq_range k L f xi)

end AlgebraicGeometry.FiniteEtale
