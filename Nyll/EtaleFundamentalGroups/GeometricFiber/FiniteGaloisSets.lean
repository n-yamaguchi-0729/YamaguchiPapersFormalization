/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-!
# Finite Galois sets over a field

This file supplies the finite part of the equivalence in Stacks Project,
Tag `03QR`.  It directly transports the canonical Galois-category equivalence
along the canonical topological group isomorphism from the absolute Galois
group to the automorphism group of the geometric fiber functor.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]

/-- Finite étale `k`-schemes are canonically equivalent to finite continuous
sets with an action of the absolute Galois group of `k`.  This is the finite
part of Stacks Project, Tag `03QR`. -/
def equivContAction :
    FiniteEtale (Spec (.of k)) ≌ ContAction FintypeCat.{u} (K ≃ₐ[k] K) := by
  letI : IsSepClosed K := IsSepClosure.sep_closed k
  let F := fiber (Spec.map (CommRingCat.ofHom <| algebraMap k K))
  exact (PreGaloisCategory.functorToContAction F).asEquivalence.trans <|
    ContAction.resEquiv FintypeCat <|
      ContinuousMulEquiv.mk'
        (PreGaloisCategory.toAutHomeo F (K ≃ₐ[k] K))
        (fun g h ↦ by
          simpa only [PreGaloisCategory.toAutHomeo_apply] using
            (PreGaloisCategory.toAut F (K ≃ₐ[k] K)).map_mul g h)

end AlgebraicGeometry.FiniteEtale
