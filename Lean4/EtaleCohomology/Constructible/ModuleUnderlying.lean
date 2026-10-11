/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.FiniteLocallyConstantSet
import EtaleCohomology.Constructible.LocallyConstant
import EtaleCohomology.Sites.ModuleSetComparison
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Underlying finite locally constant sheaves

Over a finite coefficient ring, the underlying set sheaf of a finite type
locally constant module sheaf is finite locally constant. The original
trivializing étale cover works: inverse image commutes with forgetting the
module structure, and each finitely generated module over a finite ring is
a finite set. The base scheme is arbitrary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology

/-- Finite type local constancy over a finite ring gives finite local constancy
of the underlying set sheaf, on the same étale cover. -/
lemma IsEtaleFiniteTypeLocallyConstant.isEtaleFiniteLocallyConstantSet
    {X : Scheme.{u}} {R : Type u} [CommRing R] [Finite R]
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleFiniteTypeLocallyConstant R G) :
    IsEtaleFiniteLocallyConstantSet ((etaleModuleUnderlying X R).obj G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰, fun a => ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒰 a
  have : Module.Finite R M := hM
  exact ⟨M, Module.finite_of_finite R,
    ⟨((etalePullbackModuleUnderlyingIso (𝒰.f a) R).app G).symm ≪≫
      (etaleModuleUnderlying (𝒰.X a) R).mapIso eM ≪≫
      (etaleConstantModuleUnderlyingIso (𝒰.X a) R).app M⟩⟩

end EtaleCohomology
