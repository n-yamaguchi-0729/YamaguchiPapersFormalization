/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteCoverTrivialization
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
import Nyll.EtaleCohomology.Constructible.LocallyConstant
import Nyll.EtaleCohomology.Constructible.ModuleUnderlying
import Nyll.EtaleCohomology.Sites.ConnectedConstants
import Nyll.EtaleCohomology.Sites.ModuleConstant
import Nyll.EtaleCohomology.Sites.ModuleSetComparison
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite étale trivialization of module sheaves

On a connected scheme, a module sheaf with finite locally constant underlying
set sheaf is trivialized by a connected finite étale surjective cover. The
constant module is constructed from sections on that cover, and the actual
constant-sheaf counit supplies an isomorphism respecting addition and scalars.

In particular this applies to finite type locally constant sheaves over any
finite commutative coefficient ring. No base field or noetherian hypothesis
is used. Finiteness of the ring is only needed for this last specialization.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- A finite locally constant underlying set sheaf has a finite étale
trivialization as a module sheaf, even over an infinite coefficient ring. -/
theorem exists_finite_etale_module_trivialization_of_underlying
    {X : Scheme.{u}} [ConnectedSpace X] {R : Type u} [CommRing R]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (hG : IsEtaleFiniteLocallyConstantSet ((etaleModuleUnderlying X R).obj G)) :
    ∃ A : FiniteEtale X, ConnectedSpace A.left ∧ Surjective A.hom ∧
      ∃ M : ModuleCat.{u} R, Finite M ∧ Module.Finite R M ∧
        Nonempty ((etalePullback A.hom R).obj G ≅
          (constantSheaf A.left.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
  obtain ⟨A, hA, hsurj, ι, hι, ⟨e⟩⟩ := hG.exists_finite_etale_trivialization
  have : ConnectedSpace A.left := hA
  have : Finite ι := hι
  let ff : (constantSheaf A.left.smallEtaleTopology (Type u)).FullyFaithful :=
    etaleConstantSheafFullyFaithful A.left
  have := ff.faithful
  have := ff.full
  let eG : (etaleModuleUnderlying A.left R).obj ((etalePullback A.hom R).obj G) ≅
      (constantSheaf A.left.smallEtaleTopology (Type u)).obj ι :=
    (etalePullbackModuleUnderlyingIso A.hom R).app G ≪≫ e
  obtain ⟨M, hM, hfin, eM⟩ := exists_finite_constantModule_of_underlying_iso
    (X := A.left) ((etalePullback A.hom R).obj G) ι eG
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) A.left)
  exact ⟨A, hA, hsurj, M, hM, hfin, eM⟩

/-- Over a finite coefficient ring, any finite type locally constant module
sheaf on a connected scheme becomes constant on a connected finite étale
surjective cover. -/
theorem IsEtaleFiniteTypeLocallyConstant.exists_finite_etale_trivialization
    {X : Scheme.{u}} [ConnectedSpace X] {R : Type u} [CommRing R] [Finite R]
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleFiniteTypeLocallyConstant R G) :
    ∃ A : FiniteEtale X, ConnectedSpace A.left ∧ Surjective A.hom ∧
      ∃ M : ModuleCat.{u} R, Finite M ∧ Module.Finite R M ∧
        Nonempty ((etalePullback A.hom R).obj G ≅
          (constantSheaf A.left.smallEtaleTopology (ModuleCat.{u} R)).obj M) :=
  exists_finite_etale_module_trivialization_of_underlying G
    hG.isEtaleFiniteLocallyConstantSet

end EtaleCohomology
