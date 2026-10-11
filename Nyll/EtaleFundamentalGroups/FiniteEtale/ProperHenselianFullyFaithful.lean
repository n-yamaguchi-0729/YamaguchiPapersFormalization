/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.ProperHenselianSections
import Nyll.SchemeTheory.FiniteEtale.ProperClosedFiberFaithful
import Nyll.SchemeTheory.FiniteEtale.FullOfSectionDescent
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Full faithfulness over an arbitrary henselian local base

This proves the full-faithfulness part of the proper henselian-local comparison
without a Noetherian hypothesis. Essential surjectivity, and hence the full
equivalence in Stacks 0A48, is separate.

Fullness uses the existing finite étale internal Hom and henselian section
lift. Faithfulness is supplied by the arbitrary-local proper closed-fibre
comparison. The proper morphism is not assumed flat.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale

/-- Henselian lifting of sections of the actual finite étale internal Hom
makes the canonical closed-fibre pullback full over any henselian local ring. -/
theorem pullback_full_closedFiber_of_isProper_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).Full where
  map_surjective := (pullback_full_of_section_descent
    (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (fun W a ha =>
      exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing
        f W.hom a ha)).map_surjective

/-- The canonical finite étale pullback is fully faithful for a proper scheme
over any henselian local ring. Essential surjectivity is a separate assertion. -/
def pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).FullyFaithful := by
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  let hfull : (FiniteEtale.pullback i).Full :=
    pullback_full_closedFiber_of_isProper_of_henselianLocalRing f
  let hfaithful : (FiniteEtale.pullback i).Faithful :=
    pullback_faithful_closedFiber_of_isProper f
  exact Functor.FullyFaithful.ofFullyFaithful (FiniteEtale.pullback i)

end AlgebraicGeometry.FiniteEtale
