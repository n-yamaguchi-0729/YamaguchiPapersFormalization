/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomology

/-!
# Radical invariance of derived local cohomology

The diagram of powers of an ideal is initial in the diagram of all ideals
whose radical contains it.  Applying the same cofinality argument as for
Mathlib's legacy local cohomology shows that the derived-Ext colimit depends
only on the radical of its support ideal.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u v v'

/-- Precomposing an ideal diagram gives the corresponding precomposition of
the contravariant derived-Ext diagrams. -/
def derivedLocalCohomologyDiagramComp
    {R : Type max u v v'} [CommRing R]
    {D : Type v} [SmallCategory D]
    {E : Type v'} [SmallCategory E]
    (F : E ⥤ D) (I : D ⥤ Ideal R)
    (M : ModuleCat.{max u v v'} R) (i : ℕ) :
    derivedLocalCohomologyDiagram (F ⋙ I) M i ≅
      F.op ⋙ derivedLocalCohomologyDiagram I M i :=
  Iso.refl _

/-- Derived local cohomology is unchanged after precomposition by an initial
functor (equivalently, after precomposition of the opposite diagram by a
final functor). -/
def derivedLocalCohomologyIsoOfInitial
    {R : Type max u v v'} [CommRing R]
    {D : Type v} [SmallCategory D]
    {E : Type v'} [SmallCategory E]
    (F : E ⥤ D) [Functor.Initial F] (I : D ⥤ Ideal R)
    (M : ModuleCat.{max u v v'} R) (i : ℕ) :
    derivedLocalCohomologyOfDiagram.{max u v, v'} (F ⋙ I) M i ≅
      derivedLocalCohomologyOfDiagram.{max u v', v} I M i :=
  HasColimit.isoOfNatIso
      (derivedLocalCohomologyDiagramComp.{u, v, v'} F I M i) ≪≫
    Functor.Final.colimitIso F.op
      (derivedLocalCohomologyDiagram I M i)

section Noetherian

variable {R : Type u} [CommRing R] [IsNoetherian R R]

/-- The derived Ext colimit over all ideals whose radical contains `I`. -/
def derivedLocalCohomologyOfSelfLERadical
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) : AddCommGrpCat.{u} :=
  derivedLocalCohomologyOfDiagram
    (localCohomology.selfLERadicalDiagram I) M i

/-- The all-supports and powers models of derived local cohomology agree. -/
def derivedLocalCohomologyIsoSelfLERadical
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    derivedLocalCohomologyOfSelfLERadical I M i ≅
      derivedLocalCohomology I M i :=
  (derivedLocalCohomologyIsoOfInitial
      (localCohomology.idealPowersToSelfLERadical I)
      (localCohomology.selfLERadicalDiagram I) M i).symm ≪≫
    HasColimit.isoOfNatIso (Iso.refl _)

/-- The all-supports derived Ext colimits agree for ideals with the same
radical. -/
def derivedLocalCohomologyOfSelfLERadicalIsoOfSameRadical
    {I J : Ideal R} (hIJ : I.radical = J.radical)
    (M : ModuleCat.{u} R) (i : ℕ) :
    derivedLocalCohomologyOfSelfLERadical I M i ≅
      derivedLocalCohomologyOfSelfLERadical J M i :=
  (derivedLocalCohomologyIsoOfInitial
      (localCohomology.SelfLERadical.cast hIJ.symm)
      (localCohomology.selfLERadicalDiagram I) M i).symm

/-- The derived local-cohomology object depends only on the radical of its
support ideal. -/
def derivedLocalCohomologyIsoOfSameRadical
    {I J : Ideal R} (hIJ : I.radical = J.radical)
    (M : ModuleCat.{u} R) (i : ℕ) :
    derivedLocalCohomology I M i ≅ derivedLocalCohomology J M i :=
  (derivedLocalCohomologyIsoSelfLERadical I M i).symm ≪≫
    derivedLocalCohomologyOfSelfLERadicalIsoOfSameRadical hIJ M i ≪≫
    derivedLocalCohomologyIsoSelfLERadical J M i

end Noetherian

end EtaleFundamentalGroups

end
