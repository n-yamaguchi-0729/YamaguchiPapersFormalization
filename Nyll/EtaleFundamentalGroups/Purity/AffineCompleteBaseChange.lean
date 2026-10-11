/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.FiniteEtaleCompleteBaseChange
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence

/-!
# Finite étale covers under complete affine base change

Quotient base change for finite étale algebras over a complete Noetherian local ring is
transported across the affine finite étale equivalence.  This gives the corresponding
equivalence for finite étale covers of affine schemes.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- Pullback along `Spec (R ⧸ I) ⟶ Spec R` is an equivalence on finite étale covers when
`R` is a complete Noetherian local ring and `I` is contained in its maximal ideal. -/
theorem finiteEtale_pullback_isEquivalence_of_complete_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    (AlgebraicGeometry.FiniteEtale.pullback
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk I)))).IsEquivalence := by
  let F := AlgebraicGeometry.FiniteEtale.pullback
    (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let B := CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)
  let E := AlgebraicGeometry.FiniteEtale.affineEquivalence
    (CommRingCat.of (R ⧸ I))
  let : B.IsEquivalence :=
    finiteEtale_baseChange_isEquivalence_of_le_maximalIdeal I hI
  have :
      ((AlgebraicGeometry.FiniteEtale.affineEquivalence
          (CommRingCat.of R)).functor ⋙ B).IsEquivalence := inferInstance
  have : (F.op ⋙ E.functor).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (AlgebraicGeometry.FiniteEtale.affineEquivalenceCompBaseChangeIso
        R (R ⧸ I))
  have : F.op.IsEquivalence :=
    Functor.isEquivalence_of_comp_right F.op E.functor
  have : F.op.unop.IsEquivalence :=
    F.op.asEquivalence.unop.isEquivalence_functor
  exact Functor.isEquivalence_of_iso (Functor.opUnopIso F)

/-- The categorical equivalence on finite étale covers induced by
`Spec (R ⧸ I) ⟶ Spec R`. -/
def finiteEtale_pullback_equivalence_of_complete_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    AlgebraicGeometry.FiniteEtale (AlgebraicGeometry.Spec (.of R)) ≌
      AlgebraicGeometry.FiniteEtale
        (AlgebraicGeometry.Spec (.of (R ⧸ I))) := by
  let F := AlgebraicGeometry.FiniteEtale.pullback
    (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  letI : F.IsEquivalence :=
    finiteEtale_pullback_isEquivalence_of_complete_quotient I hI
  exact F.asEquivalence

end EtaleFundamentalGroups
