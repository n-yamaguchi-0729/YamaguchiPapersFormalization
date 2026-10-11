/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.AffineCompleteBaseChange
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumQuotient

/-!
# The categorical hypersurface step for punctured local purity

For a complete Noetherian local ring, finite-etale covers of a quotient lift
uniquely to the ambient affine spectrum.  If restriction from the ambient
puncture to the quotient puncture is fully faithful, purity for the quotient
therefore implies purity for the ambient ring.  This isolates the genuine
local Lefschetz input from the already formalized complete-quotient lifting.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- The complete hypersurface induction step for local purity.

The first hypothesis is purity one dimension lower.  The second is the
substantive local-Lefschetz assertion that a finite-etale cover, and every map
between such covers, is determined on the quotient puncture.  The conclusion
is obtained by lifting the lower-dimensional extension across the complete
quotient and then reflecting its comparison isomorphism through that fully
faithful restriction functor. -/
theorem hasPuncturedPurity_of_complete_quotient_of_fullyFaithful
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    AlgebraicGeometry.FiniteEtale.HasPuncturedPurity (R ⧸ I) →
      (AlgebraicGeometry.FiniteEtale.pullback
        (AlgebraicGeometry.Scheme.puncturedSpectrumQuotientMorphism
          R I hI)).FullyFaithful →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity R := by
  let : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  intro hquotient hlefschetz
  rw [AlgebraicGeometry.FiniteEtale.hasPuncturedPurity_iff] at hquotient ⊢
  intro W
  let j := AlgebraicGeometry.Scheme.puncturedSpectrumInclusion R
  let jI :=
    AlgebraicGeometry.Scheme.puncturedSpectrumInclusion (R ⧸ I)
  let q := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let g := AlgebraicGeometry.Scheme.puncturedSpectrumQuotientMorphism
    R I hI
  let Fj := AlgebraicGeometry.FiniteEtale.pullback j
  let FjI := AlgebraicGeometry.FiniteEtale.pullback jI
  let Fq := AlgebraicGeometry.FiniteEtale.pullback q
  let Fg := AlgebraicGeometry.FiniteEtale.pullback g
  let WI := Fg.obj W
  obtain ⟨ZI, ⟨eZI⟩⟩ := hquotient WI
  let : Fq.IsEquivalence := by
    dsimp only [Fq, q]
    exact finiteEtale_pullback_isEquivalence_of_complete_quotient I hI
  obtain ⟨Z, ⟨eZ⟩⟩ :=
    (inferInstance : Fq.EssSurj).mem_essImage ZI
  let eSquare : Fg.obj (Fj.obj Z) ≅ FjI.obj (Fq.obj Z) :=
    (AlgebraicGeometry.Scheme.puncturedSpectrumQuotientPullbackIso
      R I hI).app Z
  let eRestricted : Fg.obj (Fj.obj Z) ≅ Fg.obj W :=
    eSquare ≪≫ FjI.mapIso eZ ≪≫ eZI
  refine ⟨Z, ⟨?_⟩⟩
  exact hlefschetz.preimageIso eRestricted

/-- The complete hypersurface induction step in connected-cover form.

Instead of requiring full faithfulness as input, it is enough to prove the
geometric local-Lefschetz assertion that every connected finite-etale cover
of the ambient puncture stays connected on the quotient puncture.  The
Galois-category connected-object criterion produces full faithfulness, after
which `hasPuncturedPurity_of_complete_quotient_of_fullyFaithful` applies. -/
theorem hasPuncturedPurity_of_complete_quotient_of_preserves_connected
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    ConnectedSpace (AlgebraicGeometry.Scheme.puncturedSpectrum R) →
      ConnectedSpace
        (AlgebraicGeometry.Scheme.puncturedSpectrum (R ⧸ I)) →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity (R ⧸ I) →
      (∀ W : AlgebraicGeometry.FiniteEtale
          (AlgebraicGeometry.Scheme.puncturedSpectrum R),
        CategoryTheory.PreGaloisCategory.IsConnected W →
          CategoryTheory.PreGaloisCategory.IsConnected
            ((AlgebraicGeometry.FiniteEtale.pullback
              (AlgebraicGeometry.Scheme.puncturedSpectrumQuotientMorphism
                R I hI)).obj W)) →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity R := by
  let : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  intro hconnectedR hconnectedQuotient hpurity hpreserves
  let : ConnectedSpace
      (AlgebraicGeometry.Scheme.puncturedSpectrum R) := hconnectedR
  let : ConnectedSpace
      (AlgebraicGeometry.Scheme.puncturedSpectrum (R ⧸ I)) :=
    hconnectedQuotient
  let g := AlgebraicGeometry.Scheme.puncturedSpectrumQuotientMorphism
    R I hI
  have hfullyFaithful : Nonempty
      (AlgebraicGeometry.FiniteEtale.pullback g).FullyFaithful :=
    AlgebraicGeometry.FiniteEtale.pullback_fullyFaithful_of_preserves_connected
      g hpreserves
  exact hasPuncturedPurity_of_complete_quotient_of_fullyFaithful
    I hI hpurity hfullyFaithful.some

end EtaleFundamentalGroups

end
