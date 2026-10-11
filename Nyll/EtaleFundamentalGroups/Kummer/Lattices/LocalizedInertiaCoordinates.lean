/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Laurent.DiagonalRadical
import Nyll.EtaleFundamentalGroups.Kummer.Lattices.FractionFieldGalois
import Nyll.EtaleFundamentalGroups.Inertia.Localized.CyclicCoordinates

/-!
# Smith coordinates for localized lattice-cover inertia

The quotient-character action identifies the Galois group of a finite lattice
cover with the character group of its quotient lattice.  At a height-one prime
of any regular model of the base fraction field, localized normalization
inertia embeds into that Galois group.  The Smith coordinates used by the
iterated-radical presentation then give an injective coordinate map from the
cyclic inertia coordinate to the same product of `ZMod` factors.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u

/--
For a finite-index lattice cover, localized normalization inertia at a
height-one characteristic-zero point embeds in the product of cyclic groups
coming from the same Smith choice as the iterated-radical presentation.

The embedding is produced by composing the inertia inclusion with the
fraction-field `IsGaloisGroup` equivalence, a chosen finite-character duality,
and the Smith quotient equivalence.  Its injectivity is therefore generated
from source-produced equivalences and the subgroup inclusion; it is not an
assumption.
-/
theorem exists_localizedNormalizationInertiaZModSmithEmbedding
    {k L : Type u} [CommRing k] [IsDomain k] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    let A₀ := AddMonoidAlgebra k H
    let B := AddMonoidAlgebra k L
    letI : UniqueSums L := latticeUniqueSums_of_freeIntModule L
    letI : UniqueSums H :=
      latticeSubgroupUniqueSums H.toAddSubgroup
    letI : IsDomain A₀ := inferInstance
    letI : IsDomain B := inferInstance
    letI : Algebra A₀ B :=
      latticeMapDomainAlgebra H.toAddSubgroup
    letI : FaithfulSMul A₀ B :=
      latticeMapDomainFaithfulSMul H.toAddSubgroup
    let K := FractionRing A₀
    let E := FractionRing B
    letI : Algebra K E := FractionRing.liftAlgebra A₀ E
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRegularRing A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A E] [IsScalarTower A K E]
      (P : Ideal A) [P.IsPrime] (_hP : P.height = 1)
      (Q : Ideal (integralClosure A E)) [Q.IsPrime] [Q.LiesOver P]
      [CharZero (A ⧸ P)],
      let I := localizedNormalizationInertia (K := K) (L := E) P Q
      ∃ (r : ℕ) (n : Fin r → ℕ),
        (∀ i, 0 < n i) ∧
          ∃ (eQ : (L ⧸ H) ≃+ ∀ i, ZMod (n i))
            (eH : AddMonoidAlgebra k H ≃+*
              AddMonoidAlgebra k (Fin r → ℤ))
            (eL : AddMonoidAlgebra k L ≃+*
              AddMonoidAlgebra k (Fin r → ℤ))
            (eRad : nestedDiagonalRadical k r n ≃+*
              AddMonoidAlgebra k (Fin r → ℤ)),
            eL.toRingHom.comp
                (AddMonoidAlgebra.mapDomainRingHom k
                  H.subtype.toAddMonoidHom) =
              eRad.toRingHom.comp
                ((finDiagonalRadicalBase k n).comp eH.toRingHom) ∧
              ∃ (N : AddSubgroup (L ⧸ H))
                (eI : ZMod (Nat.card I) ≃+ N),
                Function.Injective
                  (eQ.toAddMonoidHom.comp
                    (N.subtype.comp eI.toAddMonoidHom)) := by
  dsimp only
  let A₀ := AddMonoidAlgebra k H
  let B := AddMonoidAlgebra k L
  let : Finite (L ⧸ H.toAddSubgroup) := by
    change Finite (L ⧸ H)
    infer_instance
  let : HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H.toAddSubgroup))) := by
    change HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))
    infer_instance
  let G := Multiplicative (L ⧸ H.toAddSubgroup) →* kˣ
  let K := FractionRing A₀
  let E := FractionRing B
  let : UniqueSums L := latticeUniqueSums_of_freeIntModule L
  let : UniqueSums H :=
    latticeSubgroupUniqueSums H.toAddSubgroup
  let : IsDomain A₀ := inferInstance
  let : IsDomain B := inferInstance
  let : Algebra A₀ B :=
    latticeMapDomainAlgebra H.toAddSubgroup
  let : FaithfulSMul A₀ B :=
    latticeMapDomainFaithfulSMul H.toAddSubgroup
  let : Algebra K E := FractionRing.liftAlgebra A₀ E
  let : MulSemiringAction G B :=
    latticeCharacterMulSemiringAction H.toAddSubgroup
  let : MulSemiringAction G E :=
    IsFractionRing.mulSemiringAction G B E
  intro A _ _ _ _ _ _ _ P _ hP Q _ _ _
  let : Finite G :=
    latticeCharacterGroupFinite H.toAddSubgroup
  have : IsGaloisGroup G K E :=
    latticeCharacter_isGaloisGroup_fractionRing H.toAddSubgroup
  let : FiniteDimensional K E :=
    IsGaloisGroup.finiteDimensional G K E
  let : IsGalois K E := IsGaloisGroup.isGalois G K E
  obtain ⟨r, n, hn, eQ, eH, eL, eRad, hsquare⟩ :=
    exists_smithDiagonalRadicalPresentation (R := k) H
  let I := localizedNormalizationInertia (K := K) (L := E) P Q
  let galoisEquiv : G ≃* Gal(E/K) :=
    IsGaloisGroup.mulEquivAlgEquiv G K E
  let characterDuality : G ≃* Multiplicative (L ⧸ H) :=
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      (Multiplicative (L ⧸ H)) k).some
  let galToQuotientMul : Gal(E/K) ≃* Multiplicative (L ⧸ H) :=
    galoisEquiv.symm.trans characterDuality
  let galToQuotientAdd : Additive Gal(E/K) ≃+ (L ⧸ H) :=
    galToQuotientMul.toAdditive.trans
      (AddEquiv.additiveMultiplicative (L ⧸ H))
  let inertiaCyclic : Additive I ≃+ ZMod (Nat.card I) :=
    localizedNormalizationInertiaAddEquivZMod
      (A := A) (K := K) (L := E) P hP Q
  let N : AddSubgroup (L ⧸ H) :=
    I.toAddSubgroup.map galToQuotientAdd.toAddMonoidHom
  let inertiaToN : Additive I ≃+ N :=
    I.toAddSubgroup.equivMapOfInjective
      galToQuotientAdd.toAddMonoidHom galToQuotientAdd.injective
  let eI : ZMod (Nat.card I) ≃+ N :=
    inertiaCyclic.symm.trans inertiaToN
  refine ⟨r, n, hn, eQ, eH, eL, eRad, hsquare, N, eI, ?_⟩
  exact eQ.injective.comp (N.subtype_injective.comp eI.injective)

end EtaleFundamentalGroups.Kummer

end
