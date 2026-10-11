/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.FreeModule.Basic
import Nyll.EtaleFundamentalGroups.Kummer.Lattices.GaloisGroup

/-!
# Fraction-field Galois extension of a finite lattice cover

The quotient-character action on a lattice algebra extends canonically to its
fraction field.  The ring-level `IsGaloisGroup` producer and mathlib's
fraction-ring transport then identify the same finite character group as a
Galois group of the fraction-field extension.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u v

/-- A free abelian group has unique sums, via the coordinates of a chosen
`ℤ`-basis.  This is a named producer so lattice-algebra domain instances can
remain local to fraction-field consumers. -/
theorem latticeUniqueSums_of_freeIntModule
    (L : Type v) [AddCommGroup L] [Module.Free ℤ L] : UniqueSums L :=
  UniqueSums.of_injective_addHom
    (Module.Free.chooseBasis ℤ L).repr.toLinearMap.toAddHom
    (Module.Free.chooseBasis ℤ L).repr.injective inferInstance

/-- A subgroup of a unique-sums abelian group has unique sums. -/
theorem latticeSubgroupUniqueSums
    {L : Type v} [AddCommGroup L] [UniqueSums L] (H : AddSubgroup L) :
    UniqueSums H :=
  UniqueSums.of_injective_addHom (G := L) (H := H) H.subtype.toAddHom
    H.subtype_injective inferInstance

/--
The finite quotient-character group is a Galois group for the induced
extension of lattice fraction fields.  All actions and algebra structures are
the named canonical producers from the ring-level lattice cover.
-/
theorem latticeCharacter_isGaloisGroup_fractionRing
    {k : Type u} {L : Type v} [CommRing k] [IsDomain k]
    [AddCommGroup L]
    [Module.Free ℤ L]
    (H : AddSubgroup L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    let A := AddMonoidAlgebra k H
    let B := AddMonoidAlgebra k L
    let G := Multiplicative (L ⧸ H) →* kˣ
    letI : UniqueSums L := latticeUniqueSums_of_freeIntModule L
    letI : UniqueSums H := latticeSubgroupUniqueSums H
    letI : IsDomain A := inferInstance
    letI : IsDomain B := inferInstance
    letI : Algebra A B := latticeMapDomainAlgebra H
    letI : FaithfulSMul A B := latticeMapDomainFaithfulSMul H
    let K := FractionRing A
    let E := FractionRing B
    letI : Algebra K E := FractionRing.liftAlgebra A E
    letI : MulSemiringAction G B := latticeCharacterMulSemiringAction H
    letI : MulSemiringAction G E := IsFractionRing.mulSemiringAction G B E
    IsGaloisGroup G K E := by
  dsimp only
  let A := AddMonoidAlgebra k H
  let B := AddMonoidAlgebra k L
  let G := Multiplicative (L ⧸ H) →* kˣ
  let K := FractionRing A
  let E := FractionRing B
  let : UniqueSums L := latticeUniqueSums_of_freeIntModule L
  let : UniqueSums H := latticeSubgroupUniqueSums H
  let : IsDomain A := inferInstance
  let : IsDomain B := inferInstance
  let : Algebra A B := latticeMapDomainAlgebra H
  let : FaithfulSMul A B := latticeMapDomainFaithfulSMul H
  let : Algebra K E := FractionRing.liftAlgebra A E
  let : MulSemiringAction G B := latticeCharacterMulSemiringAction H
  let : MulSemiringAction G E := IsFractionRing.mulSemiringAction G B E
  let : Finite G := latticeCharacterGroupFinite H
  have : IsGaloisGroup G A B := latticeCharacter_isGaloisGroup H
  infer_instance

end EtaleFundamentalGroups.Kummer
