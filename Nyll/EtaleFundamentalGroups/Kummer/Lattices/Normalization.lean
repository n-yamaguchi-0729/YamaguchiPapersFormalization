/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Lattices.IntegralCover
import Nyll.EtaleFundamentalGroups.Kummer.Laurent.IntegrallyClosed

/-!
# Normalization of a finite-index lattice cover

For a finite-index inclusion of finite free integer lattices, the target
monoid algebra is integral over the source and is an integrally closed domain.
Consequently it is the integral closure of the source in its own fraction
field.  The algebra structures below are the maps occurring in the lattice
cover and their single composite with the fraction-field inclusion.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u

/--
The target of a finite-index lattice monoid-algebra cover is the normalization
of the source in the target fraction field.
-/
theorem latticeMonoidAlgebra_isIntegralClosure_in_fractionRing
    {R L : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)] :
    let A := AddMonoidAlgebra R H
    let B := AddMonoidAlgebra R L
    let f := AddMonoidAlgebra.mapDomainRingHom R
      H.subtype.toAddMonoidHom
    letI : Algebra A B := f.toAlgebra
    IsIntegralClosure B A (FractionRing B) := by
  dsimp only
  let f := AddMonoidAlgebra.mapDomainRingHom R
    H.subtype.toAddMonoidHom
  let : Algebra (AddMonoidAlgebra R H) (AddMonoidAlgebra R L) :=
    f.toAlgebra
  have hIntegral := latticeMonoidAlgebraMap_isIntegral (R := R) H
  let : Algebra.IsIntegral (AddMonoidAlgebra R H)
      (AddMonoidAlgebra R L) :=
    algebraMap_isIntegral_iff.mp (by
      simpa only [RingHom.algebraMap_toAlgebra, f] using hIntegral)
  let : IsIntegrallyClosed (AddMonoidAlgebra R L) :=
    latticeMonoidAlgebra_isIntegrallyClosed
  infer_instance

end EtaleFundamentalGroups.Kummer
