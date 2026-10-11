/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.Henselian.BoundaryAwayNoetherian

/-!
# Boundary Away at an arbitrary normalization prime

An arbitrary closed normalization prime is supplied directly to Tag 00UJ.
The Henselian pointed comparison recovers that same input prime from the
chosen idempotent factor, so the primitive boundary Away theorem transports
to its literal prime-local ring.  Tag data and the comparison equivalence are
entirely internal to the proof.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe uR uL

/-- The primitive boundary Away map is etale at every closed prime of a
finite normalization over a Henselian local base.

The chosen factor and its comparison with `Localization.AtPrime p` are
produced by applying Tag 00UJ to `p` itself; neither appears as a hypothesis. -/
theorem arbitraryNormalizationPrime_boundaryAway_local
    {R : Type uR} {L : Type uL}
    [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field L] [Algebra R L]
    [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    [Module.Finite R (integralClosure R L)]
    (f : R)
    (hAway :
      (Localization.awayMap
        (algebraMap R (integralClosure R L)) f).Etale)
    (p : Ideal (integralClosure R L)) [p.IsPrime]
    [p.LiesOver (IsLocalRing.maximalIdeal R)] :
    @RingHom.Etale
      (Localization.Away f)
      (Localization.Away
        (algebraMap R (Localization.AtPrime p) f))
      _ _
      (Localization.awayMap
        (algebraMap R (Localization.AtPrime p)) f) := by
  exact arbitraryNormalizationPrime_boundaryAway_local_without_noetherian
    f hAway p

end EtaleFundamentalGroups.Kummer

end
