/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.CompleteLocalSymbolicPowers
import EtaleFundamentalGroups.Purity.SymbolicPowerErrorArtinian
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The Artinian error between symbolic and ordinary powers

For a prime `P` with `dim (R / P) ≤ 1`, the image of `P^(n)` in `R / P^n`
is an Artinian `R`-module.  A common denominator outside `P` annihilates
this image, as does `P^n`.  The image is therefore a finite module over the
Artinian quotient by `P^n + (s)`.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

/-- The difference between a symbolic power and the ordinary power is an
Artinian module when the prime quotient has dimension at most one. -/
theorem isArtinian_primeSymbolicPower_quotient_pow
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime]
    (hdim : ringKrullDim (R ⧸ P) ≤ (1 : WithBot ℕ∞)) (n : ℕ) :
    IsArtinian R
      (Submodule.map (Submodule.mkQ (P ^ n))
        (primeSymbolicPower P n : Submodule R R)) := by
  let K : Submodule R (R ⧸ P ^ n) :=
    Submodule.map (Submodule.mkQ (P ^ n))
      (primeSymbolicPower P n : Submodule R R)
  obtain ⟨s, hs, hsmul⟩ := exists_mul_primeSymbolicPower_mem_pow P n
  let I : Ideal R := P ^ n ⊔ Ideal.span {s}
  have hpow : P ^ n ≤ Module.annihilator R K := by
    intro a ha
    apply Module.mem_annihilator.mpr
    intro z
    apply Subtype.ext
    change a • (z : R ⧸ P ^ n) = (0 : R ⧸ P ^ n)
    obtain ⟨r, hr⟩ := Submodule.mkQ_surjective (P ^ n) (z : R ⧸ P ^ n)
    rw [← hr]
    change Ideal.Quotient.mk (P ^ n) (a * r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((P ^ n).mul_mem_right r ha)
  have hsAnn : s ∈ Module.annihilator R K := by
    apply Module.mem_annihilator.mpr
    intro z
    obtain ⟨r, hr, hrz⟩ := Submodule.mem_map.mp z.property
    apply Subtype.ext
    change s • (z : R ⧸ P ^ n) = (0 : R ⧸ P ^ n)
    rw [← hrz]
    change Ideal.Quotient.mk (P ^ n) (s * r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hsmul r hr)
  have hI : I ≤ Module.annihilator R K :=
    sup_le hpow ((Module.annihilator R K).span_singleton_le_iff_mem.mpr hsAnn)
  have hTorsion : Module.IsTorsionBySet R K I :=
    (Module.isTorsionBySet_iff_subset_annihilator R K).mpr hI
  let : Module.Finite R K :=
    Module.Finite.of_fg
      ((IsNoetherian.noetherian (primeSymbolicPower P n)).map
        (Submodule.mkQ (P ^ n)))
  let : Module (R ⧸ I) K := hTorsion.module
  let : Module.Finite (R ⧸ I) K :=
    Module.Finite.of_surjective hTorsion.semilinearMap Function.surjective_id
  let : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_quotient_pow_sup_span_singleton P hdim n s hs
  have hK : IsArtinian (R ⧸ I) K := isArtinian_of_fg_of_artinian'
  exact
    (LinearMap.isArtinian_iff_of_bijective
      hTorsion.semilinearMap Function.bijective_id).mpr hK

end EtaleFundamentalGroups.Purity

end
