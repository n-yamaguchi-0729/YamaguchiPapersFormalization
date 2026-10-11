/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import GaloisCohomology.Kummer.Concrete.AbsoluteH1Action
import ProCGroups.Abelian.AbelianModPower
import Mathlib.Topology.Instances.ZMod

/-!
# Relative Galois conjugation on the abelianization modulo powers

The conjugation map on the absolute Galois group is a continuous
automorphism. Passing to its topological abelianization and then modulo
`q`-th powers gives the actual map used in Section 3.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ClassFieldTower.ProP

/-- A nontrivial inverse pullback action on degree-one classes gives a
character moved by forward conjugation. -/
theorem exists_changed_character_of_inverse_relativeH1Action_ne_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (q : ℕ) (τ : Gal(L/K))
    (hτ : relativeGaloisH1Action (n := q) K L τ⁻¹ ≠ 1) :
    ∃ χ : Gal(AlgebraicClosure L/L) →ₜ* Multiplicative (ZMod q),
      ∃ σ : Gal(AlgebraicClosure L/L),
        χ (absoluteGaloisConjugate τ.toRingEquiv σ) ≠ χ σ := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ContinuousH1ZMod (p := q)
      (G := Field.absoluteGaloisGroup L),
      (relativeGaloisH1Action (n := q) K L τ⁻¹).toAdd c ≠ c := by
    by_contra hnot
    apply hτ
    apply AddEquiv.ext
    intro c
    exact not_not.mp (fun hne => hnot ⟨c, hne⟩)
  obtain ⟨σ, hσ⟩ : ∃ σ : Additive (Field.absoluteGaloisGroup L),
      (relativeGaloisH1Action (n := q) K L τ⁻¹).toAdd c σ ≠ c σ := by
    by_contra hnot
    apply hc
    apply ContinuousAddMonoidHom.ext
    intro σ
    exact not_not.mp (fun hne => hnot ⟨σ, hne⟩)
  let σ₀ : Gal(AlgebraicClosure L/L) := σ.toMul
  let χ : Gal(AlgebraicClosure L/L) →ₜ* Multiplicative (ZMod q) := characterOfH1 c
  refine ⟨χ, σ₀, ?_⟩
  intro heq
  apply hσ
  change c (Additive.ofMul (absoluteGaloisConjugate τ.toRingEquiv σ₀)) =
    c (Additive.ofMul σ₀)
  exact congrArg Multiplicative.toAdd heq

end ClassFieldTower.Martinet.Shafarevich

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ProCGroups.Abelian

universe u

/-- The map on `G_Lᵃᵇ/q` induced by a relative Galois automorphism.
It is constructed from the chosen continuous conjugation of `G_L`; the
choice disappears on abelianization. -/
noncomputable def relativeGaloisAbelianModPowerTransform
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (q : ℕ) (τ : Gal(L/K)) :
    abelianModPower Gal(AlgebraicClosure L/L) q →*
      abelianModPower Gal(AlgebraicClosure L/L) q :=
  abelianModPowerMap q
    (ContinuousMonoidHom.toContinuousMonoidHom
      (absoluteGaloisConjugateContinuousEquiv τ.toRingEquiv))

/-- Conjugation on `G_Lᵃᵇ/q` evaluates on the canonical quotient image. -/
theorem relativeGaloisAbelianModPowerTransform_apply_mk
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (q : ℕ) (τ : Gal(L/K)) (σ : Gal(AlgebraicClosure L/L)) :
    relativeGaloisAbelianModPowerTransform K L q τ
        ((TopologicalAbelianization.mk Gal(AlgebraicClosure L/L) σ :
          TopologicalAbelianization Gal(AlgebraicClosure L/L)) :
          abelianModPower Gal(AlgebraicClosure L/L) q) =
      ((TopologicalAbelianization.mk Gal(AlgebraicClosure L/L)
          (absoluteGaloisConjugate τ.toRingEquiv σ) :
        TopologicalAbelianization Gal(AlgebraicClosure L/L)) :
        abelianModPower Gal(AlgebraicClosure L/L) q) := by
  rfl

/-- A nontrivial inverse action on continuous H¹ moves an element of the
actual quotient `G_Lᵃᵇ/q` under forward relative Galois conjugation. -/
theorem exists_moved_abelianModPower_of_inverse_relativeH1Action_ne_one
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (q : ℕ) (τ : Gal(L/K))
    (hτ : relativeGaloisH1Action (n := q) K L τ⁻¹ ≠ 1) :
    ∃ z : abelianModPower Gal(AlgebraicClosure L/L) q,
      relativeGaloisAbelianModPowerTransform K L q τ z ≠ z := by
  obtain ⟨χ, σ, hχ⟩ :=
    ClassFieldTower.Martinet.Shafarevich.exists_changed_character_of_inverse_relativeH1Action_ne_one
      q τ hτ
  let z : abelianModPower Gal(AlgebraicClosure L/L) q :=
    (TopologicalAbelianization.mk _ σ : TopologicalAbelianization _)
  refine ⟨z, ?_⟩
  intro hz
  have hpow : ∀ a : Multiplicative (ZMod q), a ^ q = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    change q • a.toAdd = (0 : ZMod q)
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let χbar := abelianModPowerLift q χ hpow
  have hquotient :
      ((TopologicalAbelianization.mk _
        (absoluteGaloisConjugate τ.toRingEquiv σ) : TopologicalAbelianization _) :
        abelianModPower Gal(AlgebraicClosure L/L) q) = z := by
    rw [← relativeGaloisAbelianModPowerTransform_apply_mk]
    exact hz
  have hvalue := congrArg χbar hquotient
  apply hχ
  simp only [χbar, z] at hvalue
  change χ (absoluteGaloisConjugate τ.toRingEquiv σ) = χ σ at hvalue
  exact hvalue

end Yamaguchi26AbfaithfulGalois
