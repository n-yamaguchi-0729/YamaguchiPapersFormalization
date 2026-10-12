/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerSplittingField
import Nyll.AnabelianGeometry.KummerTheory.TwistedRootFields

/-!
# Root fields detected by equivalent fibre actions

Equivariant identifications of actual Kummer fibres preserve their root
fields. Simultaneous pointwise stabilizers detect the compositum of two
root fields; their common-twist family detects the root field of the ratio.
-/

noncomputable section

namespace AnabelianGeometry.GeometricFundamentalGroup

open AnabelianGeometry.KummerTheory

universe u v w

/-- Equivariant bijections preserve the pointwise stabilizer of an entire action. -/
theorem iInf_stabilizer_eq_of_equivariant_equiv
    {G : Type u} [Group G] {X : Type v} {Y : Type w}
    [MulAction G X] [MulAction G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    (⨅ x : X, MulAction.stabilizer G x) = ⨅ y : Y, MulAction.stabilizer G y := by
  ext g
  simp only [Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← he, h x]
  · intro h x
    apply e.injective
    rw [he, h (e x)]

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- Equivariantly equivalent actual Kummer fibres have the same full root field. -/
theorem rootField_eq_of_equivariant_fiber_equiv [IsGalois K L]
    (n : ℕ) (a b : Kˣ)
    (e : LaurentKummerFiberHom (L := L) n a ≃ LaurentKummerFiberHom (L := L) n b)
    (he : ∀ (σ : L ≃ₐ[K] L) (f : LaurentKummerFiberHom (L := L) n a),
      e (σ • f) = σ • e f) :
    rootField (L := L) n (a : K) = rootField (L := L) n (b : K) := by
  rw [← fixedField_laurentKummerFiber_pointwise_stabilizer n a,
    ← fixedField_laurentKummerFiber_pointwise_stabilizer n b,
    iInf_stabilizer_eq_of_equivariant_equiv e he]

/-- Simultaneous pointwise fixing of two fibres detects their compositum. -/
theorem fixedField_two_fiber_stabilizers [IsGalois K L] (n : ℕ) (a b : Kˣ) :
    IntermediateField.fixedField
      ((⨅ f : LaurentKummerFiberHom (L := L) n a,
        MulAction.stabilizer (L ≃ₐ[K] L) f) ⊓
       (⨅ f : LaurentKummerFiberHom (L := L) n b,
        MulAction.stabilizer (L ≃ₐ[K] L) f)) =
      rootField (L := L) n (a : K) ⊔ rootField (L := L) n (b : K) := by
  rw [laurentKummerFiber_pointwise_stabilizer, laurentKummerFiber_pointwise_stabilizer,
    ← IntermediateField.fixingSubgroup_sup, InfiniteGalois.fixedField_fixingSubgroup]

/-- Equality of the simultaneous fibre stabilizers for all common twists
forces equality of the full root fields of the two ratios. -/
theorem rootField_ratio_eq_of_twisted_stabilizers [IsGalois K L] [IsAlgClosed L]
    (n : ℕ) (hn : 0 < n) (x y x' y' : Kˣ)
    (h : ∀ c : Kˣ,
      ((⨅ f : LaurentKummerFiberHom (L := L) n (c * x),
        MulAction.stabilizer (L ≃ₐ[K] L) f) ⊓
       (⨅ f : LaurentKummerFiberHom (L := L) n (c * y),
        MulAction.stabilizer (L ≃ₐ[K] L) f)) =
      ((⨅ f : LaurentKummerFiberHom (L := L) n (c * x'),
        MulAction.stabilizer (L ≃ₐ[K] L) f) ⊓
       (⨅ f : LaurentKummerFiberHom (L := L) n (c * y'),
        MulAction.stabilizer (L ≃ₐ[K] L) f))) :
    rootField (L := L) n ((y / x : Kˣ) : K) =
      rootField (L := L) n ((y' / x' : Kˣ) : K) := by
  rw [← iInf_twisted_rootFields_eq n hn x y, ← iInf_twisted_rootFields_eq n hn x' y']
  apply iInf_congr
  intro c
  rw [← fixedField_two_fiber_stabilizers n (c * x) (c * y),
    ← fixedField_two_fiber_stabilizers n (c * x') (c * y'), h c]

end AnabelianGeometry.GeometricFundamentalGroup
