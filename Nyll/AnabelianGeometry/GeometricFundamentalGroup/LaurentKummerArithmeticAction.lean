/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerArithmeticFiber
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiberActionComparison

/-!
# The actual arithmetic action on Kummer fibres

The canonical Galois action on the geometric fibre of the pulled-back
finite-etale scheme agrees with postcomposition on the root algebra points.
Its pointwise stabilizer therefore recovers the full root field. This is a
comparison theorem for the existing geometric-fibre functor, not a newly
transported action defined to make the comparison true.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AnabelianGeometry.KummerTheory

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u
variable {K : Type u} [Field K] [CharZero K]
  {L : Type u} [Field L] [Algebra K L] [IsSepClosed L]

/-- The arithmetic-fibre comparison intertwines the existing geometric
Galois action with literal postcomposition on algebra points. -/
theorem laurentKummerArithmeticFiberEquiv_smul
    (n : ℕ) (hn : 0 < n) (a : Kˣ) (σ : L ≃ₐ[K] L)
    (z : (fib K L).obj (laurentKummerArithmeticFiber n hn a)) :
    laurentKummerArithmeticFiberEquiv n hn a (σ • z) =
      σ • laurentKummerArithmeticFiberEquiv n hn a z := by
  have hpoint :
      (fiberObjEquivHom (ξ K L) (laurentKummerArithmeticFiber n hn a) (σ • z)).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          (fiberObjEquivHom (ξ K L) (laurentKummerArithmeticFiber n hn a) z).left := by
    rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply, algEquiv_smul_hom]
    rfl
  have hspec :
      Spec.map (CommRingCat.ofHom
        (laurentKummerArithmeticFiberEquiv n hn a (σ • z)).val) =
      Spec.map (CommRingCat.ofHom
        (σ • laurentKummerArithmeticFiberEquiv n hn a z).val) := by
    erw [laurentKummerArithmeticFiberEquiv_spec, hpoint, Category.assoc,
      ← laurentKummerArithmeticFiberEquiv_spec]
    exact (Spec.map_comp
      (CommRingCat.ofHom (laurentKummerArithmeticFiberEquiv n hn a z).val)
      (CommRingCat.ofHom σ.toRingHom)).symm
  apply Subtype.ext
  have h := congrArg
    (fun p : Spec (.of L) ⟶ Spec (.of (LaurentKummerAlgebra K n)) =>
      (Spec.preimage p).hom) hspec
  simpa only [Spec.preimage_map, CommRingCat.hom_ofHom] using h

/-- The kernel of the actual arithmetic fibre action is the fixing subgroup
of the root field. -/
theorem laurentKummerArithmeticFiber_pointwise_stabilizer
    (n : ℕ) (hn : 0 < n) (a : Kˣ) :
    (⨅ z : (fib K L).obj (laurentKummerArithmeticFiber n hn a),
      MulAction.stabilizer (L ≃ₐ[K] L) z) =
      (rootField (L := L) n (a : K)).fixingSubgroup := by
  rw [iInf_stabilizer_eq_of_equivariant_equiv (laurentKummerArithmeticFiberEquiv n hn a)
    (laurentKummerArithmeticFiberEquiv_smul n hn a),
    laurentKummerFiber_pointwise_stabilizer]

/-- The pointwise stabilizer of the actual arithmetic geometric fibre
fixes exactly the full Kummer root field. -/
theorem fixedField_laurentKummerArithmeticFiber [IsGalois K L]
    (n : ℕ) (hn : 0 < n) (a : Kˣ) :
    IntermediateField.fixedField
      (⨅ z : (fib K L).obj (laurentKummerArithmeticFiber n hn a),
        MulAction.stabilizer (L ≃ₐ[K] L) z) = rootField (L := L) n (a : K) := by
  rw [iInf_stabilizer_eq_of_equivariant_equiv (laurentKummerArithmeticFiberEquiv n hn a)
    (laurentKummerArithmeticFiberEquiv_smul n hn a),
    fixedField_laurentKummerFiber_pointwise_stabilizer]

/-- An equivariant bijection of the actual arithmetic fibres determines
the same full Kummer root field. -/
theorem rootField_eq_of_arithmeticFiber_equiv [IsGalois K L]
    (n : ℕ) (hn : 0 < n) (a b : Kˣ)
    (e : (fib K L).obj (laurentKummerArithmeticFiber n hn a) ≃
      (fib K L).obj (laurentKummerArithmeticFiber n hn b))
    (he : ∀ (σ : L ≃ₐ[K] L) (z : (fib K L).obj (laurentKummerArithmeticFiber n hn a)),
      e (σ • z) = σ • e z) :
    rootField (L := L) n (a : K) = rootField (L := L) n (b : K) := by
  rw [← fixedField_laurentKummerArithmeticFiber n hn a,
    ← fixedField_laurentKummerArithmeticFiber n hn b,
    iInf_stabilizer_eq_of_equivariant_equiv e he]

/-- Simultaneous pointwise fixing in two actual finite-etale fibres recovers
the compositum of their root fields. -/
theorem fixedField_two_arithmeticFiber_stabilizers [IsGalois K L]
    (n : ℕ) (hn : 0 < n) (a b : Kˣ) :
    IntermediateField.fixedField
      ((⨅ z : (fib K L).obj (laurentKummerArithmeticFiber n hn a),
        MulAction.stabilizer (L ≃ₐ[K] L) z) ⊓
       (⨅ z : (fib K L).obj (laurentKummerArithmeticFiber n hn b),
        MulAction.stabilizer (L ≃ₐ[K] L) z)) =
      rootField (L := L) n (a : K) ⊔ rootField (L := L) n (b : K) := by
  rw [laurentKummerArithmeticFiber_pointwise_stabilizer,
    laurentKummerArithmeticFiber_pointwise_stabilizer,
    ← IntermediateField.fixingSubgroup_sup, InfiniteGalois.fixedField_fixingSubgroup]

/-- The common-twist family of actual arithmetic fibre actions recovers
the root field of the ratio. -/
theorem iInf_fixedField_twisted_arithmeticFibers [IsGalois K L] [IsAlgClosed L]
    (n : ℕ) (hn : 0 < n) (x y : Kˣ) :
    (⨅ c : Kˣ, IntermediateField.fixedField
      ((⨅ z : (fib K L).obj (laurentKummerArithmeticFiber n hn (c * x)),
        MulAction.stabilizer (L ≃ₐ[K] L) z) ⊓
       (⨅ z : (fib K L).obj (laurentKummerArithmeticFiber n hn (c * y)),
        MulAction.stabilizer (L ≃ₐ[K] L) z))) =
      rootField (L := L) n ((y / x : Kˣ) : K) := by
  simp_rw [fixedField_two_arithmeticFiber_stabilizers]
  exact iInf_twisted_rootFields_eq n hn x y

end AnabelianGeometry.GeometricFundamentalGroup
