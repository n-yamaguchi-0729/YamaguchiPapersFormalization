/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.PointedH1Pullback
import EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import EtaleFundamentalGroups.GeometricFiber.DeckFundamentalGroup
import EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
import GaloisCohomology.ProP.FiniteCoefficientTransfer

/-!
# Descent of actual finite-coefficient H¹ along Galois covers

For coefficient order coprime to the covering subgroup index, a class fixed by
every actual geometric deck pullback descends to the base. The proof constructs
the descended character by normalized continuous transfer, using the proved
geometric deck/conjugation comparison and actual derived-H¹ naturality.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ClassFieldTower.Cohomology

namespace EtaleFundamentalGroups.Cohomology

variable {S : Scheme.{u}} [ConnectedSpace S] (A : FiniteEtale S)
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
variable (xi : Spec (.of Ω) ⟶ A.left)

local instance baseFiberFunctor :
    FiberFunctor (FiniteEtale.fiber (xi ≫ A.hom)) :=
  FiniteEtale.fiberFunctor (X := S) (xi ≫ A.hom)

/-- The actual open subgroup of the base fundamental group selected by the
lifted geometric point of a finite étale cover. -/
def pointedCoverOpenSubgroup :
    OpenSubgroup (Aut (FiniteEtale.fiber (xi ≫ A.hom))) where
  toSubgroup := MulAction.stabilizer _ (FiniteEtale.liftedFiberPoint A xi)
  isOpen' := stabilizer_isOpen _ (FiniteEtale.liftedFiberPoint A xi)

variable [IsGalois (C := FiniteEtale S) A] [ConnectedSpace A.left]
variable (B : AddCommGrpCat.{u}) [Finite B]

/-- Actual derived H¹ pullback is injective for finite coefficients whose order
is coprime to the index of the Galois covering subgroup. -/
theorem constantH1Pullback_injective_of_coprime_index
    (hcop : (Nat.card (Multiplicative B)).Coprime
      (pointedCoverOpenSubgroup A xi).toSubgroup.index) :
    Function.Injective (constantCohomologyPullback A.hom B 1) := by
  let : TopologicalSpace (Multiplicative B) := ⊥
  let G := Aut (FiniteEtale.fiber (xi ≫ A.hom))
  let H : OpenSubgroup G := pointedCoverOpenSubgroup A xi
  have : H.toSubgroup.Normal :=
    stabilizer_normal_of_isGalois (C := FiniteEtale S)
      (FiniteEtale.fiber (X := S) (xi ≫ A.hom)) A
      (FiniteEtale.liftedFiberPoint A xi)
  let e : Aut (FiniteEtale.fiber xi) ≃ₜ* H :=
    FiniteEtale.fundamentalGroupEquivStabilizerOfLift A xi
  intro b c hbc
  apply h1Character_injective (X := S) B (xi ≫ A.hom)
  have he : (h1Character (X := S) B (xi ≫ A.hom) b).toMonoidHom =
      (h1Character (X := S) B (xi ≫ A.hom) c).toMonoidHom := by
    apply finiteCharacterRestriction_injective_of_coprime H.toSubgroup hcop
    apply MonoidHom.ext
    intro h
    let a := e.symm h
    have ha : FiniteEtale.fundamentalGroupHom A.hom xi a = (h : G) :=
      (FiniteEtale.fundamentalGroupEquivStabilizerOfLift_coe A xi a).symm.trans
        (congrArg (fun k : H => (k : G)) (e.apply_symm_apply h))
    have hb := congrArg
      (fun χ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B => χ a)
      (h1Character_schemePullback (X := A.left) (Y := S) A.hom B xi b)
    have hc := congrArg
      (fun χ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B => χ a)
      (h1Character_schemePullback (X := A.left) (Y := S) A.hom B xi c)
    change h1Character (X := S) B (xi ≫ A.hom) b (h : G) =
      h1Character (X := S) B (xi ≫ A.hom) c (h : G)
    rw [← ha]
    exact hb.trans ((congrArg (fun z => h1Character B xi z a) hbc).trans hc.symm)
  apply ContinuousMonoidHom.ext
  intro g
  exact DFunLike.congr_fun he g

/-- A deck-invariant actual derived H¹ class descends across a finite étale
Galois cover of coprime index. The class downstairs is constructed by transfer. -/
theorem exists_constantH1Pullback_eq_of_deckInvariant
    (hcop : (Nat.card (Multiplicative B)).Coprime
      (pointedCoverOpenSubgroup A xi).toSubgroup.index)
    (c : Sheaf.H.{u} ((constantSheaf A.left.smallEtaleTopology AddCommGrpCat.{u}).obj B) 1)
    (hinv : ∀ σ : Aut A, constantCohomologyPullback σ.hom.left B 1 c = c) :
    ∃ b : Sheaf.H.{u} ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj B) 1,
      constantCohomologyPullback A.hom B 1 b = c := by
  let : TopologicalSpace (Multiplicative B) := ⊥
  have : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
  let G := Aut (FiniteEtale.fiber (xi ≫ A.hom))
  let H : OpenSubgroup G := pointedCoverOpenSubgroup A xi
  have : H.toSubgroup.Normal :=
    stabilizer_normal_of_isGalois (C := FiniteEtale S)
      (FiniteEtale.fiber (X := S) (xi ≫ A.hom)) A
      (FiniteEtale.liftedFiberPoint A xi)
  let e : Aut (FiniteEtale.fiber xi) ≃ₜ* H :=
    FiniteEtale.fundamentalGroupEquivStabilizerOfLift A xi
  let χ := h1Character B xi c
  let es : H →ₜ* Aut (FiniteEtale.fiber xi) :=
    { __ := e.symm.toMonoidHom
      continuous_toFun := e.symm.continuous }
  let φ : H →ₜ* Multiplicative B := χ.comp es
  have hφ : ∀ (g : G) (h : H), φ (MulAut.conjNormal g h) = φ h := by
    intro g h
    let σ : Aut A :=
      (galoisObjectQuotientMonoidHom (C := FiniteEtale S) (FiniteEtale.fiber (xi ≫ A.hom)) G A
        (FiniteEtale.liftedFiberPoint A xi) g⁻¹).unop
    have hσ : (FiniteEtale.fiber (xi ≫ A.hom)).map σ.hom
        (FiniteEtale.liftedFiberPoint A xi) =
        g⁻¹ • FiniteEtale.liftedFiberPoint A xi :=
      galoisObjectQuotientMonoidHom_evaluation (C := FiniteEtale S)
        (FiniteEtale.fiber (xi ≫ A.hom)) G A (FiniteEtale.liftedFiberPoint A xi) g⁻¹
    let t := FiniteEtale.deckPointedGeometricFiberIso A xi σ g⁻¹ hσ
    let d := autHomOfCompIso (FiniteEtale.pullback σ.hom.left) t
    let a := e.symm h
    have ha : FiniteEtale.fundamentalGroupHom A.hom xi a = (h : G) :=
      (FiniteEtale.fundamentalGroupEquivStabilizerOfLift_coe A xi a).symm.trans
        (congrArg (fun k : H => (k : G)) (e.apply_symm_apply h))
    have hd : e (d a) = MulAut.conjNormal g h := by
      apply Subtype.ext
      change (FiniteEtale.fundamentalGroupEquivStabilizerOfLift A xi (d a) : G) =
        g * (h : G) * g⁻¹
      rw [FiniteEtale.fundamentalGroupEquivStabilizerOfLift_coe]
      have ht := FiniteEtale.fundamentalGroupHom_deckPointed A xi σ g⁻¹ hσ a
      change FiniteEtale.fundamentalGroupHom A.hom xi (d a) = _ at ht
      exact ht.trans (by rw [inv_inv, ha])
    have hp : χ (d a) = χ a := by
      have hn := congrArg
        (fun ψ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B => ψ a)
        (h1Character_pointedSchemePullback σ.hom.left B xi xi t c)
      exact hn.trans (congrArg (fun z => h1Character B xi z a) (hinv σ))
    change χ (e.symm (MulAut.conjNormal g h)) = χ (e.symm h)
    rw [← hd, e.symm_apply_apply]
    exact hp
  have : H.toSubgroup.FiniteIndex := by
    have : Finite (G ⧸ H.toSubgroup) :=
      Finite.of_equiv (MulAction.orbit G (FiniteEtale.liftedFiberPoint A xi))
        (MulAction.orbitEquivQuotientStabilizer G (FiniteEtale.liftedFiberPoint A xi))
    exact Subgroup.finiteIndex_of_finite_quotient
  let ψ := finiteCoefficientTransfer H φ
  obtain ⟨b, hb⟩ := h1Character_surjective (X := S) B (xi ≫ A.hom) ψ
  refine ⟨b, ?_⟩
  apply h1Character_injective B xi
  apply ContinuousMonoidHom.ext
  intro a
  have hn := congrArg
    (fun ρ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B => ρ a)
    (h1Character_schemePullback (X := A.left) (Y := S) A.hom B xi b)
  calc
    h1Character B xi (constantCohomologyPullback A.hom B 1 b) a =
        h1Character (X := S) B (xi ≫ A.hom) b
          (FiniteEtale.fundamentalGroupHom A.hom xi a) := hn.symm
    _ = ψ (FiniteEtale.fundamentalGroupHom A.hom xi a) :=
      congrArg (fun ρ => ρ (FiniteEtale.fundamentalGroupHom A.hom xi a)) hb
    _ = ψ (e a : G) := congrArg ψ
      (FiniteEtale.fundamentalGroupEquivStabilizerOfLift_coe A xi a).symm
    _ = φ (e a) := finiteCoefficientTransfer_subtype H hcop φ hφ (e a)
    _ = h1Character B xi c a := congrArg χ (e.symm_apply_apply a)

include xi in
/-- Pullback of a base class is fixed by every actual geometric deck
transformation. This follows from the constructed conjugation comparison. -/
theorem constantH1Pullback_deck_of_base
    (b : Sheaf.H.{u} ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj B) 1)
    (σ : Aut A) :
    constantCohomologyPullback σ.hom.left B 1
      (constantCohomologyPullback A.hom B 1 b) =
      constantCohomologyPullback A.hom B 1 b := by
  let : TopologicalSpace (Multiplicative B) := ⊥
  let G := Aut (FiniteEtale.fiber (xi ≫ A.hom))
  obtain ⟨g, hg⟩ := galoisObjectQuotientMonoidHom_surjective
    (C := FiniteEtale S) (FiniteEtale.fiber (xi ≫ A.hom)) G A
    (FiniteEtale.liftedFiberPoint A xi) (MulOpposite.op σ)
  have hσ : (FiniteEtale.fiber (xi ≫ A.hom)).map σ.hom
      (FiniteEtale.liftedFiberPoint A xi) =
      g • FiniteEtale.liftedFiberPoint A xi := by
    have he := galoisObjectQuotientMonoidHom_evaluation
      (C := FiniteEtale S) (FiniteEtale.fiber (xi ≫ A.hom)) G A
      (FiniteEtale.liftedFiberPoint A xi) g
    rw [hg] at he
    exact he
  let t := FiniteEtale.deckPointedGeometricFiberIso A xi σ g hσ
  let d := autHomOfCompIso (FiniteEtale.pullback σ.hom.left) t
  let c := constantCohomologyPullback A.hom B 1 b
  let χ := h1Character (X := S) B (xi ≫ A.hom) b
  have hb (a : Aut (FiniteEtale.fiber xi)) :
      χ (FiniteEtale.fundamentalGroupHom A.hom xi a) =
        h1Character B xi c a :=
    congrArg (fun ρ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B => ρ a)
      (h1Character_schemePullback (X := A.left) (Y := S) A.hom B xi b)
  apply h1Character_injective B xi
  apply ContinuousMonoidHom.ext
  intro a
  have hd := FiniteEtale.fundamentalGroupHom_deckPointed A xi σ g hσ a
  have hp := congrArg
    (fun ρ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B => ρ a)
    (h1Character_pointedSchemePullback σ.hom.left B xi xi t c)
  calc
    h1Character B xi (constantCohomologyPullback σ.hom.left B 1 c) a =
        h1Character B xi c (d a) := hp.symm
    _ = χ (FiniteEtale.fundamentalGroupHom A.hom xi (d a)) := (hb (d a)).symm
    _ = χ (g⁻¹ * FiniteEtale.fundamentalGroupHom A.hom xi a * g) :=
      congrArg χ hd
    _ = χ (FiniteEtale.fundamentalGroupHom A.hom xi a) := by
      rw [map_mul, map_mul, map_inv, mul_comm (χ g)⁻¹, mul_assoc, inv_mul_cancel,
        mul_one]
    _ = h1Character B xi c a := hb a

/-- The image of actual H¹ pullback is exactly the classes fixed by actual deck
pullbacks, for coefficient order coprime to the Galois covering index. -/
theorem mem_range_constantH1Pullback_iff_deckInvariant
    (hcop : (Nat.card (Multiplicative B)).Coprime
      (pointedCoverOpenSubgroup A xi).toSubgroup.index)
    (c : Sheaf.H.{u} ((constantSheaf A.left.smallEtaleTopology AddCommGrpCat.{u}).obj B) 1) :
    c ∈ Set.range (constantCohomologyPullback A.hom B 1) ↔
      ∀ σ : Aut A, constantCohomologyPullback σ.hom.left B 1 c = c := by
  constructor
  · rintro ⟨b, rfl⟩ σ
    exact constantH1Pullback_deck_of_base A xi B b σ
  · exact exists_constantH1Pullback_eq_of_deckInvariant A xi B hcop c

end EtaleFundamentalGroups.Cohomology
