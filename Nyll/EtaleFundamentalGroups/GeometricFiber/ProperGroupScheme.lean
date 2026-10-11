/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.MultiplicationMorphisms
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperKunneth
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The fundamental group of a proper smooth group scheme

The actual multiplication morphism, the two unit embeddings and the proper
Künneth comparison identify its induced map with group multiplication.
Consequently the fundamental group is commutative. Multiplication by an
integer induces the corresponding power map, with the unit basepoint fixed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

variable {K : Type u} [Field K] [IsSepClosed K]
  {A : Scheme.{u}} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] [GeometricallyConnected f]

private theorem multiplication_data (G : RelativeGroupLaw K f) :
    let e := (G.one (𝟙 (Spec (.of K)))).1
    let z := pullback.lift e e (rfl : e ≫ f = e ≫ f)
    let P := pointedFundamentalGroupHom (pullback.fst f f) z e
      (pullback.lift_fst _ _ _)
    let Q := pointedFundamentalGroupHom (pullback.snd f f) z e
      (pullback.lift_snd _ _ _)
    let M := pointedFundamentalGroupHom (G.mulRight f idPoint) z e
      G.unitPoint_comp_mulRight_idPoint
    (∀ a, M a = P a * Q a) ∧ (∀ a b : π₁ᵉᵗ(e), a * b = b * a) := by
  intro e z P Q M
  have he : e ≫ f = 𝟙 _ := (G.one (𝟙 (Spec (.of K)))).2
  have hA : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  have hN : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  have hz₁ : z ≫ pullback.fst f f = e := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd f f = e := pullback.lift_snd _ _ _
  let i : A ⟶ pullback f f := pullback.lift (𝟙 A) (f ≫ e)
    (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  let j : A ⟶ pullback f f := pullback.lift (f ≫ e) (𝟙 A)
    (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have hi₁ : i ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have hi₂ : i ≫ pullback.snd f f = f ≫ e := pullback.lift_snd _ _ _
  have hj₁ : j ≫ pullback.fst f f = f ≫ e := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd f f = 𝟙 A := pullback.lift_snd _ _ _
  have hei : e ≫ i = z := by
    apply pullback.hom_ext
    · rw [Category.assoc, hi₁, Category.comp_id, hz₁]
    · rw [Category.assoc, hi₂, ← Category.assoc, he, Category.id_comp, hz₂]
  have hej : e ≫ j = z := by
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, ← Category.assoc, he, Category.id_comp, hz₁]
    · rw [Category.assoc, hj₂, Category.comp_id, hz₂]
  let I := pointedFundamentalGroupHom i e z hei
  let J := pointedFundamentalGroupHom j e z hej
  have hPI : P.comp I = ContinuousMonoidHom.id π₁ᵉᵗ(e) := by
    dsimp only [P, I]
    rw [pointedFundamentalGroupHom_comp]
    simpa only [hi₁] using pointedFundamentalGroupHom_id e
  have hQI : Q.comp I = 1 := by
    dsimp only [Q, I]
    rw [pointedFundamentalGroupHom_comp]
    simpa only [hi₂] using
      pointedFundamentalGroupHom_constant f e e e
        (by rw [← Category.assoc, he, Category.id_comp])
  have hPJ : P.comp J = 1 := by
    dsimp only [P, J]
    rw [pointedFundamentalGroupHom_comp]
    simpa only [hj₁] using
      pointedFundamentalGroupHom_constant f e e e
        (by rw [← Category.assoc, he, Category.id_comp])
  have hQJ : Q.comp J = ContinuousMonoidHom.id π₁ᵉᵗ(e) := by
    dsimp only [Q, J]
    rw [pointedFundamentalGroupHom_comp]
    simpa only [hj₂] using pointedFundamentalGroupHom_id e
  have hMI : M.comp I = ContinuousMonoidHom.id π₁ᵉᵗ(e) := by
    have hm : i ≫ G.mulRight f idPoint = 𝟙 A := G.rightUnit_comp_mulRight_idPoint
    dsimp only [M, I]
    rw [pointedFundamentalGroupHom_comp]
    simpa only [hm] using pointedFundamentalGroupHom_id e
  have hMJ : M.comp J = ContinuousMonoidHom.id π₁ᵉᵗ(e) := by
    have hm : j ≫ G.mulRight f idPoint = 𝟙 A := G.leftUnit_comp_mulRight_idPoint
    dsimp only [M, J]
    rw [pointedFundamentalGroupHom_comp]
    simpa only [hm] using pointedFundamentalGroupHom_id e
  have hpair : Function.Injective (P.prod Q) := by
    have hn := (fundamentalGroupHom_proper_product_bijective f f z
      (by rw [hz₂, he])).1
    intro a b hab
    apply hn
    apply Prod.ext
    · change fundamentalGroupHom (pullback.fst f f) z a =
        fundamentalGroupHom (pullback.fst f f) z b
      apply (eq_rec_on_bijective
        (C := fun eta : Spec (.of K) ⟶ A => π₁ᵉᵗ(eta)) hz₁).injective
      have h : P a = P b := congrArg Prod.fst hab
      simpa only [P, pointedFundamentalGroupHom_apply] using h
    · change fundamentalGroupHom (pullback.snd f f) z a =
        fundamentalGroupHom (pullback.snd f f) z b
      apply (eq_rec_on_bijective
        (C := fun eta : Spec (.of K) ⟶ A => π₁ᵉᵗ(eta)) hz₂).injective
      have h : Q a = Q b := congrArg Prod.snd hab
      simpa only [Q, pointedFundamentalGroupHom_apply] using h
  have hpi (a) : P (I a) = a := DFunLike.congr_fun hPI a
  have hqi (a) : Q (I a) = 1 := DFunLike.congr_fun hQI a
  have hpj (a) : P (J a) = 1 := DFunLike.congr_fun hPJ a
  have hqj (a) : Q (J a) = a := DFunLike.congr_fun hQJ a
  have hmi (a) : M (I a) = a := DFunLike.congr_fun hMI a
  have hmj (a) : M (J a) = a := DFunLike.congr_fun hMJ a
  have hdecomp (a : π₁ᵉᵗ(z)) : I (P a) * J (Q a) = a := by
    apply hpair
    apply Prod.ext
    · change P (I (P a) * J (Q a)) = P a
      rw [map_mul, hpi, hpj, _root_.mul_one]
    · change Q (I (P a) * J (Q a)) = Q a
      rw [map_mul, hqi, hqj, _root_.one_mul]
  constructor
  · intro a
    calc
      M a = M (I (P a) * J (Q a)) := congrArg M (hdecomp a).symm
      _ = P a * Q a := by rw [map_mul, hmi, hmj]
  · intro a b
    have hab : I a * J b = J b * I a := by
      apply hpair
      apply Prod.ext
      · change P (I a * J b) = P (J b * I a)
        rw [map_mul, map_mul, hpi, hpj, _root_.mul_one, _root_.one_mul]
      · change Q (I a * J b) = Q (J b * I a)
        rw [map_mul, map_mul, hqi, hqj, _root_.mul_one, _root_.one_mul]
    calc
      a * b = M (I a * J b) := by rw [map_mul, hmi, hmj]
      _ = M (J b * I a) := congrArg M hab
      _ = b * a := by rw [map_mul, hmj, hmi]

/-- The actual fundamental group at the unit of a proper smooth geometrically
connected group scheme over a separably closed field is commutative. -/
theorem fundamentalGroup_mul_comm (G : RelativeGroupLaw K f)
    (a b : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) : a * b = b * a :=
  (multiplication_data G).2 a b

/-- The actual pointed fundamental-group map of multiplication by `n` is
the `n`th power map at the unit basepoint. -/
theorem pointedFundamentalGroupHom_schemeNsmul (G : RelativeGroupLaw K f) (n : ℕ)
    (a : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    pointedFundamentalGroupHom (G.schemeNsmul n)
      (G.one (𝟙 (Spec (.of K)))).1 (G.one (𝟙 (Spec (.of K)))).1
      (G.unit_comp_schemeNsmul n) a = a ^ n := by
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 (Spec (.of K)))).1
  have he : e ≫ f = 𝟙 _ := (G.one (𝟙 (Spec (.of K)))).2
  have hA : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let z : Spec (.of K) ⟶ pullback f f := pullback.lift e e rfl
  have hz₁ : z ≫ pullback.fst f f = e := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd f f = e := pullback.lift_snd _ _ _
  let P := pointedFundamentalGroupHom (pullback.fst f f) z e hz₁
  let Q := pointedFundamentalGroupHom (pullback.snd f f) z e hz₂
  let M := pointedFundamentalGroupHom (G.mulRight f idPoint) z e
    G.unitPoint_comp_mulRight_idPoint
  have hM (b : π₁ᵉᵗ(z)) : M b = P b * Q b := (multiplication_data G).1 b
  change pointedFundamentalGroupHom (G.schemeNsmul n) e e (G.unit_comp_schemeNsmul n) a = a ^ n
  induction n with
  | zero =>
    have hzero : G.schemeNsmul 0 = f ≫ e := by
      change (G.nsmul f 0 idPoint).1 = f ≫ e
      rw [G.nsmul_zero]
      exact (congrArg Subtype.val
        (G.one_natural (𝟙 (Spec (.of K))) f f (Category.comp_id f))).symm
    have hconst : pointedFundamentalGroupHom (G.schemeNsmul 0) e e
        (G.unit_comp_schemeNsmul 0) = 1 := by
      simpa only [hzero] using pointedFundamentalGroupHom_constant f e e e
        (by rw [← Category.assoc, he, Category.id_comp])
    rw [hconst]
    exact (pow_zero a).symm
  | succ n ih =>
    let t : A ⟶ pullback f f := pullback.lift (G.schemeNsmul n) (𝟙 A)
      ((G.schemeNsmul_over n).trans (Category.id_comp f).symm)
    have ht₁ : t ≫ pullback.fst f f = G.schemeNsmul n := pullback.lift_fst _ _ _
    have ht₂ : t ≫ pullback.snd f f = 𝟙 A := pullback.lift_snd _ _ _
    have het : e ≫ t = z := by
      apply pullback.hom_ext
      · rw [Category.assoc, ht₁, G.unit_comp_schemeNsmul, hz₁]
      · rw [Category.assoc, ht₂, Category.comp_id, hz₂]
    let T := pointedFundamentalGroupHom t e z het
    have htm : t ≫ G.mulRight f idPoint = G.schemeNsmul (n + 1) :=
      G.schemeNsmul_pair_id_comp_mulRight n
    have hMT : M.comp T = pointedFundamentalGroupHom (G.schemeNsmul (n + 1)) e e
        (G.unit_comp_schemeNsmul (n + 1)) := by
      have h := pointedFundamentalGroupHom_comp t (G.mulRight f idPoint) e z e het
        G.unitPoint_comp_mulRight_idPoint
      simpa only [htm] using h
    have hPT : P.comp T = pointedFundamentalGroupHom (G.schemeNsmul n) e e
        (G.unit_comp_schemeNsmul n) := by
      have h := pointedFundamentalGroupHom_comp t (pullback.fst f f) e z e het hz₁
      simpa only [ht₁] using h
    have hQT : Q.comp T = ContinuousMonoidHom.id π₁ᵉᵗ(e) := by
      dsimp only [Q, T]
      rw [pointedFundamentalGroupHom_comp]
      simpa only [ht₂] using pointedFundamentalGroupHom_id e
    calc
      pointedFundamentalGroupHom (G.schemeNsmul (n + 1)) e e
          (G.unit_comp_schemeNsmul (n + 1)) a = M (T a) :=
        (DFunLike.congr_fun hMT a).symm
      _ = P (T a) * Q (T a) := hM (T a)
      _ = a ^ n * a := by
        have hp : P (T a) = pointedFundamentalGroupHom (G.schemeNsmul n) e e
            (G.unit_comp_schemeNsmul n) a := DFunLike.congr_fun hPT a
        have hq : Q (T a) = a := DFunLike.congr_fun hQT a
        rw [hp, hq, ih]
      _ = a ^ (n + 1) := (pow_succ a n).symm

end GoodReductionJacobian.RelativeGroupLaw
