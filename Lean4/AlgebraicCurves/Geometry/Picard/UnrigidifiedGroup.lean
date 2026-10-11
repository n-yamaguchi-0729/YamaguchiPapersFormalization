/- 
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The quotient group construction follows the existing adapted Picard group:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicGroup.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the unrigidified construction: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import AlgebraicCurves.Geometry.Picard.UnrigidifiedAlgEquivZero
import AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_tensor_inverse
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.Quot

/-!
# The commutative group of unrigidified Picard-zero classes

Tensor product and actual tensor inverses give the group structure without a
section. Pullback is a group homomorphism.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.RelPicard.Unrigidified

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}

/-- Tensor product of actual invertible modules. -/
def tensorBundle {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M N : LineBundle c t) : LineBundle c t :=
  ⟨M.1 ⊗ N.1, M.2.tensor N.2⟩

theorem baseTwist_tensor_right {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : LineBundle c t) {N N' : LineBundle c t} (h : BaseTwist c t N N') :
    BaseTwist c t (tensorBundle M N) (tensorBundle M N') := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := h
  exact ⟨Q, hQ, ⟨(Iso.refl M.1 ⊗ᵢ e) ≪≫ (α_ _ _ _).symm ≪≫
    ((β_ _ _) ⊗ᵢ Iso.refl N.1) ≪≫ α_ _ _ _⟩⟩

theorem baseTwist_tensor_left {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (N : LineBundle c t) {M M' : LineBundle c t} (h : BaseTwist c t M M') :
    BaseTwist c t (tensorBundle M N) (tensorBundle M' N) := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := h
  exact ⟨Q, hQ, ⟨(e ⊗ᵢ Iso.refl N.1) ≪≫ α_ _ _ _⟩⟩

/-- Tensor product descends to relative line-bundle classes. -/
def classesMul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Classes c t → Classes c t → Classes c t :=
  Quot.map₂ tensorBundle
    (fun M _ _ h => baseTwist_tensor_right M h)
    (fun _ _ N h => baseTwist_tensor_left N h)

theorem fibrewiseZero_tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M N : LineBundle c t} (hM : FibrewiseZero M) (hN : FibrewiseZero N) :
    FibrewiseZero (tensorBundle M N) := by
  intro k _ _ s
  exact ((hM k s).tensor (hN k s)).of_iso (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

/-- Tensor product on fibrewise algebraically trivial classes. -/
def zeroMul (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ)
    (x y : (zeroPresheaf c).obj X) : (zeroPresheaf c).obj X :=
  ⟨classesMul X.unop.hom x.1 y.1, by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    induction x using Quot.ind with
    | _ M =>
      induction y using Quot.ind with
      | _ N => exact fibrewiseZero_tensor hx hy⟩

/-- The structure sheaf defines the identity class. -/
def zeroOne (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ) : (zeroPresheaf c).obj X :=
  ⟨Quot.mk _ ⟨𝟙_ (pullback c X.unop.hom).Modules,
      Scheme.Modules.isInvertible_unit (pullback c X.unop.hom)⟩,
    by
      intro k _ _ s
      refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
        𝟙_ (pullback (fibreAt c X.unop.hom s) (𝟙 (Spec (CommRingCat.of k)))).Modules,
        Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩,
        ⟨𝟙 _, Category.comp_id _⟩, ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
      exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackUnitIso _).symm⟩

/-- An actual tensor inverse of an invertible module. -/
def inverseBundle {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : LineBundle c t) : LineBundle c t :=
  ⟨M.2.exists_tensor_inverse.choose, M.2.exists_tensor_inverse.choose_spec.1⟩

theorem inverseBundle_iso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : LineBundle c t) : Nonempty (M.1 ⊗ (inverseBundle M).1 ≅ 𝟙_ _) :=
  M.2.exists_tensor_inverse.choose_spec.2

theorem fibrewiseZero_inverse {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M : LineBundle c t} (hM : FibrewiseZero M) : FibrewiseZero (inverseBundle M) := by
  intro k _ _ s
  exact (hM k s).of_tensor_iso_unit
    ((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (inverseBundle_iso M).some ≪≫
      Scheme.Modules.pullbackUnitIso _)

/-- A tensor inverse defines the inverse relative class. -/
def zeroInv (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ)
    (x : (zeroPresheaf c).obj X) : (zeroPresheaf c).obj X :=
  ⟨Quot.mk _ (inverseBundle (Quot.out x.1)), fibrewiseZero_inverse (by
    have hx := x.2
    rw [← Quot.out_eq x.1] at hx
    exact hx)⟩

/-- The commutative group structure supplied by tensor products and tensor inverses. -/
@[reducible]
def zeroCommGroup (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    CommGroup ((zeroPresheaf c).obj X) where
  mul := zeroMul X
  one := zeroOne X
  inv := zeroInv X
  mul_assoc := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    apply Subtype.ext
    induction x using Quot.ind
    induction y using Quot.ind
    induction z using Quot.ind
    exact Quot.sound (baseTwist_of_iso (α_ _ _ _))
  one_mul := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    induction x using Quot.ind
    exact Quot.sound (baseTwist_of_iso (λ_ _))
  mul_one := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    induction x using Quot.ind
    exact Quot.sound (baseTwist_of_iso (ρ_ _))
  mul_comm := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    induction x using Quot.ind
    induction y using Quot.ind
    exact Quot.sound (baseTwist_of_iso (β_ _ _))
  inv_mul_cancel := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    change classesMul X.unop.hom (Quot.mk _ (inverseBundle (Quot.out x))) x = _
    have h : classesMul X.unop.hom (Quot.mk _ (inverseBundle (Quot.out x)))
        (Quot.mk _ (Quot.out x)) =
        Quot.mk _ ⟨𝟙_ (pullback c X.unop.hom).Modules,
          Scheme.Modules.isInvertible_unit _⟩ :=
      Quot.sound (baseTwist_of_iso
        (β_ (inverseBundle (Quot.out x)).1 (Quot.out x).1 ≪≫
          (inverseBundle_iso (Quot.out x)).some))
    exact (congrArg (classesMul X.unop.hom (Quot.mk _ (inverseBundle (Quot.out x))))
      (Quot.out_eq x)).symm.trans h

/-- The actual commutative-group-valued unrigidified Picard-zero presheaf. -/
def zeroCommGrpPresheaf (c : C ⟶ Spec (CommRingCat.of R)) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj X := @CommGrpCat.of ((zeroPresheaf c).obj X) (zeroCommGroup X)
  map {X Y} φ :=
    let _ : CommGroup ((zeroPresheaf c).obj X) := zeroCommGroup X
    let _ : CommGroup ((zeroPresheaf c).obj Y) := zeroCommGroup Y
    CommGrpCat.ofHom
      { toFun := (zeroPresheaf c).map φ
        map_one' := by
          apply Subtype.ext
          exact Quot.sound (baseTwist_of_iso (Scheme.Modules.pullbackUnitIso _))
        map_mul' := by
          rintro ⟨x, hx⟩ ⟨y, hy⟩
          apply Subtype.ext
          induction x using Quot.ind
          induction y using Quot.ind
          exact Quot.sound (baseTwist_of_iso (Scheme.Modules.pullbackTensorObjIso _ _ _)) }
  map_id X := by
    let _ : CommGroup ((zeroPresheaf c).obj X) := zeroCommGroup X
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact ConcreteCategory.congr_hom ((zeroPresheaf c).map_id X) x
  map_comp {X Y Z} φ ψ := by
    let _ : CommGroup ((zeroPresheaf c).obj X) := zeroCommGroup X
    let _ : CommGroup ((zeroPresheaf c).obj Y) := zeroCommGroup Y
    let _ : CommGroup ((zeroPresheaf c).obj Z) := zeroCommGroup Z
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact ConcreteCategory.congr_hom ((zeroPresheaf c).map_comp φ ψ) x

end AlgebraicGeometry.RelPicard.Unrigidified
