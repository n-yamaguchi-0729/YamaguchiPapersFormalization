/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverAction
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_root_fromNormalization_kummer_existsUnique_lift
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Nyll.AlgebraicCurves.Places.Exists_place_range_stalk_eq

/-!
# Local root coordinates for the actual Kummer action

The automorphisms of the actual normalized Kummer cover act on its local
root coordinate by multiplication with the root of unity pulled back from the
base field. Equality of sections is proved using the schematic dominance of
the original generic algebra in its normalization. No connectedness assumption
on the cover or irreducibility assumption on the root algebra is used.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open JacobianVarieties.Kummer

namespace AlgebraicCurve.CurveModel

private theorem appLE_commutation {S N : Scheme.{u}}
    (f : S ⟶ N) (eS : S ⟶ S) (eN : N ⟶ N) (hc : f ≫ eN = eS ≫ f)
    (W : N.Opens) (hW : W ≤ eN ⁻¹ᵁ W) (hf : ⊤ ≤ f ⁻¹ᵁ W) :
    eN.appLE W W hW ≫ f.appLE W ⊤ hf =
      f.appLE W ⊤ hf ≫ eS.appTop := by
  have heS : eS.appTop = eS.appLE ⊤ ⊤ le_top := eS.app_eq_appLE
  have hleft := Scheme.Hom.appLE_comp_appLE f eN W W ⊤ hW hf
  have hright := Scheme.Hom.appLE_comp_appLE eS f W ⊤ ⊤ hf le_top
  have hmid {g g' : S ⟶ N} (hgg : g = g')
      (hg : ⊤ ≤ g ⁻¹ᵁ W) (hg' : ⊤ ≤ g' ⁻¹ᵁ W) :
      g.appLE W ⊤ hg = g'.appLE W ⊤ hg' := by
    subst g'
    rfl
  rw [heS]
  exact hleft.trans ((hmid hc _ _).trans hright.symm)

private theorem appLE_injective_of_preimage_top {S N : Scheme.{u}} (f : S ⟶ N)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (W : N.Opens) (hf : f ⁻¹ᵁ W = ⊤) :
    Function.Injective (f.appLE W ⊤ hf.ge) := by
  have h := f.app_injective W
  rw [f.app_eq_appLE] at h
  exact (f.appLE_congr le_rfl rfl hf (fun q => Function.Injective q)).mp h

private theorem appLE_of_app {S N : Scheme.{u}} (f : S ⟶ N)
    (W : N.Opens) (hf : f ⁻¹ᵁ W = ⊤) (s : Γ(N, W)) (t : Γ(S, ⊤))
    (hs : f.app W s = S.presheaf.map (homOfLE le_top).op t) :
    f.appLE W ⊤ hf.ge s = t := by
  change S.presheaf.map (homOfLE hf.ge).op (f.app W s) = t
  rw [hs, ← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  have hcomp : (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)).op ≫ (homOfLE hf.ge).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  rw [hcomp, CategoryTheory.Functor.map_id, CommRingCat.id_apply]

private theorem section_map_eq_of_generic {S N : Scheme.{u}}
    (f : S ⟶ N) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (eS : S ⟶ S) (eN : N ⟶ N) (hc : f ≫ eN = eS ≫ f)
    (W : N.Opens) (hW : W ≤ eN ⁻¹ᵁ W) (hf : f ⁻¹ᵁ W = ⊤)
    (s t : Γ(N, W)) (ρ : Γ(S, ⊤))
    (hs : f.appLE W ⊤ hf.ge s = ρ)
    (ht : f.appLE W ⊤ hf.ge t = eS.appTop ρ) :
    eN.appLE W W hW s = t := by
  apply appLE_injective_of_preimage_top f W hf
  have happ := ConcreteCategory.congr_hom (appLE_commutation f eS eN hc W hW hf.ge) s
  change f.appLE W ⊤ hf.ge (eN.appLE W W hW s) = eS.appTop (f.appLE W ⊤ hf.ge s) at happ
  exact happ.trans ((congrArg eS.appTop hs).trans ht.symm)

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)

open AlgebraicCurves.Geometry.Schemes.Proofs
open exists_root_fromNormalization_kummer_existsUnique_lift.KummerLift in
private theorem hasValue_baseScalar (V : M.C.Opens) (a : K) :
    HasValue V
      (M.toBase.appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv a))
      (baseToFunctionField M.toBase a) := by
  intro x hx
  rw [baseToFunctionField_apply_eq_algebraMap_stalk M.toBase x a]
  change algebraMap (M.C.presheaf.stalk x) M.C.functionField
    (M.C.presheaf.germ V x hx
      (M.C.presheaf.map (homOfLE le_top).op
        (M.toBase.appTop ((Scheme.ΓSpecIso (.of K)).inv a)))) = _
  rw [TopCat.Presheaf.germ_res_apply]

private theorem genericRootScale_appTop (ζ : rootsOfUnity (n : ℕ) K)
    (a : AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField)) :
    (Scheme.ΓSpecIso _).hom
      ((M.kummerGenericRootScale n u ζ).hom.appTop ((Scheme.ΓSpecIso _).inv a)) =
        kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F))
          (restrictRootsOfUnity (baseToFunctionField M.toBase) (n : ℕ) ζ) a := by
  let e := kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F))
    (restrictRootsOfUnity (baseToFunctionField M.toBase) (n : ℕ) ζ)
  change (Scheme.ΓSpecIso _).hom
    ((Spec.map (CommRingCat.ofHom e.toRingHom)).appTop ((Scheme.ΓSpecIso _).inv a)) = e a
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e.toRingHom)) a
  change (Scheme.ΓSpecIso _).inv (e a) =
    (Spec.map (CommRingCat.ofHom e.toRingHom)).appTop ((Scheme.ΓSpecIso _).inv a) at h
  rw [← h, Iso.inv_hom_id_apply]

private theorem genericRootScale_rootSection (ζ : rootsOfUnity (n : ℕ) K)
    (h : M.C.functionField) :
    let A := AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField)
    (M.kummerGenericRootScale n u ζ).hom.appTop
        ((Scheme.ΓSpecIso (.of A)).inv
          (algebraMap M.C.functionField A h⁻¹ * AdjoinRoot.root _)) =
      (Scheme.ΓSpecIso (.of A)).inv
        (algebraMap M.C.functionField A (baseToFunctionField M.toBase ((ζ : Kˣ) : K)) *
          (algebraMap M.C.functionField A h⁻¹ * AdjoinRoot.root _)) := by
  intro A
  apply (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (.of A)).hom
      ((M.kummerGenericRootScale n u ζ).hom.appTop
        ((Scheme.ΓSpecIso (.of A)).inv
          (algebraMap M.C.functionField A h⁻¹ * AdjoinRoot.root _))) =
    (Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv
      (algebraMap M.C.functionField A (baseToFunctionField M.toBase ((ζ : Kˣ) : K)) *
        (algebraMap M.C.functionField A h⁻¹ * AdjoinRoot.root _)))
  rw [genericRootScale_appTop, Iso.inv_hom_id_apply, map_mul,
    AlgHom.commutes, kummerRootScale_root]
  exact (mul_left_comm _ _ _).symm

open exists_root_fromNormalization_kummer_existsUnique_lift.KummerLift in
/-- The actual root-scaling automorphism multiplies the distinguished local
root coordinate by the root of unity pulled back from the base field. -/
theorem kummerNormalizationRootScale_localRoot
    (V : M.C.Opens) [Nonempty V]
    (h : M.C.functionField)
    (T : Γ((M.kummerGenericMap n u).normalization,
      (M.kummerGenericMap n u).fromNormalization ⁻¹ᵁ V))
    (hT : (M.kummerGenericMap n u).toNormalization.app
      ((M.kummerGenericMap n u).fromNormalization ⁻¹ᵁ V) T =
        (Spec (.of (AdjoinRoot (Polynomial.X ^ (n : ℕ) -
          Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField)))).presheaf.map
          (homOfLE le_top).op ((Scheme.ΓSpecIso _).inv
            (algebraMap M.C.functionField _ h⁻¹ * AdjoinRoot.root _)))
    (ζ : rootsOfUnity (n : ℕ) K) :
    let f := M.kummerGenericMap n u
    let e := M.kummerNormalizationRootScale n u ζ
    let W := f.fromNormalization ⁻¹ᵁ V
    let hW : W ≤ e.hom ⁻¹ᵁ W := by
      change f.fromNormalization ⁻¹ᵁ V ≤ e.hom ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ V)
      have hover : e.hom ≫ f.fromNormalization = f.fromNormalization :=
        EtaleFundamentalGroups.Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _
      rw [← Scheme.Hom.comp_preimage, hover]
    e.hom.appLE W W hW T = f.fromNormalization.app V
      (M.toBase.appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv ((ζ : Kˣ) : K))) * T := by
  intro f e W hW
  let A := AdjoinRoot (Polynomial.X ^ (n : ℕ) -
    Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField)
  let c : Γ(M.C, V) :=
    M.toBase.appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv ((ζ : Kˣ) : K))
  let q : M.C.functionField := baseToFunctionField M.toBase ((ζ : Kˣ) : K)
  let ρ : A := algebraMap M.C.functionField A h⁻¹ * AdjoinRoot.root _
  have hf : f.toNormalization ⁻¹ᵁ W = ⊤ := by
    change f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ V) = ⊤
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
    exact preimage_eq_top (CommRingCat.ofHom (algebraMap M.C.functionField A)) V
  have : IsSchemeTheoreticallyDominant f.toNormalization := ⟨f.ker_toNormalization⟩
  have hs : f.toNormalization.appLE W ⊤ hf.ge T = (Scheme.ΓSpecIso (.of A)).inv ρ :=
    appLE_of_app f.toNormalization W hf T _ hT
  have hcval : HasValue V c q := hasValue_baseScalar M V ((ζ : Kˣ) : K)
  have hfV : f ⁻¹ᵁ V = ⊤ :=
    preimage_eq_top (CommRingCat.ofHom (algebraMap M.C.functionField A)) V
  have hcapp : f.app V c = (Spec (.of A)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (.of A)).inv (algebraMap M.C.functionField A q)) := by
    have happ := ConcreteCategory.congr_hom
      (app_eq (CommRingCat.ofHom (algebraMap M.C.functionField A)) V) c
    change f.app V c = (Spec (.of A)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (.of A)).inv
        (algebraMap M.C.functionField A (M.C.germToFunctionField V c))) at happ
    exact happ.trans (congrArg (fun r => (Spec (.of A)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (.of A)).inv (algebraMap M.C.functionField A r)))
        hcval.germToFunctionField_eq)
  have hcgeneric : f.appLE V ⊤ hfV.ge c =
      (Scheme.ΓSpecIso (.of A)).inv (algebraMap M.C.functionField A q) :=
    appLE_of_app f V hfV c _ hcapp
  have hcomp := Scheme.Hom.appLE_comp_appLE f.toNormalization f.fromNormalization
    V W ⊤ le_rfl hf.ge
  have hmid {g g' : Spec (.of A) ⟶ M.C} (hgg : g = g')
      (hg : ⊤ ≤ g ⁻¹ᵁ V) (hg' : ⊤ ≤ g' ⁻¹ᵁ V) :
      g.appLE V ⊤ hg = g'.appLE V ⊤ hg' := by
    subst g'
    rfl
  have hcomp' : f.fromNormalization.app V ≫ f.toNormalization.appLE W ⊤ hf.ge =
      f.appLE V ⊤ hfV.ge :=
    (congrArg (fun m => m ≫ f.toNormalization.appLE W ⊤ hf.ge)
      f.fromNormalization.app_eq_appLE).trans
      (hcomp.trans (hmid f.toNormalization_fromNormalization _ _))
  have hcf : f.toNormalization.appLE W ⊤ hf.ge (f.fromNormalization.app V c) =
      (Scheme.ΓSpecIso (.of A)).inv (algebraMap M.C.functionField A q) :=
    (ConcreteCategory.congr_hom hcomp' c).trans hcgeneric
  apply section_map_eq_of_generic f.toNormalization
    (M.kummerGenericRootScale n u ζ).hom e.hom
    (M.toNormalization_kummerNormalizationRootScale n u ζ) W hW hf T
    (f.fromNormalization.app V c * T) ((Scheme.ΓSpecIso (.of A)).inv ρ) hs
  calc
    f.toNormalization.appLE W ⊤ hf.ge (f.fromNormalization.app V c * T) =
        f.toNormalization.appLE W ⊤ hf.ge (f.fromNormalization.app V c) *
          f.toNormalization.appLE W ⊤ hf.ge T := map_mul _ _ _
    _ = (Scheme.ΓSpecIso (.of A)).inv (algebraMap M.C.functionField A q) *
        (Scheme.ΓSpecIso (.of A)).inv ρ := congrArg₂ (· * ·) hcf hs
    _ = (Scheme.ΓSpecIso (.of A)).inv (algebraMap M.C.functionField A q * ρ) :=
      (map_mul (Scheme.ΓSpecIso (.of A)).inv.hom _ _).symm
    _ = (M.kummerGenericRootScale n u ζ).hom.appTop
        ((Scheme.ΓSpecIso (.of A)).inv ρ) := (genericRootScale_rootSection M n u ζ h).symm

end AlgebraicCurve.CurveModel
