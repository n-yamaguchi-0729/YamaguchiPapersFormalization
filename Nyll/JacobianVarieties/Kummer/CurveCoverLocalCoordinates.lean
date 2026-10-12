/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCover
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_root_fromNormalization_kummer_existsUnique_lift
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Actual affine root coordinates on the normalized Kummer cover

Every point of the original curve has an affine neighborhood on which the
actual normalized cover represents roots of a unit. Its distinguished section
is compared with the literal root of the original generic Kummer algebra.
This retained comparison is necessary to identify the previously constructed
root-scaling automorphisms on geometric fibers.

The local sections are supplied by the existing Kummer normalization theorem,
whose Anthropic FLT attribution is retained in its original source file.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace AlgebraicCurve.CurveModel

open AlgebraicCurves.Geometry.Schemes.Proofs
open exists_root_fromNormalization_kummer_existsUnique_lift.KummerLift in
/-- A local unit Kummer equation on any normal integral scheme has an actual
root coordinate on its normalization, with the root-lifting universal property. -/
theorem exists_affine_root_coordinate
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of R)) (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : R)) (g h : X.functionField) (hg : g ≠ 0) (hh : h ≠ 0)
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (hdiv : ∀ x ∈ V, g / h ^ (n : ℕ) ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h ^ (n : ℕ) / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    let A := AdjoinRoot (Polynomial.X ^ (n : ℕ) - Polynomial.C g : Polynomial X.functionField)
    let f := Spec.map (CommRingCat.ofHom (algebraMap X.functionField A)) ≫
      X.fromSpecStalk (genericPoint X)
    ∃ (v : Γ(X, V)), IsUnit v ∧ ∃ T : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V),
      T ^ (n : ℕ) = f.fromNormalization.app V v ∧
      f.toNormalization.app (f.fromNormalization ⁻¹ᵁ V) T =
        (Spec (.of A)).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (.of A)).inv
            (algebraMap X.functionField A h⁻¹ * AdjoinRoot.root _)) ∧
      ∀ (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ V = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ (n : ℕ) = z.app V v →
          ∃! s : Z ⟶ f.normalization, s ≫ f.fromNormalization = z ∧
            s.app (f.fromNormalization ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ := by
  intro A f
  have hvex := exists_hasValue (X := X) V (g / h ^ (n : ℕ))
    (fun x hx => (hdiv x hx).1)
  let v : Γ(X, V) := Classical.choose hvex
  have hv : HasValue V v (g / h ^ (n : ℕ)) := Classical.choose_spec hvex
  have hvunit : IsUnit v := hv.isUnit (div_ne_zero hg (pow_ne_zero _ hh))
    (fun x hx => by rw [inv_div]; exact (hdiv x hx).2)
  have hTex := exists_hasYVal_root (X := X) (k := (n : ℕ)) (g := g)
    n.ne_zero V h v hv
  let T : Γ((fK (n : ℕ) g).normalization,
      (fK (n : ℕ) g).fromNormalization ⁻¹ᵁ V) :=
    Classical.choose hTex
  have hTval : HasYVal (n : ℕ) g V T
      (algebraMap X.functionField A h⁻¹ * AdjoinRoot.root _) := Classical.choose_spec hTex
  have hTpow : T ^ (n : ℕ) = (fK (n : ℕ) g).fromNormalization.app V v := by
    apply (hTval.pow (n : ℕ)).eq
    rw [root_div_pow]
    exact hasYVal_app hv
  have hTself : yval (n : ℕ) g V hV T =
      algebraMap X.functionField A h⁻¹ * AdjoinRoot.root _ := by
    simpa only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      CommRingCat.id_apply] using hTval V hV inferInstance le_rfl
  have hT := toNormalization_app_eq (X := X) (n : ℕ) g V hV T _ hTself
  have hnv : IsUnit ((n : ℕ) : Γ(X, V)) := by
    have hmap := hn.map (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom)
    simpa only [map_natCast] using hmap
  refine ⟨v, hvunit, T, hTpow, hT, ?_⟩
  exact existsUnique_lift_fromNormalization_kummer_of_isAffineOpen (X := X) hnorm
    (n : ℕ) g V hV inferInstance hnv v hvunit h hh hv T hT

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)

/-- Around each actual point, the normalized Kummer cover represents roots of
an actual unit, and its distinguished section is the original generic root
divided by the explicitly supplied local rational factor. -/
theorem exists_kummer_root_chart (hn : IsUnit ((n : ℕ) : K)) (x : M.C) :
    let f := M.kummerGenericMap n u
    let N := f.normalization
    let π := f.fromNormalization
    let A := AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField)
    ∃ (V : M.C.Opens) (_hV : IsAffineOpen V), x ∈ V ∧
      ∃ (h : M.C.functionField) (_hh : h ≠ 0) (v : Γ(M.C, V)), IsUnit v ∧
        ∃ T : Γ(N, π ⁻¹ᵁ V),
          T ^ (n : ℕ) = π.app V v ∧
          f.toNormalization.app (π ⁻¹ᵁ V) T =
            (Spec (.of A)).presheaf.map (homOfLE le_top).op
              ((Scheme.ΓSpecIso (.of A)).inv
                (algebraMap M.C.functionField A h⁻¹ * AdjoinRoot.root _)) ∧
          ∀ (Z : Scheme.{u}) (z : Z ⟶ M.C), z ⁻¹ᵁ V = ⊤ →
            ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ (n : ℕ) = z.app V v →
              ∃! s : Z ⟶ N, s ≫ π = z ∧
                s.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ := by
  intro f N π A
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have hnorm : ∀ y : M.C, IsIntegrallyClosed (M.C.presheaf.stalk y) :=
    fun y => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase y).2
  obtain ⟨r, U, h, hU, hh, hdiv⟩ := M.exists_kummer_unit_cover n u
  have hx : x ∈ (⨆ i, U i) := hU.symm ▸ Set.mem_univ x
  have haex : ∃ a, x ∈ U a := Opens.mem_iSup.mp hx
  let a : Fin r := Classical.choose haex
  have hxa : x ∈ U a := Classical.choose_spec haex
  have hVex : ∃ V : M.C.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U a := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      M.C.isBasis_affineOpens.exists_subset_of_mem_open hxa (U a).isOpen
    exact ⟨V, hV, hxV, hVU⟩
  let V : M.C.Opens := Classical.choose hVex
  have hV : IsAffineOpen V := (Classical.choose_spec hVex).1
  have hxV : x ∈ V := (Classical.choose_spec hVex).2.1
  have hVU : V ≤ U a := (Classical.choose_spec hVex).2.2
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨V, hV, hxV, h a, hh a, ?_⟩
  exact exists_affine_root_coordinate (R := K) (X := M.C) M.toBase hnorm n hn
    (M.ffEquiv (u.val : F))
    (h a) ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)) (hh a) V hV
    (fun y hy => hdiv a y (hVU hy))

end AlgebraicCurve.CurveModel
