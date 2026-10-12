/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCover
import Nyll.JacobianVarieties.Kummer.CurveCoverTorsor
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverAction
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverLocalCoordinates
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverLocalAction
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootFiberTransitivity
import Mathlib.Algebra.Torsor.Defs

/-!
# The actual Kummer covering fiber is a root-of-unity torsor

Local root coordinates on the original normalization identify its geometric
fiber with nonzero roots of an actual unit. The root-scaling formula and
uniqueness of roots up to a root of unity prove that the existing action is
free and transitive. Local roots over a separably closed geometric point also
prove nonemptiness. The covering scheme may be disconnected.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace



namespace AlgebraicCurve.CurveModel.OpenKummer

open JacobianVarieties.Kummer

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  (w : Pic0.openKummerUnits K F S n)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  (hn : IsUnit ((n : ℕ) : K)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X)

private theorem exists_kummerFiberCoordinate :
    let := kummerGeometricRootAction M S n w j hj hinterior hn ξ
    ∃ q : (FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn w j hj hinterior) → Ω,
      Function.Injective q ∧ (∀ x, q x ≠ 0) ∧
      (∀ x y, q x ^ (n : ℕ) = q y ^ (n : ℕ)) ∧
      ∀ (ζ : rootsOfUnity (n : ℕ) K) x,
        q (ζ • x) = pointScalar (j ≫ M.toBase) ξ ((ζ : Kˣ) : K) * q x := by
  let := kummerGeometricRootAction M S n w j hj hinterior hn ξ
  let f := M.openKummerGenericMap S n w j hj
  let π := f.fromNormalization
  let W := M.openKummerCover S n hn w j hj hinterior
  obtain ⟨V, _hV, hxV, h, _hh, v, hv, T, hTpow, hTgen, hlift⟩ :=
    exists_kummer_root_chart M S n w j hj hinterior hn (ξ default)
  have : Nonempty V := ⟨⟨ξ default, hxV⟩⟩
  have hξ : ξ ⁻¹ᵁ V = ⊤ := point_preimage_top ξ V hxV
  let l := fiberLiftEquiv ξ W
  let c : {s : Spec (.of Ω) ⟶ f.normalization // s ≫ π = ξ} → Γ(Spec (.of Ω), ⊤) :=
    rootLiftCoordinate π V ξ hξ T
  let q : (FiniteEtale.fiber ξ).obj W → Ω :=
    fun x => (Scheme.ΓSpecIso (.of Ω)).hom (c (l x))
  have hpow (x : (FiniteEtale.fiber ξ).obj W) :
      q x ^ (n : ℕ) = (Scheme.ΓSpecIso (.of Ω)).hom (ξ.appLE V ⊤ hξ.ge v) := by
    change ((Scheme.ΓSpecIso (.of Ω)).hom (c (l x))) ^ (n : ℕ) = _
    rw [← map_pow]
    exact congrArg (Scheme.ΓSpecIso (.of Ω)).hom
      (rootLiftCoordinate_pow π V ξ hξ T (n : ℕ) v hTpow (l x))
  have hvΩ : IsUnit ((Scheme.ΓSpecIso (.of Ω)).hom (ξ.appLE V ⊤ hξ.ge v)) :=
    (hv.map (ξ.appLE V ⊤ hξ.ge).hom).map (Scheme.ΓSpecIso (.of Ω)).hom.hom
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply l.injective
    apply rootLiftCoordinate_injective π V ξ hξ T (n : ℕ) v hTpow (hlift _ ξ hξ)
    exact (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective hxy
  · intro x hx
    apply hvΩ.ne_zero
    rw [← hpow x, hx, zero_pow n.ne_zero]
  · intro x y
    exact (hpow x).trans (hpow y).symm
  · intro ζ x
    let e := kummerNormalizationRootScale M S n w j hj ζ
    have he : e.hom ≫ π = π :=
      EtaleFundamentalGroups.Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _
    have hpre : π ⁻¹ᵁ V ≤ e.hom ⁻¹ᵁ (π ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, he]
    have hscale := kummerNormalizationRootScale_localRoot M S n w j hj V h T hTgen ζ
    have hcoord := rootLiftCoordinate_comp π V ξ hξ T e.hom he hpre
      ((j ≫ M.toBase).appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv ((ζ : Kˣ) : K)))
      hscale (l x)
    have hl : l (ζ • x) =
        ⟨(l x).1 ≫ e.hom,
          (Category.assoc _ _ _).trans ((congrArg ((l x).1 ≫ ·) he).trans (l x).2)⟩ := by
      apply Subtype.ext
      exact fiberLiftEquiv_naturality ξ (kummerCoverRootScale M S n w j hj hinterior hn ζ).hom x
    change (Scheme.ΓSpecIso (.of Ω)).hom (c (l (ζ • x))) = _
    rw [hl]
    change (Scheme.ΓSpecIso (.of Ω)).hom
      (rootLiftCoordinate π V ξ hξ T _) = _
    apply (congrArg (Scheme.ΓSpecIso (.of Ω)).hom hcoord).trans
    apply (map_mul (Scheme.ΓSpecIso (.of Ω)).hom.hom _ _).trans
    exact congrArg (fun a : Γ(Spec (.of Ω), ⊤) =>
      (Scheme.ΓSpecIso (.of Ω)).hom a * q x)
      (appLE_baseScalar (j ≫ M.toBase) ξ V hξ ((Scheme.ΓSpecIso (.of K)).inv ((ζ : Kˣ) : K)))

/-- The actual normalized Kummer cover has a nonempty geometric fiber. The
proof constructs a local root over the separably closed geometric point. -/
theorem kummerGeometricFiber_nonempty :
    Nonempty ((FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn w j hj hinterior)) := by
  let f := M.openKummerGenericMap S n w j hj
  let π := f.fromNormalization
  obtain ⟨V, _hV, hxV, _h, _hh, v, _hv, T, _hTpow, _hTgen, hlift⟩ :=
    exists_kummer_root_chart M S n w j hj hinterior hn (ξ default)
  have hξ : ξ ⁻¹ᵁ V = ⊤ := point_preimage_top ξ V hxV
  let ι := pointScalar (j ≫ M.toBase) ξ
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map ι
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨a, ha⟩ := IsSepClosed.exists_pow_nat_eq
    ((Scheme.ΓSpecIso (.of Ω)).hom (ξ.appLE V ⊤ hξ.ge v)) (n : ℕ)
  let τ : Γ(Spec (.of Ω), ⊤) := (Scheme.ΓSpecIso (.of Ω)).inv a
  have hτ : τ ^ (n : ℕ) = ξ.appLE V ⊤ hξ.ge v := by
    apply (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective
    rw [map_pow]
    change ((Scheme.ΓSpecIso (.of Ω)).hom ((Scheme.ΓSpecIso (.of Ω)).inv a)) ^ (n : ℕ) = _
    rw [Iso.inv_hom_id_apply]
    exact ha
  obtain ⟨s, _hs⟩ := exists_rootLiftCoordinate π V ξ hξ T (n : ℕ) v (hlift _ ξ hξ) τ hτ
  exact ⟨(fiberLiftEquiv ξ (M.openKummerCover S n hn w j hj hinterior)).symm s⟩

/-- Root scaling acts freely and transitively on the actual geometric fiber,
including for disconnected normalized Kummer covers. -/
theorem kummerGeometricRootAction_existsUnique [IsSepClosed K]
    (x y : (FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn w j hj hinterior)) :
    let := kummerGeometricRootAction M S n w j hj hinterior hn ξ
    ∃! ζ : rootsOfUnity (n : ℕ) K, ζ • x = y := by
  let := kummerGeometricRootAction M S n w j hj hinterior hn ξ
  obtain ⟨q, hqinj, hqzero, hqpow, hqscale⟩ :=
    exists_kummerFiberCoordinate M S n w j hj hinterior hn ξ
  obtain ⟨ζ, hζ, huniq⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
    (pointScalar (j ≫ M.toBase) ξ) n hn (q x) (q y) (hqzero x) (hqpow x y)
  refine ⟨ζ, hqinj ((hqscale ζ x).trans hζ), ?_⟩
  intro η hη
  apply huniq η
  exact (hqscale η x).symm.trans (congrArg q hη)

/-- The torsor structure uses the already constructed root-scaling action on
the original geometric fiber; no connectedness hypothesis is required. -/
@[instance_reducible]
def kummerGeometricRootTorsor [IsSepClosed K] :
    Torsor (rootsOfUnity (n : ℕ) K)
      ((FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn w j hj hinterior)) := by
  let a := kummerGeometricRootAction M S n w j hj hinterior hn ξ
  let d (x y : (FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn w j hj hinterior)) :
      rootsOfUnity (n : ℕ) K :=
    Classical.choose (kummerGeometricRootAction_existsUnique M S n w j hj hinterior hn ξ y x).exists
  have hd (x y : (FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn w j hj hinterior)) :
      d x y • y = x :=
    Classical.choose_spec
      (kummerGeometricRootAction_existsUnique M S n w j hj hinterior hn ξ y x).exists
  exact {
    toMulAction := a
    sdiv := d
    nonempty := kummerGeometricFiber_nonempty M S n w j hj hinterior hn ξ
    sdiv_smul' := hd
    smul_sdiv' := fun ζ x =>
      (kummerGeometricRootAction_existsUnique M S n w j hj hinterior hn ξ x (ζ • x)).unique
        (hd (ζ • x) x) rfl }

end AlgebraicCurve.CurveModel.OpenKummer
