/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_split
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver

/-!
Construct the sum map for universal relative effective Cartier divisors.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_IsUniversal_exists_sumMap
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem prodKerGraph_congr {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : Fin r → (T ⟶ 𝒞)} (h : a = a') (ha : ∀ i, a i ≫ f = g) (ha' : ∀ i, a' i ≫ f = g) :
    prodKerGraph f a ha = prodKerGraph f a' ha' := by
  subst h; rfl

namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace IsUniversal
open _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal
open _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal
open _root_.AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}


private theorem _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_sumMap_aux (hU :
    Duniv.IsUniversal) :
    ∃ (σ : fibrePowOver f r ⟶ Y) (hσ : σ ≫ y = fibrePowOver.toBase f r),
      Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r ∧
      IsFinite σ ∧ Flat σ ∧ LocallyOfFinitePresentation σ ∧ Surjective σ ∧
      ∀ x : Y, σ.finrank x = r.factorial := by
  obtain ⟨Dt, hDt⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := f)
    (fibrePowOver.proj f r) (fibrePowOver.proj_comp f r)
  set σ : fibrePowOver f r ⟶ Y := hU.lift Dt with hσdef
  have hσ : σ ≫ y = fibrePowOver.toBase f r := hU.lift_comp Dt
  have hσI : Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r :=
    (hU.pullsBackOver_lift Dt).trans hDt
  clear_value σ
  obtain ⟨P, gP, p, hp, b, hb, hfin, hflat, hlfp, hsurj, hrank, hI, huniv⟩ :=
    RelEffCartierDiv.exists_split Duniv
  subst hp
  obtain ⟨u, ⟨hup, hub⟩, -⟩ := huniv (fibrePowOver.toBase f r) σ hσ (fibrePowOver.proj f r)
    (fibrePowOver.proj_comp f r) hσI
  let t : P ⟶ fibrePowOver f r := WidePullback.lift (p ≫ y) b hb
  have ht_proj : ∀ i, t ≫ fibrePowOver.proj f r i = b i := fun i => WidePullback.lift_π _ _ _ _ _
  have ht_base : t ≫ fibrePowOver.toBase f r = p ≫ y := WidePullback.lift_base _ _ _ _
  have hut : u ≫ t = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro i
      rw [Category.assoc, Category.id_comp]
      exact (ht_proj i).symm ▸ hub i
    · rw [Category.assoc, ht_base, Category.id_comp, ← Category.assoc, hup, hσ]
  have hty : (t ≫ σ) ≫ y = p ≫ y := by rw [Category.assoc, hσ, ht_base]
  have hcomp := congrArg RelEffCartierDiv.I (Duniv.pullbackAlong_comp σ hσ t ht_base)
  have htσ : p = t ≫ σ := by
    refine hU.hom_ext hty.symm ?_
    change (Duniv.pullbackAlong p rfl).I = (Duniv.pullbackAlong (t ≫ σ) hty).I
    rw [hI, ← hcomp]
    change prodKerGraph f b hb =
      ((Duniv.I.comap (mapOnProdOver f σ hσ)).comap (mapOnProdOver f t ht_base))
    rw [hσI, fibrePowOver.tautIdeal, prodKerGraph_comap_mapOnProdOver]
    exact prodKerGraph_congr f (funext fun i => (ht_proj i).symm) _ _
  have htu : t ≫ u = 𝟙 P := by
    obtain ⟨w, -, hwuniq⟩ := huniv (p ≫ y) p rfl b hb hI
    have h1 : t ≫ u = w :=
      hwuniq _ ⟨by rw [Category.assoc, hup, ← htσ], fun i => by rw [Category.assoc, hub, ht_proj]⟩
    have h2 : 𝟙 P = w := hwuniq _ ⟨Category.id_comp _, fun i => Category.id_comp _⟩
    exact h1.trans h2.symm
  have : IsIso u := ⟨⟨t, hut, htu⟩⟩
  subst hup
  exact ⟨u ≫ p, hσ, hσI, inferInstance, inferInstance, inferInstance, inferInstance,
    fun x => by rw [Scheme.Hom.finrank_comp_left_of_isIso]; exact hrank x⟩

open _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal
end RelEffCartierDiv.IsUniversal

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_sumMap
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}
    (hU : Duniv.IsUniversal) :
    ∃ (σ : fibrePowOver f r ⟶ Y) (hσ : σ ≫ y = fibrePowOver.toBase f r),
      Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r ∧
      IsFinite σ ∧ Flat σ ∧ LocallyOfFinitePresentation σ ∧ Surjective σ ∧
      ∀ x : Y, σ.finrank x = r.factorial :=
  hU.exists_sumMap_aux
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_IsUniversal_exists_sumMap
end ProofImplementation
