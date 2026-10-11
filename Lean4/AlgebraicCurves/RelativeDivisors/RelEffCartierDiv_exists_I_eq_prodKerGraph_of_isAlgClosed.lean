/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_split
import AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver

/-!
Express a relative divisor ideal as a product of graph kernels over an algebraically closed
field.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
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
namespace SumPtsAux
end AlgebraicGeometry.SumPtsAux
open scoped AlgebraicGeometry in
theorem AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [Nonempty X] :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ :=
    nonempty_inter_closedPoints (X := X) Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {k : Type u} [Field k] [IsAlgClosed k] {x : Spec (CommRingCat.of k) ⟶ S}
    {r : ℕ} (D : RelEffCartierDiv f r x) :
    ∃ (a : Fin r → (Spec (CommRingCat.of k) ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = x),
      D.I = prodKerGraph f a ha := by
  obtain ⟨P, gP, p, hp, b, hb, hfin, -, -, hsurj, -, hsplit, -⟩ := D.exists_split
  have : Nonempty P := by
    obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary _)
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed p
  have hu' : u ≫ gP = x := by rw [← hp, ← Category.assoc, hu, Category.id_comp]
  have key : D = (D.pullbackAlong p hp).pullbackAlong u hu' := by
    rw [RelEffCartierDiv.pullbackAlong_comp]
    have aux : ∀ (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ x = x),
        φ = 𝟙 _ → D.pullbackAlong φ hφ = D := by
      rintro φ hφ rfl
      exact D.pullbackAlong_id
    exact (aux _ _ hu).symm
  refine ⟨fun i => u ≫ b i, fun i => by rw [Category.assoc, hb, hu'], ?_⟩
  calc D.I = ((D.pullbackAlong p hp).pullbackAlong u hu').I := by rw [← key]
    _ = (D.pullbackAlong p hp).I.comap (mapOnProdOver f u hu') := rfl
    _ = (prodKerGraph f b hb).comap (mapOnProdOver f u hu') := by rw [hsplit]
    _ = prodKerGraph f (fun i => u ≫ b i) _ := prodKerGraph_comap_mapOnProdOver b hb u hu'
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
end ProofImplementation
