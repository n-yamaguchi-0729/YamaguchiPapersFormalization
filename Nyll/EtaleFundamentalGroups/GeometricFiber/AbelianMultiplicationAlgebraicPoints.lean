/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationFiberAction
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Mathlib.Algebra.Algebra.Hom

/-!
# Actual multiplication fibres as algebraic division points

The fibre point is converted to the additive group of actual algebraic
points. Its division equation and monodromy translation are consequences
of the original finite étale cover and group scheme law.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra K Ω]

omit [IsAlgClosed K] in
/-- An actual multiplication-cover fibre point, expressed as an algebraic point. -/
def multiplicationFiberAlgPoint
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : ℕ+) (z : (FiniteEtale.fiber ξ.1).obj (G.multiplicationCover hc n)) :
    G.AlgPoints hc Ω :=
  AlgPoints.ofPoint
    ⟨(G.multiplicationFiberPoint hc ξ.1 n z).1,
      (G.multiplicationFiberPoint hc ξ.1 n z).2.trans ξ.2⟩

omit [IsAlgClosed K] in
/-- The algebraic point constructed from the fibre satisfies its actual division equation. -/
theorem nsmul_multiplicationFiberAlgPoint
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : ℕ+) (z : (FiniteEtale.fiber ξ.1).obj (G.multiplicationCover hc n)) :
    (n : ℕ) • G.multiplicationFiberAlgPoint hc ξ n z = AlgPoints.ofPoint ξ := by
  let s : Spec (.of Ω) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let q₀ : SchemeHomOver (ξ.1 ≫ f) f :=
    G.multiplicationFiberPoint hc ξ.1 n z
  let q : SchemeHomOver s f := ⟨q₀.1, q₀.2.trans ξ.2⟩
  have hchange (b : Spec (.of Ω) ⟶ Spec (.of K)) (hb : b = s)
      (p : SchemeHomOver b f) :
      G.nsmul s (n : ℕ) ⟨p.1, p.2.trans hb⟩ =
        (⟨(G.nsmul b (n : ℕ) p).1,
          (G.nsmul b (n : ℕ) p).2.trans hb⟩ : SchemeHomOver s f) := by
    subst b
    rfl
  have hdivision : G.nsmul (ξ.1 ≫ f) (n : ℕ) q₀ =
      (⟨ξ.1, rfl⟩ : SchemeHomOver (ξ.1 ≫ f) f) :=
    G.multiplicationFiberPoint_nsmul hc ξ.1 n z
  have htransport :
      (⟨(G.nsmul (ξ.1 ≫ f) (n : ℕ) q₀).1,
        (G.nsmul (ξ.1 ≫ f) (n : ℕ) q₀).2.trans ξ.2⟩ :
        SchemeHomOver s f) = ξ :=
    Subtype.ext (congrArg
      (fun p : SchemeHomOver (ξ.1 ≫ f) f => p.1) hdivision)
  have hn : G.nsmul s (n : ℕ) q = ξ :=
    (hchange (ξ.1 ≫ f) ξ.2 q₀).trans htransport
  exact (AlgPoints.ofPoint_nsmul (L := G) (hc := hc) (T := Ω)
      (n : ℕ) q).symm.trans
    (congrArg (fun p : SchemeHomOver s f =>
      (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω) p : G.AlgPoints hc Ω)) hn)

/-- Actual monodromy on the fibre is addition of the actual torsion point,
also after passage to the algebraic-point group over the geometric field. -/
theorem multiplicationFiberAlgPoint_smul
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : ℕ+)
    (τ : FiniteEtale.fiber ξ.1 ≅ FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (g : π₁ᵉᵗ(ξ.1))
    (z : (FiniteEtale.fiber ξ.1).obj (G.multiplicationCover hc n)) :
    G.multiplicationFiberAlgPoint hc ξ n (g • z) =
      G.multiplicationFiberAlgPoint hc ξ n z +
        AlgPoints.map (L := G) (hc := hc) (T := K) (T' := Ω) (Algebra.ofId K Ω)
          (G.multiplicationMonodromy hc n (continuousConjAut τ g)).1 := by
  let s : Spec (.of Ω) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let b : Spec (.of Ω) ⟶ Spec (.of K) := ξ.1 ≫ f
  have hsum (p : SchemeHomOver b f)
      (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
      (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω)
        (⟨(G.mul b p (GoodReductionJacobian.schemeHomOverComp b
            (Category.comp_id b) (G.torsionPointSection hc n t))).1,
          (G.mul b p (GoodReductionJacobian.schemeHomOverComp b
            (Category.comp_id b) (G.torsionPointSection hc n t))).2.trans ξ.2⟩ :
          SchemeHomOver s f) : G.AlgPoints hc Ω) =
        (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω)
          (⟨p.1, p.2.trans ξ.2⟩ : SchemeHomOver s f) : G.AlgPoints hc Ω) +
          AlgPoints.map (L := G) (hc := hc) (T := K) (T' := Ω)
            (Algebra.ofId K Ω) t.1 := by
    let q : SchemeHomOver s f := ⟨p.1, p.2.trans ξ.2⟩
    let u₀ : SchemeHomOver b f := GoodReductionJacobian.schemeHomOverComp b
      (Category.comp_id b) (G.torsionPointSection hc n t)
    let u : SchemeHomOver s f := ⟨u₀.1, u₀.2.trans ξ.2⟩
    have hchange (c : Spec (.of Ω) ⟶ Spec (.of K)) (hc' : c = s)
        (v w : SchemeHomOver c f) :
        (⟨(G.mul c v w).1, (G.mul c v w).2.trans hc'⟩ : SchemeHomOver s f) =
          G.mul s ⟨v.1, v.2.trans hc'⟩ ⟨w.1, w.2.trans hc'⟩ := by
      subst c
      rfl
    have hpoint :
        (⟨(G.mul b p u₀).1, (G.mul b p u₀).2.trans ξ.2⟩ : SchemeHomOver s f) =
          G.mul s q u :=
      hchange b ξ.2 p u₀
    let a : K →ₐ[K] Ω := Algebra.ofId K Ω
    let y : G.AlgPoints hc Ω :=
      AlgPoints.map (L := G) (hc := hc) (T := K) (T' := Ω) a t.1
    have hscalar : a.toRingHom = algebraMap K Ω :=
      Algebra.toRingHom_ofId (R := K) Ω
    have hmap : (AlgPoints.toPoint (L := G) (hc := hc) (T := Ω) y).1 =
        s ≫ (AlgPoints.toPoint (L := G) (hc := hc) (T := K) t.1).1 :=
      (AlgPoints.toPoint_map_coe (L := G) (hc := hc) (T := K) (T' := Ω) a t.1).trans
        (congrArg (fun ψ : K →+* Ω =>
          Spec.map (CommRingCat.ofHom ψ) ≫
            (AlgPoints.toPoint (L := G) (hc := hc) (T := K) t.1).1) hscalar)
    have hbase : u.1 =
        s ≫ (AlgPoints.toPoint (L := G) (hc := hc) (T := K) t.1).1 :=
      congrArg (fun c : Spec (.of Ω) ⟶ Spec (.of K) =>
        c ≫ (AlgPoints.toPoint (L := G) (hc := hc) (T := K) t.1).1) ξ.2
    have hu : u = AlgPoints.toPoint (L := G) (hc := hc) (T := Ω) y :=
      Subtype.ext (hbase.trans hmap.symm)
    have hofu : (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω) u : G.AlgPoints hc Ω) = y :=
      (congrArg (fun r : SchemeHomOver s f =>
        (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω) r : G.AlgPoints hc Ω)) hu).trans
        (AlgPoints.ofPoint_toPoint (L := G) (hc := hc) (T := Ω) y)
    have hadd :
        (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω) (G.mul s q u) : G.AlgPoints hc Ω) =
          (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω) q : G.AlgPoints hc Ω) + y :=
      (AlgPoints.ofPoint_mul (L := G) (hc := hc) (T := Ω) q u).trans
        (congrArg (fun v : G.AlgPoints hc Ω =>
          (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω) q : G.AlgPoints hc Ω) + v) hofu)
    exact (congrArg (fun r : SchemeHomOver s f =>
      (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω) r : G.AlgPoints hc Ω)) hpoint).trans hadd
  exact (congrArg (fun p : SchemeHomOver b f =>
    (AlgPoints.ofPoint (L := G) (hc := hc) (T := Ω)
      (⟨p.1, p.2.trans ξ.2⟩ : SchemeHomOver s f) : G.AlgPoints hc Ω))
    (G.multiplicationFiberPoint_smul hc ξ.1 n τ g z)).trans
      (hsum (G.multiplicationFiberPoint hc ξ.1 n z)
        (G.multiplicationMonodromy hc n (continuousConjAut τ g)))

end GoodReductionJacobian.RelativeGroupLaw
