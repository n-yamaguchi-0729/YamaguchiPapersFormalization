/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_exists_sumMap
import AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver

/-!
# The test-scheme kernel of the universal divisor sum map

The existing finite flat sum cover has exactly the same-divisor relation on every
test scheme, including nonreduced schemes. This comparison uses the actual universal
divisor, its classifying morphisms, and naturality of products of graph ideals.

This supplies a kernel comparison. It does not assert that arbitrary-target finite
sums equalize that kernel, nor that principal divisors vanish under such sums.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelEffCartierDiv.IsUniversal

/-- The finite flat sum cover identifies precisely the families with the same graph-ideal
product on every test scheme. -/
theorem exists_sumMap_with_sameDivisor_kernel
    {C S : Scheme.{u}} {f : C ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {D : RelEffCartierDiv f r y}
    (hU : D.IsUniversal) :
    ∃ (σ : fibrePowOver f r ⟶ Y) (hσ : σ ≫ y = fibrePowOver.toBase f r),
      D.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r ∧
      IsFinite σ ∧ Flat σ ∧ LocallyOfFinitePresentation σ ∧ Surjective σ ∧
      (∀ z : Y, σ.finrank z = r.factorial) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (u v : T ⟶ fibrePowOver f r)
        (hu : u ≫ fibrePowOver.toBase f r = g)
        (hv : v ≫ fibrePowOver.toBase f r = g),
        u ≫ σ = v ≫ σ ↔
          SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, hu])
            (fun i => v ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, hv]) := by
  obtain ⟨σ, hσ, hI, hfinite, hflat, hlfp, hsurj, hrank⟩ := hU.exists_sumMap
  have key {T : Scheme.{u}} (g : T ⟶ S) (u : T ⟶ fibrePowOver f r)
      (hu : u ≫ fibrePowOver.toBase f r = g) :
      (D.pullbackAlong (u ≫ σ) (by rw [Category.assoc, hσ, hu])).I =
        prodKerGraph f (fun i => u ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, hu]) := by
    rw [← D.pullbackAlong_comp σ hσ u hu]
    change (D.I.comap (mapOnProdOver f σ hσ)).comap (mapOnProdOver f u hu) = _
    rw [hI]
    exact prodKerGraph_comap_mapOnProdOver
      (fibrePowOver.proj f r) (fibrePowOver.proj_comp f r) u hu
  refine ⟨σ, hσ, hI, hfinite, hflat, hlfp, hsurj, hrank, ?_⟩
  intro T g u v hu hv
  have huσ : (u ≫ σ) ≫ y = g := by rw [Category.assoc, hσ, hu]
  have hvσ : (v ≫ σ) ≫ y = g := by rw [Category.assoc, hσ, hv]
  have pullback_congr {φ ψ : T ⟶ Y} (h : φ = ψ)
      (hφ : φ ≫ y = g) (hψ : ψ ≫ y = g) :
      D.pullbackAlong φ hφ = D.pullbackAlong ψ hψ := by
    cases h
    rfl
  constructor
  · intro h
    have hD : D.pullbackAlong (u ≫ σ) huσ = D.pullbackAlong (v ≫ σ) hvσ :=
      pullback_congr h huσ hvσ
    change prodKerGraph f _ _ = prodKerGraph f _ _
    exact (key g u hu).symm.trans ((congrArg RelEffCartierDiv.I hD).trans (key g v hv))
  · intro h
    change prodKerGraph f _ _ = prodKerGraph f _ _ at h
    have hD : D.pullbackAlong (u ≫ σ) huσ = D.pullbackAlong (v ≫ σ) hvσ := by
      apply RelEffCartierDiv.ext
      exact (key g u hu).trans (h.trans (key g v hv).symm)
    calc
      u ≫ σ = hU.lift (D.pullbackAlong (u ≫ σ) huσ) :=
        hU.eq_lift huσ (pullsBackOver_pullbackAlong D (u ≫ σ) huσ)
      _ = hU.lift (D.pullbackAlong (v ≫ σ) hvσ) :=
        congrArg (fun E : RelEffCartierDiv f r g => hU.lift E) hD
      _ = v ≫ σ :=
        (hU.eq_lift hvσ (pullsBackOver_pullbackAlong D (v ≫ σ) hvσ)).symm

end AlgebraicGeometry.RelEffCartierDiv.IsUniversal
