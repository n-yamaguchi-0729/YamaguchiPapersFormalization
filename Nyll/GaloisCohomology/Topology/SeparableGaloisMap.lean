/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.AbsoluteGaloisMap
public import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
public import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutEquiv

/-!
# Restriction maps on the separable parts of algebraic closures

The algebraic-closure embedding used for absolute Galois restriction preserves
the separable closure. Its restriction intertwines the actual Galois maps.
-/

@[expose] public section

namespace Field.absoluteGaloisGroup

variable {K L : Type*} [Field K] [Field L]

/-- The chosen algebraic-closure embedding restricts to the separable closures. -/
noncomputable def separableClosureLift (f : K →+* L) :
    SeparableClosure K →+* SeparableClosure L := by
  let : Algebra K L := f.toAlgebra
  let j : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  refine (closureLift f).comp (separableClosure K (AlgebraicClosure K)).val.toRingHom |>.codRestrict
    (separableClosure L (AlgebraicClosure L)) ?_
  intro s
  apply mem_separableClosure_iff.mpr
  change IsSeparable L (j (s : AlgebraicClosure K))
  exact (IsSeparable.map j j.injective (mem_separableClosure_iff.mp s.property)).tower_top L

/-- Inclusion into the algebraic closure recovers the chosen closure embedding. -/
theorem separableClosureLift_coe (f : K →+* L) (s : SeparableClosure K) :
    (separableClosureLift f s : AlgebraicClosure L) = closureLift f (s : AlgebraicClosure K) := rfl

/-- The separable-closure embedding extends the original field embedding. -/
theorem separableClosureLift_algebraMap (f : K →+* L) (x : K) :
    separableClosureLift f (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (f x) := by
  apply Subtype.ext
  exact closureLift_algebraMap f x

/-- Galois restriction intertwines the induced embedding of separable closures. -/
theorem map_separableClosureLift (f : K →+* L)
    (σ : Gal(AlgebraicClosure L/L)) (s : SeparableClosure K) :
    separableClosureLift f
        (ValuationTheory.Completion.separableClosureAutEquiv K (map f σ) s) =
      ValuationTheory.Completion.separableClosureAutEquiv L σ (separableClosureLift f s) := by
  apply Subtype.ext
  exact (congrArg (closureLift f)
    (ValuationTheory.Completion.separableClosureAutEquiv_apply K (map f σ) s)).trans
      ((map_closureLift f σ (s : AlgebraicClosure K)).trans
        (ValuationTheory.Completion.separableClosureAutEquiv_apply L σ
          (separableClosureLift f s)).symm)

/-- The actual continuous absolute Galois map, expressed on the native
separable closures by the original restriction equivalences. -/
noncomputable def separableMap (f : K →+* L) :
    Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv K)).comp
      ((map f).comp (ContinuousMonoidHom.toContinuousMonoidHom
        (ValuationTheory.Completion.separableClosureAutContinuousEquiv L).symm))

/-- The native separable Galois map has exactly the action induced by the
chosen embedding behind the original algebraic-closure Galois map. -/
theorem separableMap_commutes (f : K →+* L)
    (σ : Gal(SeparableClosure L/L)) (s : SeparableClosure K) :
    separableClosureLift f (separableMap f σ s) = σ (separableClosureLift f s) := by
  change separableClosureLift f
      (ValuationTheory.Completion.separableClosureAutEquiv K
        (map f ((ValuationTheory.Completion.separableClosureAutEquiv L).symm σ)) s) = _
  have h := map_separableClosureLift f
    ((ValuationTheory.Completion.separableClosureAutEquiv L).symm σ) s
  rw [MulEquiv.apply_symm_apply] at h
  exact h

end Field.absoluteGaloisGroup
