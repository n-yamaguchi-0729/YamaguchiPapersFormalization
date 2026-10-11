/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.GaloisH2OfTsen
import Nyll.GaloisCohomology.Kummer.FiniteKummerAbsoluteLift
import Nyll.GaloisCohomology.Topology.GaloisFiniteStageFunctions
import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Continuous mod-p two-cocycle primitives over curve function fields

A continuous finite-valued cocycle descends to an actual finite Galois
intermediate field. Tsen supplies vanishing of its actual field-unit H²
class. The existing Hilbert-90 and Kummer correction gives a continuous
mod-p primitive on the absolute Galois group.

This proves an absolute-Galois statement. It does not assert the still
separate comparison with higher étale cohomology of a curve.
-/

open CategoryTheory
open scoped Topology

namespace AlgebraicCurve

open ClassFieldTower.Martinet.Shafarevich

/-- Every continuous mod-p two-cocycle on the actual absolute Galois
group of a characteristic-zero curve function field is a continuous
coboundary. No finite-stage norm or vanishing hypothesis is required. -/
theorem exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (c : C(Field.absoluteGaloisGroup F × Field.absoluteGaloisGroup F,
      ULift.{0} (ZMod (p : ℕ))))
    (hc : ∀ s t u : Field.absoluteGaloisGroup F,
      c (s * t, u) + c (s, t) = c (t, u) + c (s, t * u)) :
    ∃ a : C(Field.absoluteGaloisGroup F, ULift.{0} (ZMod (p : ℕ))),
      ∀ s t, a t + a s - a (s * t) = c (s, t) := by
  classical
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨E, cE, hfac⟩ :=
    GaloisCohomology.exists_finiteGalois_factor_continuous_pair
      (K := F) (Ω := AlgebraicClosure F) c c.continuous
  let r : Gal(AlgebraicClosure F/F) →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective _
  have hcE (s t u : Gal(E/F)) :
      cE (s * t) u + cE s t = cE t u + cE s (t * u) := by
    obtain ⟨s', rfl⟩ := hr s
    obtain ⟨t', rfl⟩ := hr t
    obtain ⟨u', rfl⟩ := hr u
    rw [← map_mul r, ← map_mul r]
    change cE (AlgEquiv.restrictNormalHom E (s' * t'))
        (AlgEquiv.restrictNormalHom E u') +
      cE (AlgEquiv.restrictNormalHom E s') (AlgEquiv.restrictNormalHom E t') =
      cE (AlgEquiv.restrictNormalHom E t') (AlgEquiv.restrictNormalHom E u') +
      cE (AlgEquiv.restrictNormalHom E s')
        (AlgEquiv.restrictNormalHom E (t' * u'))
    rw [hfac, hfac, hfac, hfac]
    exact hc s' t' u'
  let z : groupCohomology.cocycles₂
      (Rep.trivial ℤ Gal(E/F) (ULift.{0} (ZMod (p : ℕ)))) :=
    ⟨fun st => cE st.1 st.2,
      (groupCohomology.mem_cocycles₂_iff _).mpr hcE⟩
  have hmu : (primitiveRoots (p : ℕ) F).Nonempty := by
    have : NeZero (p : ℕ) := ⟨p.ne_zero⟩
    obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (p : ℕ)
    exact ⟨algebraMap K F zeta,
      (mem_primitiveRoots p.pos).mpr
        (hzeta.map_of_injective (algebraMap K F).injective)⟩
  let zu := groupCohomology.mapCocycles₂ (MonoidHom.id Gal(E/F))
    (finiteKummerCoefficientRepHom F E p hmu) z
  have hz : groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F E) zu = 0 :=
    galoisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional K x hx hfin E _
  obtain ⟨b, hb⟩ : ∃ b : Gal(E/F) → Additive Eˣ,
      (groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits F E)).hom b = zu.1 :=
    (groupCohomology.H2π_eq_zero_iff zu).mp hz
  obtain ⟨a, ha⟩ := exists_absoluteZModP_primitive_of_finiteKummerUnit_boundary
    F p E hmu cE (fun s => (b s).toMul) (by
      intro s t
      have h := congrArg Additive.toMul (congrFun hb (s, t))
      change Units.map (s : E →* E) (b t).toMul / (b (s * t)).toMul * (b s).toMul =
        (finiteKummerCoefficientAddHom F E p hmu (cE s t)).toMul at h
      simpa only [div_mul_eq_mul_div] using h)
  refine ⟨a, ?_⟩
  intro s t
  rw [ha]
  exact hfac s t

/-- Actual continuous degree-two cohomology with trivial mod-p coefficients
vanishes for the absolute Galois group of the curve function field. -/
theorem absoluteGalois_continuousH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (v : ClassFieldTower.Cohomology.continuousCohomologyZModPLifted
      (p : ℕ) (Field.absoluteGaloisGroup F) 2) : v = 0 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure F/F))
  let A : TopRep (ZMod (p : ℕ)) (Field.absoluteGaloisGroup F) :=
    ClassFieldTower.Cohomology.trivialZModPLifted
    (p : ℕ) (Field.absoluteGaloisGroup F)
  obtain ⟨z, rfl⟩ := ContinuousCohomology.π_surjective A 2 v
  let c : C(Field.absoluteGaloisGroup F × Field.absoluteGaloisGroup F,
      ULift.{0} (ZMod (p : ℕ))) :=
    ⟨fun st => ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle z st.1 st.2,
      ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle_continuous z⟩
  obtain ⟨a, ha⟩ :=
    exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
      K x hx hfin p c (by
        intro s t u
        change ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle z (s * t) u +
            ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle z s t =
          ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle z t u +
            ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle z s (t * u)
        rw [add_comm]
        exact ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle_cocycle z s t u)
  let b : C(Field.absoluteGaloisGroup F, ULift.{0} (ZMod (p : ℕ))) := -a
  have hb (s t : Field.absoluteGaloisGroup F) :
      b (s * t) = b s + b t +
        ClassFieldTower.ProP.FreeProPH2Cocycle.normalizedCocycle z s t := by
    change -a (s * t) = -a s + -a t + c (s, t)
    rw [← ha s t]
    abel
  let C := TopRep.homogeneousCochains A
  let q : C.X 1 := ClassFieldTower.ProP.FreeProPH2Cocycle.homogeneousPrimitive z b
  have hq : (C.d 1 2).hom q = (C.iCycles 2).hom z :=
    ClassFieldTower.ProP.FreeProPH2Cocycle.homogeneousPrimitive_boundary z b hb
  have hz : (C.toCycles 1 2).hom q = z := by
    apply ClassFieldTower.Cohomology.topModule_mono_injective_lifted (C.iCycles 2)
    calc
      (C.iCycles 2).hom ((C.toCycles 1 2).hom q) = (C.d 1 2).hom q :=
        ConcreteCategory.congr_hom (C.toCycles_i 1 2) q
      _ = (C.iCycles 2).hom z := hq
  rw [← hz]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) q

end AlgebraicCurve
