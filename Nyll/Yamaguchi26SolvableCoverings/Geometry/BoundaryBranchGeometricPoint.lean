/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryInertia
import Nyll.SchemeTheory.Affine.GeometricPointLocalization
import Nyll.SchemeTheory.Divisors.ComponentStalkBranch
import Nyll.SchemeTheory.FunctionFields.PlainIntegerBase
import Nyll.EtaleFundamentalGroups.GeometricFiber.RegularBoundarySurjective
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.ComponentMappedFiniteQuotientInertia

/-!
# The fixed component geometric point on a local arithmetic chart

The branch prime selected by the normal-crossings construction lies over the
original component generic point. Its geometric point on every further prime
localization has the same algebraically closed field and the same composite
morphism as `componentGeometricPoint`. This makes the local chart usable for
the stabilizer of the specified global normalization point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

namespace Yamaguchi26SolvableCoverings

private theorem fromSpecStalk_eq_of_ideal_transport
    {X : Scheme} {x x' : X} (h : x = x')
    (r : Spec (X.presheaf.stalk x)) (q : Spec (X.presheaf.stalk x'))
    (hqr : q.asIdeal = h ▸ r.asIdeal) :
    X.fromSpecStalk x' q = X.fromSpecStalk x r := by
  subst x'
  exact congrArg (X.fromSpecStalk x) (PrimeSpectrum.ext hqr)

variable {X : Scheme.{0}}

/-- A chart branch contracting to the canonical component branch maps to
that exact component generic point, including the change of centre point. -/
theorem image_etaleBranch_eq_componentPoint
    (D : X.EffectiveCartierDivisor) (E : Component D)
    (x : D.1.subscheme) (hx : x ∈ E.val)
    {U : Scheme.{0}} (f : U ⟶ X) (u : U)
    (hfu : f u = D.1.subschemeι x)
    (q : Ideal (U.presheaf.stalk u)) [hq : q.IsPrime]
    (hqcomap : q.comap (f.stalkMap u).hom =
      hfu.symm ▸ (D.1.componentBranchPrimeAt E.val E.property x hx).asIdeal) :
    f (U.fromSpecStalk u ⟨q, hq⟩) = componentPoint D E := by
  let qSpec : Spec (U.presheaf.stalk u) := ⟨q, hq⟩
  have htransport := fromSpecStalk_eq_of_ideal_transport hfu.symm
    (D.1.componentBranchPrimeAt E.val E.property x hx)
    (Spec.map (f.stalkMap u) qSpec) hqcomap
  calc
    f (U.fromSpecStalk u qSpec) =
        X.fromSpecStalk (f u) (Spec.map (f.stalkMap u) qSpec) :=
      (congrArg (fun k : Spec (U.presheaf.stalk u) ⟶ X => k qSpec)
        (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := u))).symm
    _ = X.fromSpecStalk (D.1.subschemeι x)
        (D.1.componentBranchPrimeAt E.val E.property x hx) := htransport
    _ = componentPoint D E := by
      rw [D.1.fromSpecStalk_componentBranchPrimeAt, D.1.componentGenericPoint_eq]
      rfl

/-- The prescribed global component geometric point lifts to the selected
branch of the localized chart. No extension or identification of the chosen
algebraically closed field is left as an additional assumption. -/
theorem exists_componentGeometricPoint_localized_etaleBranch
    (D : X.EffectiveCartierDivisor) (E : Component D)
    (x : D.1.subscheme) (hx : x ∈ E.val)
    {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (u : U)
    (hfu : f u = D.1.subschemeι x)
    (q : Ideal (U.presheaf.stalk u)) [hq : q.IsPrime]
    (hqcomap : q.comap (f.stalkMap u).hom =
      hfu.symm ▸ (D.1.componentBranchPrimeAt E.val E.property x hx).asIdeal)
    (P : Ideal (U.presheaf.stalk u)) [P.IsPrime] (hqP : q ≤ P) :
    ∃ y : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
        Spec (.of (Localization.AtPrime P)),
      (y (closedPoint (AlgebraicClosure (X.residueField (componentPoint D E))))).asIdeal =
        q.map (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P)) ∧
      y ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P))) ≫
        U.fromSpecStalk u ≫ f = componentGeometricPoint D E := by
  exact exists_geometricPoint_localized_chart_branch f u ⟨q, hq⟩ P hqP
    (componentPoint D E)
    (image_etaleBranch_eq_componentPoint D E x hx f u hfu q hqcomap)
    (AlgebraicClosure (X.residueField (componentPoint D E)))
    (CommRingCat.ofHom (algebraMap (X.residueField (componentPoint D E))
      (AlgebraicClosure (X.residueField (componentPoint D E)))))

/-- The hypotheses of Lemma 1.2 supply an arithmetic chart whose mapped
inertia estimate and local geometric points use the original component.
The point construction applies in particular to the height-two prime
provided by the mapped-inertia estimate. -/
theorem exists_arithmeticBoundaryChart_with_componentGeometricPoint
    [IsLocallyNoetherian X] [ConnectedSpace X]
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hreg : D.IsAmbientRegularAlongSupport) (E : Component D)
    (p : ℕ) (hp : p.Prime)
    (hnc : ∃ x : D.1.subscheme, x ∈ E.val ∧
      ringChar (X.residueField (D.1.subschemeι x)) = p ∧
        D.IsNormalCrossingsAt (D.1.subschemeι x)) :
    letI : ConnectedSpace D.1.supportComplement :=
      AlgebraicGeometry.FiniteEtale.boundaryComplement_connectedSpace D hreg
    ∃ (U : Scheme.{0}) (f : U ⟶ X) (_hf : Etale f) (u : U)
      (q : Ideal (U.presheaf.stalk u)) (_hq : q.IsPrime),
      D.1.HasMappedQuotientIdealInertiaCoprime f u q p ∧
      ∀ (P : Ideal (U.presheaf.stalk u)) (_hP : P.IsPrime), q ≤ P →
        ∃ y : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
            Spec (.of (Localization.AtPrime P)),
          (y (closedPoint
            (AlgebraicClosure (X.residueField (componentPoint D E))))).asIdeal =
              q.map (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P)) ∧
          y ≫ Spec.map (CommRingCat.ofHom
              (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P))) ≫
            U.fromSpecStalk u ≫ f = componentGeometricPoint D E := by
  let : ConnectedSpace D.1.supportComplement :=
    AlgebraicGeometry.FiniteEtale.boundaryComplement_connectedSpace D hreg
  obtain ⟨x, hx, hchar, hnc⟩ := hnc
  let : CharZero ((Spec (.of ℤ)).residueField (genericPoint (Spec (.of ℤ)))) :=
    specZGenericResidueFieldEquivQ.toRingHom.charZero
  let : CharP (X.residueField (D.1.subschemeι x)) p := ringChar.of_eq hchar
  have hhorizontal : D.ComponentsThroughPointAreHorizontal (toIntegers X) x :=
    fun Z hZ _ => hhor Z hZ
  obtain ⟨U, f, u, hfu, hf, _, _, q, hq, _, _, hqcomap, hmapped⟩ :=
    hhorizontal.exists_etaleStrictChart_component_mappedQuotientIdealInertia_coprime
      D (toIntegers X) E.val E.property x hx hnc p hp
  let : Etale f := hf
  let : q.IsPrime := hq
  refine ⟨U, f, hf, u, q, hq, hmapped, ?_⟩
  intro P hP hqP
  let : P.IsPrime := hP
  exact exists_componentGeometricPoint_localized_etaleBranch
    D E x hx f u hfu q hqcomap P hqP

end Yamaguchi26SolvableCoverings
