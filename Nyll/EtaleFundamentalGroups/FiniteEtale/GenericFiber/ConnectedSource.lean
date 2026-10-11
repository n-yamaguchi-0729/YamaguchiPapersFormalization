/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sober

/-!
# A connected generic fibre of an open morphism

The generic fibre of an open morphism to an irreducible scheme is dense in
the source. If that fibre is geometrically connected, its image is connected
and dense, so the source is connected as well.

For Remark 2.3 this supplies the connectedness of the smooth arithmetic
scheme `E` from the geometric connectedness of `E_ℚ`. Smoothness gives
universal openness through flatness and local finite presentation. Neither
properness nor connectedness of every special fibre is assumed here.
-/

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory TopologicalSpace

universe u

/-- The inclusion of the generic fibre of an open morphism to an
irreducible scheme has dense range. -/
theorem denseRange_genericFiberι_of_isOpenMap
    {X S : Scheme.{u}} [IrreducibleSpace S]
    (f : X ⟶ S) (hf : IsOpenMap f) :
    DenseRange (f.fiberι (genericPoint S)) := by
  change Dense (Set.range (f.fiberι (genericPoint S)))
  rw [f.range_fiberι]
  exact (dense_iff_closure_eq.mpr (genericPoint_closure S)).preimage hf

/-- For a universally open morphism to an irreducible base, a geometrically
connected generic fibre forces the source itself to be connected. -/
theorem connectedSpace_of_geometricallyConnected_genericFiber
    {X S : Scheme.{u}} [IrreducibleSpace S]
    (f : X ⟶ S) [UniversallyOpen f]
    [GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S))] :
    ConnectedSpace X := by
  let : ConnectedSpace (f.fiber (genericPoint S)) :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f.fiberToSpecResidueField (genericPoint S))
  let : PreconnectedSpace X :=
    (denseRange_genericFiberι_of_isOpenMap f f.isOpenMap).preconnectedSpace
      (f.fiberι (genericPoint S)).continuous
  exact ⟨(inferInstance : Nonempty (f.fiber (genericPoint S))).map
    (f.fiberι (genericPoint S))⟩

end AlgebraicGeometry.Scheme.Hom
