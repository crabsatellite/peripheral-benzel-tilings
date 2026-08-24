import BenzelProblem6Kernel.PeripheralOddSideIncidences
import BenzelProblem6Kernel.PeripheralDirectedBoundary

/-! # Global uniqueness of the explicit peripheral incidences -/

namespace BenzelProblem6Kernel

theorem nodup_of_hexSide_filters (incidences : List CellSide)
    (hfilters : ∀ side : HexSide,
      (incidences.filter (fun datum => datum.2 == side)).Nodup) :
    incidences.Nodup := by
  induction incidences with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons]
      constructor
      · intro hhead
        have hfiltered := hfilters head.2
        simp only [List.filter_cons, beq_self_eq_true, if_true,
          List.nodup_cons] at hfiltered
        exact hfiltered.1 (List.mem_filter.mpr ⟨hhead, by simp⟩)
      · apply ih
        intro side
        have hfiltered := hfilters side
        simp only [List.filter_cons] at hfiltered
        split at hfiltered
        · exact (List.nodup_cons.mp hfiltered).2
        · exact hfiltered

theorem literalPeripheralIncidences_nodup (m : ℕ) :
    (literalPeripheralIncidences m).Nodup := by
  apply nodup_of_hexSide_filters
  intro side
  cases side
  · exact literalPeripheralSide₀Incidences_nodup m
  · exact literalPeripheralSide₁Incidences_nodup m
  · exact literalPeripheralSide₂Incidences_nodup m
  · exact literalPeripheralSide₃Incidences_nodup m
  · exact literalPeripheralSide₄Incidences_nodup m
  · exact literalPeripheralSide₅Incidences_nodup m

theorem literalReducedPeripheralBoundary_nodup (m : ℕ) :
    (literalReducedPeripheralBoundary m).Nodup := by
  rw [literalReducedPeripheralBoundary]
  exact (List.nodup_reverse.mpr
    (literalPeripheralIncidences_nodup m)).map
      cellSideBoundaryEdge_injective

end BenzelProblem6Kernel
