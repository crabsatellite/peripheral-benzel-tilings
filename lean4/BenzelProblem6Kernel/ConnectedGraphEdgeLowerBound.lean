import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # Edge lower bound for finite connected simple graphs -/

namespace BenzelProblem6Kernel

open SimpleGraph

theorem connected_vertex_card_le_edge_card_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    Fintype.card V ≤ G.edgeFinset.card + 1 := by
  let root : V := Classical.choice hG.nonempty
  choose shortest hshortest using
    fun vertex : V => (hG vertex root).exists_walk_length_eq_dist
  let nonroots : Finset V := Finset.univ.erase root
  let Nonroot := ↥nonroots
  have nonroot_ne (vertex : Nonroot) : vertex.1 ≠ root :=
    (Finset.mem_erase.mp vertex.2).1
  have shortest_nonempty (vertex : Nonroot) : ¬(shortest vertex.1).Nil :=
    SimpleGraph.Walk.not_nil_of_ne (nonroot_ne vertex)
  let parentEdge : Nonroot → Sym2 V := fun vertex =>
    ((shortest vertex.1).firstDart
      (shortest_nonempty vertex)).edge
  have parentEdge_mem (vertex : Nonroot) :
      parentEdge vertex ∈ G.edgeFinset := by
    simp [parentEdge]
  have parentEdge_injective : Function.Injective parentEdge := by
    intro left right hedge
    have hleftNonempty := shortest_nonempty left
    have hrightNonempty := shortest_nonempty right
    let leftDart := (shortest left.1).firstDart hleftNonempty
    let rightDart := (shortest right.1).firstDart hrightNonempty
    have hedgeDart : leftDart.edge = rightDart.edge := by
      exact hedge
    rw [SimpleGraph.dart_edge_eq_iff leftDart rightDart] at hedgeDart
    rcases hedgeDart with hedgeDart | hedgeDart
    · apply Subtype.ext
      simpa [leftDart, rightDart] using
        congrArg (fun dart : G.Dart => dart.fst) hedgeDart
    · have hleftSnd : (shortest left.1).snd = right.1 := by
        simpa [leftDart, rightDart] using
          congrArg (fun dart : G.Dart => dart.snd) hedgeDart
      have hrightSnd : (shortest right.1).snd = left.1 := by
        simpa [leftDart, rightDart] using
          (congrArg (fun dart : G.Dart => dart.fst) hedgeDart).symm
      have hdistRight : G.dist right.1 root ≤
          (shortest left.1).tail.length := by
        simpa [hleftSnd] using
          SimpleGraph.dist_le ((shortest left.1).tail.copy hleftSnd rfl)
      have hdistLeft : G.dist left.1 root ≤
          (shortest right.1).tail.length := by
        simpa [hrightSnd] using
          SimpleGraph.dist_le ((shortest right.1).tail.copy hrightSnd rfl)
      have hleftLength := hshortest left.1
      have hrightLength := hshortest right.1
      have hleftTail :=
        SimpleGraph.Walk.length_tail_add_one hleftNonempty
      have hrightTail :=
        SimpleGraph.Walk.length_tail_add_one hrightNonempty
      omega
  have hcardImage :
      (Finset.univ.image parentEdge).card = Fintype.card Nonroot := by
    rw [Finset.card_image_iff.mpr parentEdge_injective.injOn,
      Finset.card_univ]
  have hsubset : Finset.univ.image parentEdge ⊆ G.edgeFinset := by
    intro edge hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨vertex, hvertex, rfl⟩ := hedge
    exact parentEdge_mem vertex
  have hcardNonroot : Fintype.card Nonroot + 1 = Fintype.card V := by
    rw [Fintype.card_coe]
    change (Finset.univ.erase root).card + 1 = Fintype.card V
    rw [Finset.card_erase_of_mem (by simp)]
    rw [Finset.card_univ]
    have hpositive : 0 < Fintype.card V :=
      Fintype.card_pos_iff.mpr hG.nonempty
    omega
  have hle := Finset.card_le_card hsubset
  rw [hcardImage] at hle
  omega

end BenzelProblem6Kernel
