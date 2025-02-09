import Mathlib.Topology.Connected.Clopen

variable {X : Type*} [TopologicalSpace X]

theorem preconnectedSpace_iff_clopen :
    PreconnectedSpace X ↔ ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ :=
  ⟨fun _ s hs ↦ isClopen_iff.mp hs, fun h ↦ ⟨fun u v hu hv huv huu hvv ↦ by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hdj
    have h : uᶜ = v := by
      apply subset_antisymm
      · apply Set.compl_subset_iff_union.mpr
        exact Set.eq_univ_of_univ_subset huv
      · apply Disjoint.subset_compl_left
        apply Set.disjoint_iff_inter_eq_empty.mpr
        rwa [Set.univ_inter] at hdj
    subst h
    obtain rfl | rfl := h u ⟨⟨hv⟩, hu⟩
    · simp at huu
    · simp at hvv⟩⟩

theorem connectedSpace_iff_clopen :
    ConnectedSpace X ↔ Nonempty X ∧ ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ := by
  rw [connectedSpace_iff_univ, IsConnected /- is this intended? -/, ← preconnectedSpace_iff_univ,
    preconnectedSpace_iff_clopen, Set.nonempty_iff_univ_nonempty]
