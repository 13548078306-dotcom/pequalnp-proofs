import PEqualNP.Defs

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_22741 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (191 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 9]⟩], 10⟩

  exact ⟨circuit, by simp [PEqualNP.MetaComplexity.FanInTwo, circuit],
    by decide +kernel, by decide +kernel⟩
