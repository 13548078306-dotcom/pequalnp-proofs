import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22514_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [1, 15]⟩, ⟨.and, [5, 17]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [12, 21]⟩], 22⟩

theorem valid : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22514_aux

theorem PEqualNP.Outside.L_meta_22514 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899769 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22514_aux.circuit, PEqualNP.Outside.L_meta_22514_aux.valid, by decide, by decide +kernel⟩
