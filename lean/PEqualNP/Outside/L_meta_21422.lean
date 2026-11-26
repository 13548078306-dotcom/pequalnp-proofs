import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21422_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [11, 20]⟩], 21⟩

theorem valid : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21422_aux

theorem PEqualNP.Outside.L_meta_21422 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112380 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_21422_aux.circuit, PEqualNP.Outside.L_meta_21422_aux.valid, by decide, by decide +kernel⟩
