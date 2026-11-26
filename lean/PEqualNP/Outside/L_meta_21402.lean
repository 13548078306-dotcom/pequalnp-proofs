import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21402_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [4, 19]⟩], 20⟩

theorem valid : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21402_aux

theorem PEqualNP.Outside.L_meta_21402 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114429 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_21402_aux.circuit, PEqualNP.Outside.L_meta_21402_aux.valid, by decide, by decide +kernel⟩
