import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21434_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [5, 16]⟩, ⟨.and, [0, 17]⟩, ⟨.or, [4, 16]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [11, 22]⟩], 23⟩

theorem valid : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21434_aux

theorem PEqualNP.Outside.L_meta_21434 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241598 : ℕ).testBit (5 * u.val + v.val)) 15) := by
  exact ⟨PEqualNP.Outside.L_meta_21434_aux.circuit, PEqualNP.Outside.L_meta_21434_aux.valid, by decide, by decide +kernel⟩
