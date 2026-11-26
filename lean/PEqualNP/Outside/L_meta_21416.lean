import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21416_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 16]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [11, 19]⟩], 20⟩

theorem valid : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21416_aux

theorem PEqualNP.Outside.L_meta_21416 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (111357 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_21416_aux.circuit, PEqualNP.Outside.L_meta_21416_aux.valid, by decide, by decide +kernel⟩
