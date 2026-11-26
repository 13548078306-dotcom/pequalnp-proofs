import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21406_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [4, 19]⟩], 20⟩

theorem valid : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21406_aux

theorem PEqualNP.Outside.L_meta_21406 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241149 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_21406_aux.circuit, PEqualNP.Outside.L_meta_21406_aux.valid, by decide, by decide +kernel⟩
