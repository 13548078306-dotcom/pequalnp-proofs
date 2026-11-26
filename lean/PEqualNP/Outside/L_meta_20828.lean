import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20828_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem agree_ofFn {m : ℕ} (x y : Fin m → Bool) (k : Fin m)
    (h : ∀ k1 : Fin m, k1 ≠ k → x k1 = y k1) (i : ℕ) (hi : i ≠ k.val) :
    (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  by_cases hlt : i < m
  · rw [ofFn_getD x i hlt, ofFn_getD y i hlt]
    exact h ⟨i, hlt⟩ (fun he => hi (congrArg Fin.val he))
  · rw [ofFn_getD_ge x i (by omega), ofFn_getD_ge y i (by omega)]

theorem dc_dep_k (n : ℕ) (pre : List Gate) (k : ℕ) : (∀ g ∈ pre, g.inputs.length ≤ k + 1) →
    ∀ S : Finset ℕ, ∃ T : Finset ℕ, T.card ≤ k * pre.length + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ S
    exact ⟨S, by simp, fun x y _ _ h w hw => h w hw⟩
  | append_singleton pre g ih =>
    intro h2 S
    have h2p : ∀ g1 ∈ pre, g1.inputs.length ≤ k + 1 := fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg : g.inputs.length ≤ k + 1 := h2 g (by simp)
    have key : ∀ (T : Finset ℕ) (S1 : Finset ℕ), (∀ w ∈ S, w ≠ n + pre.length → w ∈ S1) →
        (n + pre.length ∈ S → ∀ i ∈ g.inputs, i ∈ S1) →
        (∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S1, (W pre x).getD w false = (W pre y).getD w false) →
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S, (W (pre ++ [g]) x).getD w false = (W (pre ++ [g]) y).getD w false := by
      intro T S1 hS1 hin hI x y hx hy hag w hw
      have hI2 := hI x y hx hy hag
      rw [W_snoc, W_snoc]
      have hlx : (W pre x).length = n + pre.length := by rw [W_length, hx]
      have hly : (W pre y).length = n + pre.length := by rw [W_length, hy]
      rcases lt_trichotomy w (n + pre.length) with hlt | heq | hgt
      · rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        exact hI2 w (hS1 w hw (by omega))
      · rw [step_last _ _ _ (by omega), step_last _ _ _ (by omega)]
        have hmap : (g.inputs.map fun i => (W pre x).getD i false)
            = (g.inputs.map fun i => (W pre y).getD i false) :=
          List.map_congr_left (fun i hi => hI2 i (hin (heq ▸ hw) i hi))
        rw [hmap]
      · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by rw [step_len]; omega)]
    by_cases hm : (n + pre.length) ∈ S
    · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ g.inputs.toFinset)
      refine ⟨T, ?_, key T _ ?_ ?_ hTv⟩
      · have h1 := Finset.card_union_le (S.erase (n + pre.length)) g.inputs.toFinset
        have h3 := List.toFinset_card_le g.inputs
        have h4 := Finset.card_erase_of_mem hm
        have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
        rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
        omega
      · intro w hw hne
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
      · intro _ i hi
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
    · obtain ⟨T, hT, hTv⟩ := ih h2p S
      refine ⟨T, ?_, key T S (fun w hw _ => hw) (fun h => absurd h hm) hTv⟩
      rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
      omega

theorem dc_sens_card {n : ℕ} (C : Circuit) (k : ℕ) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ k + 1)
    (K : Finset (Fin n))
    (hK : ∀ i ∈ K, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    K.card ≤ k * C.size + 1 := by
  obtain ⟨T, hT, hTv⟩ := dc_dep_k n C.gates k hfan {C.output}
  have hall : ∀ i ∈ K, i.val ∈ T := by
    intro i hi
    by_contra hk
    obtain ⟨x, y, hne, hxy⟩ := hK i hi
    have he := hTv (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (fun j hj => agree_ofFn x y i hxy j (fun h => hk (h ▸ hj))) C.output
      (Finset.mem_singleton_self _)
    exact hne he
  have hcard : K.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => hall i hi)
      (fun a _ b _ h => Fin.ext h)
  rw [Finset.card_singleton] at hT
  show K.card ≤ k * C.gates.length + 1
  omega

theorem dc_sens2 {n : ℕ} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (K : Finset (Fin n))
    (hK : ∀ i ∈ K, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    K.card ≤ C.size + 1 := by
  have h := dc_sens_card C 1 hfan K hK
  rw [Nat.one_mul] at h
  exact h

def pt (n a b : ℕ) : Fin (n + n) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n : ℕ) (u v : Fin n) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega

theorem rep_pt {n : ℕ} {A : Fin n → Fin n → Bool} {C : Circuit}
    (h : PEqualNP.Represents.Represents A C) (u v : Fin n) :
    circuitFun (n + n) C (pt n u.val (n + v.val)) = A u v := by
  rw [← h u v, oneEach_pt]
  rfl

def matrix (u v : Fin 5) : Bool := (25368609 : ℕ).testBit (5 * u.val + v.val)

def witness : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [11, 17]⟩], 18⟩

theorem upper : RepSizeAtMost matrix 9 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def eraseBit (x : Fin 10 → Bool) (i j : Fin 10) : Bool := x j && decide (j ≠ i)

theorem lower : ¬ RepSizeAtMost matrix 8 := by
  rintro ⟨C, hm, hs, hr⟩
  let K : Finset (Fin 10) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
  have cert : ∀ i ∈ K, ∃ a b c d : Fin 5,
      matrix a b = true ∧ matrix c d = false ∧
      ∀ j : Fin 10, eraseBit (pt 5 a.val (5 + b.val)) i j = true →
        pt 5 c.val (5 + d.val) j = true := by decide +kernel
  have bound := dc_sens2 C (fun g hg => (hm g hg).2) K (by
    intro i hi
    obtain ⟨a,b,c,d,ha,hb,hle⟩ := cert i hi
    let x := pt 5 a.val (5 + b.val)
    let y := eraseBit x i
    have hx : circuitFun 10 C x = true := (rep_pt hr a b).trans ha

    have hy : circuitFun 10 C y ≠ true := by
      intro h
      have wrong := circuitFun_mono 10 C (andOrOnly_of_monotone2 hm) y
        (pt 5 c.val (5 + d.val)) hle h
      rw [rep_pt hr c d, hb] at wrong
      contradiction
    refine ⟨x, y, fun h => hy (h ▸ hx), ?_⟩
    intro j hj
    simp [y, eraseBit, hj])
  have count : K.card = 10 := by decide
  omega

end PEqualNP.Outside.L_meta_20828_aux

theorem PEqualNP.Outside.L_meta_20828 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25368609 : ℕ).testBit (5 * u.val + v.val)) 9 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25368609 : ℕ).testBit (5 * u.val + v.val)) 8) := ⟨PEqualNP.Outside.L_meta_20828_aux.upper, PEqualNP.Outside.L_meta_20828_aux.lower⟩
