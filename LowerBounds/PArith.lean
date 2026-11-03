import LowerBounds.PTables
import LowerBounds.PModel

/-!
# The arithmetic for 5,899 (the written proof, sections 5 and 7)

Everything here is about the tables of `PTables.lean` and lists of numbers; no rows, no words.
The closed statements about the tables are proved by `decide +kernel` (evaluation in the kernel,
no `native_decide`).

* (B) `profile_of_family`: pairs `(holes, rows)` with `rows ≤ M holes`, `Σ (holes + 6) ≤ 84` and
  `Σ (rows - holes - 5) ≥ 50` contain one of the five profiles.
* (C) `many_chains`: at least 7 pairs with `Σ (holes + 6) ≤ 90` have `Σ (rows - holes - 5) ≤ 44`.
* (D) `sum_le_HB`, `kern`, `item_Z`, `item_A1`, `item_A`, `item_B`: the knapsack.
-/

namespace SuperpermLowerBounds
namespace T5899

/-- Chain cap. -/
def Mf (x : ℕ) : ℕ := Mtab.getD x 0

/-- Ring cap. -/
def PRf (x : ℕ) : ℕ := PRtab.getD x 0

/-- Cap for sequences with `s` links of weight 4. -/
def Pf (s x : ℕ) : ℕ := (Ptabs.getD s []).getD x 0

def Bf (W : ℕ) : ℕ := Btab.getD W 0

def Cf (n W : ℕ) : ℕ := (Ctab.getD n []).getD W 0

def hvf (w : ℕ) : ℕ := hvtab.getD w 0

def HBf (W : ℕ) : ℕ := HBtab.getD W 0

theorem Pf_zero (x : ℕ) : Pf 0 x = Mf x := rfl

/-! ### The closed statements about the tables -/

theorem M_mono : ∀ a < 85, ∀ b < 85, a ≤ b → Mf a ≤ Mf b := by decide +kernel

theorem B_closure : ∀ x < 79, ∀ W < 79, W + x + 6 ≤ 84 →
    Mf x + Bf W ≤ Bf (W + x + 6) + x + 5 := by decide +kernel

theorem B_mono : ∀ a < 85, ∀ b < 85, a ≤ b → Bf a ≤ Bf b := by decide +kernel

theorem B_tight : ∀ x < 79, 55 + x ≤ Mf x + Bf (78 - x) →
    (x = 14 ∨ x = 16 ∨ x = 26 ∨ x = 34 ∨ x = 36) := by decide +kernel

theorem B_eq : ∀ x < 79, (x = 14 ∨ x = 16 ∨ x = 26 ∨ x = 34 ∨ x = 36) →
    Mf x + Bf (78 - x) = 55 + x := by decide +kernel

theorem M_vals : Mf 14 = 31 ∧ Mf 16 = 34 ∧ Mf 26 = 50 ∧ Mf 34 = 63 ∧ Mf 36 = 66 := by
  decide +kernel

theorem C_closure : ∀ n < 8, ∀ x < 85, ∀ W < 85, 6 * n ≤ W → W + x + 6 ≤ 90 →
    Mf x + Cf n W ≤ Cf (min (n + 1) 7) (W + x + 6) + x + 5 := by decide +kernel

theorem C_top : ∀ W < 91, Cf 7 W ≤ 44 := by decide +kernel

theorem HB_closure : ∀ w < 85, ∀ W < 85, w + W ≤ 84 → hvf w + HBf W ≤ HBf (w + W) := by
  decide +kernel

theorem HB_mono : ∀ a < 85, ∀ b < 85, a ≤ b → HBf a ≤ HBf b := by decide +kernel

theorem item_Z : ∀ x < 85, 7 ≤ x → PRf (x - 7) + 1 ≤ hvf x + x := by decide +kernel

theorem item_A1 : ∀ x < 79, 1 ≤ x → PRf (x - 1) ≤ hvf (x + 6) + x + 5 := by decide +kernel

theorem item_A : ∀ q < 6, 2 ≤ q → ∀ x < 85, 1 ≤ x → x + 6 * q ≤ 84 →
    Pf (q - 2) (x - 1) ≤ hvf (x + 6 * q) + x + 5 * q := by decide +kernel

theorem item_B : ∀ q < 6, 1 ≤ q → ∀ x < 85, 7 ≤ x → x + 6 * q ≤ 84 →
    Pf (q - 1) (x - 7) + 1 ≤ hvf (x + 6 * q) + x + 5 * q := by decide +kernel

theorem kern : ∀ s < 6, ∀ x < 85, x + 6 * s ≤ 84 →
    Pf s x + HBf (84 - x - 6 * s) ≤ 49 + x + 5 * s := by decide +kernel

/-! ### Lists of pairs `(holes, rows)` -/

/-- `Σ (holes + 6)`. -/
def lW (l : List (ℕ × ℕ)) : ℕ := (l.map fun p => p.1 + 6).sum

/-- `Σ (rows - holes - 5)`. -/
def lE (l : List (ℕ × ℕ)) : ℤ := (l.map fun p => (p.2 : ℤ) - (p.1 : ℤ) - 5).sum

/-- Every pair has `rows ≤ M holes`. -/
def lOK (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, p.2 ≤ Mf p.1

theorem lW_nil : lW [] = 0 := rfl

theorem lE_nil : lE [] = 0 := rfl

theorem lW_cons (p : ℕ × ℕ) (l : List (ℕ × ℕ)) : lW (p :: l) = p.1 + 6 + lW l := by
  unfold lW
  rw [List.map_cons, List.sum_cons]

theorem lE_cons (p : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    lE (p :: l) = (p.2 : ℤ) - (p.1 : ℤ) - 5 + lE l := by
  unfold lE
  rw [List.map_cons, List.sum_cons]

theorem lW_ge : ∀ l : List (ℕ × ℕ), 6 * l.length ≤ lW l
  | [] => by simp [lW]
  | p :: l => by
      have ih := lW_ge l
      rw [lW_cons, List.length_cons]
      omega

theorem lE_le_B : ∀ l : List (ℕ × ℕ), lOK l → lW l ≤ 84 → lE l ≤ (Bf (lW l) : ℤ)
  | [], _, _ => by
      rw [lE_nil]
      exact Int.natCast_nonneg _
  | p :: l, hok, hW => by
      rw [lW_cons] at hW
      have ih := lE_le_B l (fun q hq => hok q (List.mem_cons_of_mem _ hq)) (by omega)
      have hp := hok p List.mem_cons_self
      have hc := B_closure p.1 (by omega) (lW l) (by omega) (by omega)
      have e : lW l + p.1 + 6 = p.1 + 6 + lW l := by omega
      rw [e] at hc
      rw [lW_cons, lE_cons]
      omega

theorem lW_erase {l : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ l) :
    lW l = p.1 + 6 + lW (l.erase p) := by
  rw [← lW_cons]
  unfold lW
  exact ((List.perm_cons_erase hp).map _).sum_eq

theorem lE_erase {l : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ l) :
    lE l = (p.2 : ℤ) - (p.1 : ℤ) - 5 + lE (l.erase p) := by
  rw [← lE_cons]
  unfold lE
  exact ((List.perm_cons_erase hp).map _).sum_eq

/-- One of the five kinds of chains of the profiles. -/
def InS (p : ℕ × ℕ) : Prop :=
  p = (14, 31) ∨ p = (16, 34) ∨ p = (26, 50) ∨ p = (34, 63) ∨ p = (36, 66)

theorem mem_tight {l : List (ℕ × ℕ)} (hok : lOK l) (hW : lW l ≤ 84) (hE : 50 ≤ lE l)
    {p : ℕ × ℕ} (hp : p ∈ l) : InS p := by
  have h1 := lW_erase hp
  have h2 := lE_erase hp
  have hok' : lOK (l.erase p) := fun q hq => hok q (List.mem_of_mem_erase hq)
  have h3 := lE_le_B _ hok' (by omega)
  have hx : p.1 < 79 := by omega
  have h4 := B_mono (lW (l.erase p)) (by omega) (78 - p.1) (by omega) (by omega)
  have h5 := hok p hp
  have h6 := B_tight p.1 hx (by omega)
  have h7 := B_eq p.1 hx h6
  have hr : p.2 = Mf p.1 := by omega
  obtain ⟨m14, m16, m26, m34, m36⟩ := M_vals
  obtain ⟨x, r⟩ := p
  simp only at hr h6
  subst hr
  unfold InS
  rcases h6 with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by rw [m14])
  · exact Or.inr (Or.inl (by rw [m16]))
  · exact Or.inr (Or.inr (Or.inl (by rw [m26])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [m34]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [m36]))))

theorem lW_counts : ∀ l : List (ℕ × ℕ), (∀ p ∈ l, InS p) →
    lW l = 20 * l.count (14, 31) + 22 * l.count (16, 34) + 32 * l.count (26, 50) +
        40 * l.count (34, 63) + 42 * l.count (36, 66) ∧
      lE l = 12 * (l.count (14, 31) : ℤ) + 13 * (l.count (16, 34) : ℤ) +
        19 * (l.count (26, 50) : ℤ) + 24 * (l.count (34, 63) : ℤ) + 25 * (l.count (36, 66) : ℤ)
  | [], _ => by simp [lW, lE]
  | p :: l, h => by
      obtain ⟨ih1, ih2⟩ := lW_counts l (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rcases h p List.mem_cons_self with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [lW_cons, lE_cons]
         simp
         constructor <;> omega)

/-- **(B).**  A list of pairs with `rows ≤ M holes`, weight at most 84 and value at least 50
contains one of the five profiles. -/
theorem profile_of_family {l : List (ℕ × ℕ)} (hok : lOK l) (hW : lW l ≤ 84) (hE : 50 ≤ lE l) :
    2 ≤ l.count (36, 66) ∨ 2 ≤ l.count (26, 50) ∨
      (1 ≤ l.count (34, 63) ∧ 1 ≤ l.count (16, 34)) ∨
      (1 ≤ l.count (36, 66) ∧ 1 ≤ l.count (14, 31)) ∨
      (2 ≤ l.count (14, 31) ∧ 2 ≤ l.count (16, 34)) := by
  obtain ⟨h1, h2⟩ := lW_counts l (fun p hp => mem_tight hok hW hE hp)
  rw [h1] at hW
  rw [h2] at hE
  generalize l.count (14, 31) = a at hW hE ⊢
  generalize l.count (16, 34) = b at hW hE ⊢
  generalize l.count (26, 50) = c at hW hE ⊢
  generalize l.count (34, 63) = d at hW hE ⊢
  generalize l.count (36, 66) = f at hW hE ⊢
  have ha : a ≤ 4 := by omega
  have hb : b ≤ 3 := by omega
  have hc : c ≤ 2 := by omega
  have hd : d ≤ 2 := by omega
  have hf : f ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    interval_cases f <;> omega

theorem lE_le_C : ∀ l : List (ℕ × ℕ), lOK l → (∀ p ∈ l, p.1 ≤ 84) → lW l ≤ 90 →
    lE l ≤ (Cf (min l.length 7) (lW l) : ℤ)
  | [], _, _, _ => by
      rw [lE_nil]
      exact Int.natCast_nonneg _
  | p :: l, hok, hx, hW => by
      rw [lW_cons] at hW
      have ih := lE_le_C l (fun q hq => hok q (List.mem_cons_of_mem _ hq))
        (fun q hq => hx q (List.mem_cons_of_mem _ hq)) (by omega)
      have hp := hok p List.mem_cons_self
      have hxp := hx p List.mem_cons_self
      have hge := lW_ge l
      have hc := C_closure (min l.length 7) (by omega) p.1 (by omega) (lW l) (by omega)
        (by omega) (by omega)
      have e1 : min (min l.length 7 + 1) 7 = min (l.length + 1) 7 := by omega
      have e2 : lW l + p.1 + 6 = p.1 + 6 + lW l := by omega
      rw [e1, e2] at hc
      rw [lW_cons, lE_cons, List.length_cons]
      omega

/-- **(C).**  At least 7 pairs with weight at most 90 have value at most 44. -/
theorem many_chains {l : List (ℕ × ℕ)} (hok : lOK l) (hx : ∀ p ∈ l, p.1 ≤ 84) (hW : lW l ≤ 90)
    (h7 : 7 ≤ l.length) : lE l ≤ 44 := by
  have h := lE_le_C l hok hx hW
  have e : min l.length 7 = 7 := by omega
  rw [e] at h
  have ht := C_top (lW l) (by omega)
  omega

/-- **(D), the hanging part.**  Components whose values are bounded by the item table have
total value at most `HB` of their total weight. -/
theorem sum_le_HB {α : Type*} (v : α → ℤ) (w : α → ℕ) : ∀ Hs : List α,
    (∀ H ∈ Hs, v H ≤ (hvf (w H) : ℤ)) → (Hs.map w).sum ≤ 84 →
    (Hs.map v).sum ≤ (HBf ((Hs.map w).sum) : ℤ)
  | [], _, _ => by
      simp only [List.map_nil, List.sum_nil]
      exact Int.natCast_nonneg _
  | H :: Hs, hv, hW => by
      rw [List.map_cons, List.sum_cons] at hW
      have ih := sum_le_HB v w Hs (fun H' hH' => hv H' (List.mem_cons_of_mem _ hH')) (by omega)
      have h1 := hv H List.mem_cons_self
      have hc := HB_closure (w H) (by omega) ((Hs.map w).sum) (by omega) hW
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      omega

end T5899
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.T5899.profile_of_family
#print axioms SuperpermLowerBounds.T5899.many_chains
#print axioms SuperpermLowerBounds.T5899.sum_le_HB
#print axioms SuperpermLowerBounds.T5899.kern
#print axioms SuperpermLowerBounds.T5899.item_A
#print axioms SuperpermLowerBounds.T5899.item_B
