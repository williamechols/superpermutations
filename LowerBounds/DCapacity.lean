import LowerBounds.ComponentCapacityC

/-!
# Theorem D: chain lines and the capacity of a component (Lemma D1)

the written proof of Theorem D, section 3.  A *chain line* is a triple `(a, b, c)` such that every
exact weight-three chain `Q` of every strongly exitless path on `k` symbols has
`a r(Q) ≤ b δ(Q) + c` (`r` pieces, total deficit `δ`): `ChainLine k a b c`.

From a chain line this file proves the capacity of a strongly exitless path `p` with end prices
(`component_capacity_D`, Lemma D1):

  `2 a r(p) ≤ 2 b δ(p) + 2 c x⁺(p) + τ(p) + η(p)`,

where `x⁺` is the number of seams of weight at least 4 and `τ`, `η` are the prices of the first
and of the last piece: `c` for a full piece, `c + 2a - 2b d` for a partial piece of deficit `d` of
a path with at least two pieces, and `a - b d` for a path that is a single partial piece
(`priceD`).

No geometry is used beyond the partition of a path into chains
(`exists_componentExactWeightThreeChainPartition`) and the fact that a contiguous part of a chain
is a chain (`subchain`): the proof cuts off the end pieces and applies the line to the rest.

`Zone8` is the third hypothesis of the bound for 8 symbols; it is defined here next to
`ChainLine` and used in `D8.lean`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators

variable {k : ℕ} {p : HPath k}

/-- A chain line: `a r ≤ b δ + c` for every exact weight-three chain of every strongly exitless
path on `k` symbols, `r` its number of pieces and `δ` its total deficit. -/
def ChainLine (k a b c : ℕ) : Prop :=
  ∀ (p : HPath k), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
    a * chain.pieces.length ≤ b * (chain.pieces.map ComponentIntervalPiece.deficit).sum + c

/-- The zone statement for 8 symbols: an exact weight-three chain with `4 r - 9 δ ≥ 54` and
`17 r - 38 δ ≥ 258` has `4 r - 9 δ = 56`. -/
def Zone8 : Prop :=
  ∀ (p : HPath 8), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
    9 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 54 ≤ 4 * chain.pieces.length →
    38 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 258 ≤ 17 * chain.pieces.length →
    4 * chain.pieces.length = 9 * (chain.pieces.map ComponentIntervalPiece.deficit).sum + 56

/-! ### End prices -/

/-- The price of an end piece of deficit `dd` of a path with `r` pieces, for the line
`(a, b, c)`. -/
def priceD (a b c : ℕ) (dd r : ℕ) : ℤ :=
  if dd = 0 then (c : ℤ)
  else if r ≤ 1 then (a : ℤ) - (b : ℤ) * (dd : ℤ)
  else (c : ℤ) + 2 * (a : ℤ) - 2 * (b : ℤ) * (dd : ℤ)

section Price

variable {a b c : ℕ}

theorem priceD_zero (r : ℕ) : priceD a b c 0 r = (c : ℤ) := by
  unfold priceD
  rw [if_pos rfl]

theorem priceD_one {d : ℕ} (hd : d ≠ 0) {r : ℕ} (hr : r ≤ 1) :
    priceD a b c d r = (a : ℤ) - (b : ℤ) * (d : ℤ) := by
  unfold priceD
  rw [if_neg hd, if_pos hr]

theorem priceD_two {d : ℕ} (hd : d ≠ 0) {r : ℕ} (hr : 2 ≤ r) :
    priceD a b c d r = (c : ℤ) + 2 * (a : ℤ) - 2 * (b : ℤ) * (d : ℤ) := by
  unfold priceD
  rw [if_neg hd, if_neg (by omega)]

theorem priceD_eq_two (d : ℕ) {r : ℕ} (hr : 2 ≤ r) : priceD a b c d r = priceD a b c d 2 := by
  by_cases hd : d = 0
  · subst hd
    rw [priceD_zero, priceD_zero]
  · rw [priceD_two hd hr, priceD_two hd (le_refl 2)]

/-- An end never costs more than a full end. -/
theorem priceD_le (hab : a ≤ b) (d r : ℕ) : priceD a b c d r ≤ (c : ℤ) := by
  have hc : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  have habz : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
  by_cases hd : d = 0
  · subst hd
    rw [priceD_zero]
  · have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    have hm := mul_le_mul_of_nonneg_left hd1 hb
    by_cases hr : r ≤ 1
    · rw [priceD_one hd hr]
      linarith
    · rw [priceD_two hd (by omega)]
      linarith

end Price

/-! ### Lists of deficits -/

/-- The line holds for every non-empty contiguous part of the list of deficits. -/
def InfixLine (a b c : ℕ) (ds : List ℕ) : Prop :=
  ∀ L1 W L2 : List ℕ, ds = L1 ++ W ++ L2 → W ≠ [] → a * W.length ≤ b * W.sum + c

theorem firstNatValue_map {α : Type*} (f : α → ℕ) (xs : List α) :
    firstNatValue id (xs.map f) = firstNatValue f xs := by
  cases xs <;> rfl

theorem lastNatValue_map {α : Type*} (f : α → ℕ) (xs : List α) :
    lastNatValue id (xs.map f) = lastNatValue f xs := by
  unfold lastNatValue
  rw [← List.map_reverse]
  exact firstNatValue_map f _

theorem lastNatValue_concat (t : List ℕ) (y : ℕ) : lastNatValue id (t ++ [y]) = y := by
  simp [lastNatValue, firstNatValue]

section Lists

variable {a b c : ℕ}

/-- A chain with its first piece priced as an end of a longer path, the other end full. -/
theorem line_first (g : List ℕ) (hg : g ≠ []) (h : InfixLine a b c g) :
    2 * (a : ℤ) * ((g.length : ℕ) : ℤ) ≤
      2 * (b : ℤ) * ((g.sum : ℕ) : ℤ) + priceD a b c (firstNatValue id g) 2 + (c : ℤ) := by
  have hc : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hg
  have hf : firstNatValue id (x :: t) = x := rfl
  rw [hf]
  by_cases hx : x = 0
  · subst hx
    have h1 := h [] (0 :: t) [] (by simp) (by simp)
    simp only [List.length_cons, List.sum_cons] at h1 ⊢
    zify at h1
    rw [priceD_zero]
    push_cast
    linarith
  · rw [priceD_two hx (le_refl 2)]
    by_cases ht : t = []
    · subst ht
      simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      push_cast
      linarith
    · have h1 := h [x] t [] (by simp) ht
      simp only [List.length_cons, List.sum_cons]
      zify at h1
      push_cast
      linarith

/-- A chain with its last piece priced as an end of a longer path, the other end full. -/
theorem line_last (g : List ℕ) (hg : g ≠ []) (h : InfixLine a b c g) :
    2 * (a : ℤ) * ((g.length : ℕ) : ℤ) ≤
      2 * (b : ℤ) * ((g.sum : ℕ) : ℤ) + (c : ℤ) + priceD a b c (lastNatValue id g) 2 := by
  have hc : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  rcases ChainC.nil_or_concat g with rfl | ⟨t, y, rfl⟩
  · exact absurd rfl hg
  · rw [lastNatValue_concat]
    by_cases hy : y = 0
    · subst hy
      have h1 := h [] (t ++ [0]) [] (by simp) (by simp)
      simp only [List.length_append, List.sum_append, List.length_singleton,
        List.sum_singleton] at h1 ⊢
      zify at h1
      rw [priceD_zero]
      push_cast
      linarith
    · rw [priceD_two hy (le_refl 2)]
      by_cases ht : t = []
      · subst ht
        simp only [List.nil_append, List.length_singleton, List.sum_singleton]
        push_cast
        linarith
      · have h1 := h [] t [y] (by simp) ht
        simp only [List.length_append, List.sum_append, List.length_singleton,
          List.sum_singleton]
        zify at h1
        push_cast
        linarith

/-- A chain that is a whole path: both end pieces are priced. -/
theorem line_both (g : List ℕ) (hg : g ≠ []) (h : InfixLine a b c g) :
    2 * (a : ℤ) * ((g.length : ℕ) : ℤ) ≤
      2 * (b : ℤ) * ((g.sum : ℕ) : ℤ) + priceD a b c (firstNatValue id g) g.length +
        priceD a b c (lastNatValue id g) g.length := by
  have hc : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hg
  have hf : firstNatValue id (x :: t) = x := rfl
  rw [hf]
  rcases ChainC.nil_or_concat t with rfl | ⟨mid, y, rfl⟩
  · -- one piece
    have hl : lastNatValue id [x] = x := rfl
    rw [hl]
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    by_cases hx : x = 0
    · subst hx
      have h1 := h [] [0] [] (by simp) (by simp)
      simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at h1
      zify at h1
      rw [priceD_zero]
      push_cast
      linarith
    · rw [priceD_one hx (le_refl 1)]
      push_cast
      linarith
  · -- at least two pieces
    have hl : lastNatValue id (x :: (mid ++ [y])) = y := by
      rw [← List.cons_append]
      exact lastNatValue_concat _ _
    have hr : 2 ≤ (x :: (mid ++ [y])).length := by
      simp only [List.length_cons, List.length_append]
      omega
    rw [hl, priceD_eq_two x hr, priceD_eq_two y hr]
    simp only [List.length_cons, List.length_append, List.sum_cons, List.sum_append,
      List.length_nil, List.sum_nil]
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · subst hx
        subst hy
        have h1 := h [] (0 :: (mid ++ [0])) [] (by simp) (by simp)
        simp only [List.length_cons, List.length_append, List.sum_cons, List.sum_append,
          List.length_nil, List.sum_nil] at h1
        zify at h1
        rw [priceD_zero]
        push_cast
        linarith
      · subst hx
        have h1 := h [] (0 :: mid) [y] (by simp) (by simp)
        simp only [List.length_cons, List.sum_cons] at h1
        zify at h1
        rw [priceD_zero, priceD_two hy (le_refl 2)]
        push_cast
        linarith
    · by_cases hy : y = 0
      · subst hy
        have h1 := h [x] (mid ++ [0]) [] (by simp) (by simp)
        simp only [List.length_append, List.sum_append, List.length_singleton,
          List.sum_singleton] at h1
        zify at h1
        rw [priceD_zero, priceD_two hx (le_refl 2)]
        push_cast
        linarith
      · rw [priceD_two hx (le_refl 2), priceD_two hy (le_refl 2)]
        by_cases hm : mid = []
        · subst hm
          simp only [List.length_nil, List.sum_nil]
          push_cast
          linarith
        · have h1 := h [x] mid [y] (by simp) hm
          zify at h1
          push_cast
          linarith

/-- Chains in the middle of a path: each costs two full ends. -/
theorem groups_mid (a b c : ℕ) : ∀ (G : List (List ℕ)),
    (∀ g ∈ G, g ≠ [] ∧ InfixLine a b c g) →
    2 * (a : ℤ) * ((G.flatten.length : ℕ) : ℤ) ≤
      2 * (b : ℤ) * ((G.flatten.sum : ℕ) : ℤ) + 2 * (c : ℤ) * ((G.length : ℕ) : ℤ)
  | [], _ => by simp
  | g :: G, h => by
    have ih := groups_mid a b c G (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hne, hl⟩ := h g List.mem_cons_self
    have h1 := hl [] g [] (by simp) hne
    zify at h1
    simp only [List.flatten_cons, List.length_append, List.sum_append, List.length_cons]
    push_cast at ih ⊢
    linarith

/-- **Lemma D1 on lists.**  A list of deficits cut into non-empty groups, each of which
satisfies the line on all its parts: the two outer ends are priced, every cut costs two full
ends. -/
theorem groups_capacity (a b c : ℕ) (G : List (List ℕ)) (hG : G ≠ [])
    (h : ∀ g ∈ G, g ≠ [] ∧ InfixLine a b c g) :
    2 * (a : ℤ) * ((G.flatten.length : ℕ) : ℤ) + 2 * (c : ℤ) ≤
      2 * (b : ℤ) * ((G.flatten.sum : ℕ) : ℤ) + 2 * (c : ℤ) * ((G.length : ℕ) : ℤ) +
        priceD a b c (firstNatValue id G.flatten) G.flatten.length +
        priceD a b c (lastNatValue id G.flatten) G.flatten.length := by
  obtain ⟨g1, rest, rfl⟩ := List.exists_cons_of_ne_nil hG
  obtain ⟨hne1, hl1⟩ := h g1 List.mem_cons_self
  rcases List.eq_nil_or_concat rest with rfl | ⟨mid, gn, hrest⟩
  · -- one group
    have hb := line_both g1 hne1 hl1
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
      List.length_nil]
    push_cast at hb ⊢
    linarith
  · rw [List.concat_eq_append] at hrest
    subst hrest
    obtain ⟨hnen, hln⟩ := h gn (by simp)
    have hfirst : firstNatValue id (g1 :: (mid ++ [gn])).flatten = firstNatValue id g1 :=
      firstNatValue_flatten_cons id g1 _ hne1
    have hlast : lastNatValue id (g1 :: (mid ++ [gn])).flatten = lastNatValue id gn :=
      lastNatValue_flatten_of_reverse_cons id (g1 :: (mid ++ [gn])) gn (mid.reverse ++ [g1])
        hnen (by simp)
    have h1pos : 1 ≤ g1.length := List.length_pos_iff.mpr hne1
    have hnpos : 1 ≤ gn.length := List.length_pos_iff.mpr hnen
    have hflat : (g1 :: (mid ++ [gn])).flatten = g1 ++ (mid.flatten ++ gn) := by simp
    have hr : 2 ≤ (g1 :: (mid ++ [gn])).flatten.length := by
      rw [hflat, List.length_append, List.length_append]
      omega
    rw [hfirst, hlast, priceD_eq_two _ hr, priceD_eq_two _ hr, hflat]
    have hA := line_first g1 hne1 hl1
    have hB := line_last gn hnen hln
    have hM := groups_mid a b c mid (fun g hg => h g (by simp [hg]))
    simp only [List.length_append, List.sum_append, List.length_cons, List.length_nil]
    push_cast at hA hB hM ⊢
    linarith

end Lists

/-! ### Chains and paths -/

/-- A chain line holds for every contiguous part of a chain. -/
theorem infixLine_of_chainLine {a b c : ℕ} (hline : ChainLine k a b c)
    (hp : p.StronglyExitless) (chain : ExactWeightThreePieceChain p) :
    InfixLine a b c (chain.pieces.map ComponentIntervalPiece.deficit) := by
  intro L1 W L2 hD hW
  obtain ⟨P12, P3, hpieces, hP12, -⟩ := List.map_eq_append_iff.mp hD
  obtain ⟨P1, PW, rfl, -, hPW⟩ := List.map_eq_append_iff.mp hP12
  have hne : PW ≠ [] := by
    rintro rfl
    exact hW (by simpa using hPW.symm)
  have h := hline p hp (subchain chain P1 PW P3 hpieces hne)
  rw [subchain_pieces, hPW] at h
  rw [← hPW, List.length_map, hPW]
  exact h

/-- Price of the first piece of a strongly exitless path. -/
noncomputable def tailPriceD (a b c : ℕ) (p : HPath k) (hk : 1 ≤ k)
    (hp : p.StronglyExitless) : ℤ :=
  priceD a b c
    (firstNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp))
    (componentPieceCount p)

/-- Price of the last piece of a strongly exitless path. -/
noncomputable def headPriceD (a b c : ℕ) (p : HPath k) (hk : 1 ≤ k)
    (hp : p.StronglyExitless) : ℤ :=
  priceD a b c
    (lastNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp))
    (componentPieceCount p)

/-- **Lemma D1.**  The capacity of a strongly exitless path from a chain line, with end
prices; every seam of weight at least 4 costs two full ends. -/
theorem component_capacity_D {a b c : ℕ} (hk : 5 ≤ k) (hline : ChainLine k a b c)
    (hp : p.StronglyExitless) :
    2 * (a : ℤ) * (componentPieceCount p : ℤ) ≤
      2 * (b : ℤ) * (componentPieceDeficit p : ℤ) +
        2 * (c : ℤ) * ((componentPositiveSeams p).card : ℤ) +
        tailPriceD a b c p (by omega) hp + headPriceD a b c p (by omega) hp := by
  obtain ⟨chains, hflatten, hlength⟩ :=
    exists_componentExactWeightThreeChainPartition p (by omega) hp
  have hne : chains ≠ [] := by
    intro h
    rw [h] at hlength
    simp at hlength
  obtain ⟨G, hGdef⟩ : ∃ G : List (List ℕ),
      G = chains.map (fun Q => Q.pieces.map ComponentIntervalPiece.deficit) := ⟨_, rfl⟩
  have hGflat : G.flatten =
      (componentIntervalPieces p (by omega) hp).map ComponentIntervalPiece.deficit := by
    rw [hGdef, ← hflatten, List.map_flatten, List.map_map]
    rfl
  have hGne : G ≠ [] := by
    rw [hGdef]
    simpa using hne
  have hGall : ∀ g ∈ G, g ≠ [] ∧ InfixLine a b c g := by
    intro g hg
    rw [hGdef] at hg
    obtain ⟨Q, -, rfl⟩ := List.mem_map.mp hg
    exact ⟨by simpa using Q.nonempty, infixLine_of_chainLine hline hp Q⟩
  have hG := groups_capacity a b c G hGne hGall
  have hlen : G.flatten.length = componentPieceCount p := by
    rw [hGflat, List.length_map, componentIntervalPieces_length]
  have hsum : G.flatten.sum = componentPieceDeficit p := by
    rw [hGflat]
    exact componentIntervalPieces_totalDeficit (by omega) hp
  have hGl : G.length = (componentPositiveSeams p).card + 1 := by
    rw [hGdef, List.length_map, hlength]
  rw [hlen, hsum, hGl, hGflat, firstNatValue_map, lastNatValue_map] at hG
  unfold tailPriceD headPriceD
  push_cast at hG
  linarith

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.priceD_le
#print axioms SuperpermLowerBounds.groups_capacity
#print axioms SuperpermLowerBounds.component_capacity_D
