import LowerBounds.PRules
import LowerBounds.PTheorem

/-!
# 5,899 for 7 symbols, from search equations

`covers_5899_of_search`: every word over `Fin 7` that contains all permutations has at least
5,899 letters, if twelve searches of `PSearch.lean` answer `false`:

* F0 … F5: `PS.seqSearch 7 Ptabs s 0 (84 - 6 s) …` for `s = 0, …, 5` (sequences with `s` links of
  weight 4; `s = 0`: chains);
* FR: `PS.ringSearch 7 Mtab PRtab 77 …`;
* FF: `PS.profSearch 7 Mtab ts …` for the five profiles `ts`.

A search may be evaluated in parts: `PS.Covered nt f` says that every part `tp < nt` lies in a
range `pa ≤ tp < pb` for which `f pa pb = false` holds.  The fuel, the depth of the gate and the
number of parts of every search are arbitrary.

No `native_decide` here: the equations are hypotheses.  `PFinalNative.lean` supplies them.
-/

namespace SuperpermLowerBounds

open T5899

namespace PS

/-- Every part `tp < nt` of a search lies in a range of parts that answers `false`. -/
def Covered (nt : ℕ) (f : ℕ → ℕ → Bool) : Prop :=
  ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧ f pa pb = false

/-- A search evaluated in one range. -/
theorem covered_one {nt : ℕ} {f : ℕ → ℕ → Bool} (h : f 0 nt = false) : Covered nt f :=
  fun tp htp => ⟨0, nt, Nat.zero_le tp, htp, h⟩

theorem SeqCapLt.mono {k s : ℕ} {P : ℕ → ℕ} {b b' : ℕ} (h : SeqCapLt k s P b') (hb : b ≤ b') :
    SeqCapLt k s P b :=
  fun L h1 h2 h3 h4 => h L h1 h2 h3 (by omega)

theorem seqCapLt_zero (k s : ℕ) (P : ℕ → ℕ) : SeqCapLt k s P 0 :=
  fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)

end PS

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}

/-- The caps for sequences on words, from the six searches F0 … F5. -/
theorem seqCaps_of_search (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅)
    (h0 : PS.Covered n₀ (PS.seqSearch 7 Ptabs 0 0 84 f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (PS.seqSearch 7 Ptabs 1 0 78 f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (PS.seqSearch 7 Ptabs 2 0 72 f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (PS.seqSearch 7 Ptabs 3 0 66 f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (PS.seqSearch 7 Ptabs 4 0 60 f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (PS.seqSearch 7 Ptabs 5 0 54 f₅ d₅ n₅)) :
    PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 ∧ PS.SeqCapLt 7 1 (PS.capF Ptabs 1) 79 ∧
      PS.SeqCapLt 7 2 (PS.capF Ptabs 2) 73 ∧ PS.SeqCapLt 7 3 (PS.capF Ptabs 3) 67 ∧
      PS.SeqCapLt 7 4 (PS.capF Ptabs 4) 61 ∧ PS.SeqCapLt 7 5 (PS.capF Ptabs 5) 55 := by
  have c0 : PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 :=
    PS.seqCap_of_search (by norm_num) (by norm_num) hn₀ (fun j hj => absurd hj (Nat.not_lt_zero j))
      (PS.seqCapLt_zero _ _ _) h0
  have c1 : PS.SeqCapLt 7 1 (PS.capF Ptabs 1) 79 :=
    PS.seqCap_of_search (by norm_num) (by norm_num) hn₁
      (fun j hj => by
        interval_cases j
        exact c0.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h1
  have c2 : PS.SeqCapLt 7 2 (PS.capF Ptabs 2) 73 :=
    PS.seqCap_of_search (by norm_num) (by norm_num) hn₂
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h2
  have c3 : PS.SeqCapLt 7 3 (PS.capF Ptabs 3) 67 :=
    PS.seqCap_of_search (by norm_num) (by norm_num) hn₃
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num)
        · exact c2.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h3
  have c4 : PS.SeqCapLt 7 4 (PS.capF Ptabs 4) 61 :=
    PS.seqCap_of_search (by norm_num) (by norm_num) hn₄
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num)
        · exact c2.mono (by norm_num)
        · exact c3.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h4
  have c5 : PS.SeqCapLt 7 5 (PS.capF Ptabs 5) 55 :=
    PS.seqCap_of_search (by norm_num) (by norm_num) hn₅
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num)
        · exact c2.mono (by norm_num)
        · exact c3.mono (by norm_num)
        · exact c4.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h5
  exact ⟨c0, c1, c2, c3, c4, c5⟩

/-- The table of F0 is the table `Mtab`. -/
theorem capF_zero : PS.capF Ptabs 0 = fun x => Mtab.getD x 0 := rfl

/-- **`Caps`, from the searches F0 … F5 and FR.** -/
theorem caps_of_search (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR)
    (h0 : PS.Covered n₀ (PS.seqSearch 7 Ptabs 0 0 84 f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (PS.seqSearch 7 Ptabs 1 0 78 f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (PS.seqSearch 7 Ptabs 2 0 72 f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (PS.seqSearch 7 Ptabs 3 0 66 f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (PS.seqSearch 7 Ptabs 4 0 60 f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (PS.seqSearch 7 Ptabs 5 0 54 f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR)) : Caps := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := seqCaps_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ h0 h1 h2 h3 h4 h5
  refine ⟨?_, ?_, ?_⟩
  · exact PS.chainCapK_of_wcap (PS.wcap_of_seqCap c0)
  · intro s hs1 hs5
    interval_cases s
    · exact PS.pathCapK_of_seqCap c1
    · exact PS.pathCapK_of_seqCap c2
    · exact PS.pathCapK_of_seqCap c3
    · exact PS.pathCapK_of_seqCap c4
    · exact PS.pathCapK_of_seqCap c5
  · have hM : PS.SeqCapLt 7 0 (fun x => Mtab.getD x 0) (77 + 1) := by
      rw [← capF_zero]
      exact c0.mono (by norm_num)
    exact PS.ringCapK_of_ringCapT
      (PS.ringCapT_of_search (by norm_num) (by norm_num) hnR hM hR)

variable {fa da na fb db nb fc dc nc fd dd nd fe de ne : ℕ}

/-- **`Profiles`, from the search F0 and the five searches FF.** -/
theorem profiles_of_search (hn₀ : 0 < n₀) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc)
    (hnd : 0 < nd) (hne : 0 < ne)
    (h0 : PS.Covered n₀ (PS.seqSearch 7 Ptabs 0 0 84 f₀ d₀ n₀))
    (ha : PS.Covered na (PS.profSearch 7 Mtab [(66, 36), (66, 36)] fa da na))
    (hb : PS.Covered nb (PS.profSearch 7 Mtab [(50, 26), (50, 26)] fb db nb))
    (hc : PS.Covered nc (PS.profSearch 7 Mtab [(63, 34), (34, 16)] fc dc nc))
    (hd : PS.Covered nd (PS.profSearch 7 Mtab [(66, 36), (31, 14)] fd dd nd))
    (he : PS.Covered ne (PS.profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne)) :
    Profiles := by
  have c0 : PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 :=
    PS.seqCap_of_search (by norm_num) (by norm_num) hn₀ (fun j hj => absurd hj (Nat.not_lt_zero j))
      (PS.seqCapLt_zero _ _ _) h0
  have hM : PS.WCap 7 (fun x => Mtab.getD x 0) 36 := by
    rw [← capF_zero]
    exact PS.wcap_of_seqCap (c0.mono (by norm_num))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hna hM (by decide) (by decide) ha
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hnb hM (by decide) (by decide) hb
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hnc hM (by decide) (by decide) hc
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hnd hM (by decide) (by decide) hd
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hne hM (by decide) (by decide) he

/-- **Every word over `Fin 7` that contains all permutations has at least 5,899 letters**, if
the twelve searches answer `false`. -/
theorem covers_5899_of_search (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc)
    (hnd : 0 < nd) (hne : 0 < ne)
    (h0 : PS.Covered n₀ (PS.seqSearch 7 Ptabs 0 0 84 f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (PS.seqSearch 7 Ptabs 1 0 78 f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (PS.seqSearch 7 Ptabs 2 0 72 f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (PS.seqSearch 7 Ptabs 3 0 66 f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (PS.seqSearch 7 Ptabs 4 0 60 f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (PS.seqSearch 7 Ptabs 5 0 54 f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR))
    (ha : PS.Covered na (PS.profSearch 7 Mtab [(66, 36), (66, 36)] fa da na))
    (hb : PS.Covered nb (PS.profSearch 7 Mtab [(50, 26), (50, 26)] fb db nb))
    (hc : PS.Covered nc (PS.profSearch 7 Mtab [(63, 34), (34, 16)] fc dc nc))
    (hd : PS.Covered nd (PS.profSearch 7 Mtab [(66, 36), (31, 14)] fd dd nd))
    (he : PS.Covered ne (PS.profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne)) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5899 ≤ w.length :=
  covers_5899_of_caps (caps_of_search hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR)
    (profiles_of_search hn₀ hna hnb hnc hnd hne h0 ha hb hc hd he)

end

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.caps_of_search
#print axioms SuperpermLowerBounds.profiles_of_search
#print axioms SuperpermLowerBounds.covers_5899_of_search
