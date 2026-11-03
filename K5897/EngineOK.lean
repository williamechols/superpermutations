import K5897.Enc

/-!
# The tables of the engine mean what they say

What `K5897/Sound.lean` needs about the tables of `Engine.lean`, from `K5897.encC`: the coding
`enc` (the rank of the code of a word) is below 5,040 on permutation words, words with the same
class are rotations of each other, `nxtC` is the door, the six numbers `s3 i j` contain the
successors of weight 3, and `1 2 3 4 5 6 7` has index 0. These are the facts of Halfar's
`K6/TabOK.lean` that `K6/Sound.lean` uses, for 7 symbols.
-/

namespace SuperpermLowerBounds
namespace K5897

open S (PermW WLink DoorEq)

/-- The coding of words used by the engine. -/
abbrev enc (w : List ℕ) : ℕ := encR w

theorem enc_lt {w : List ℕ} (hw : PermW 7 w) : enc w < 5040 := (code_encR hw).1

/-- Words with the same class index are rotations of each other. -/
theorem ci_rot {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v) (h : ciC (enc u) = ciC (enc v)) :
    u ~r v :=
  encC.ci_inj u v hu hv h

/-- **`nxtC` is the door of the exit.** -/
theorem nx_enc {a b : List ℕ} (ha : PermW 7 a) (h : DoorEq 7 a b) : nxtC (enc a) = enc b :=
  encC.nxt_eq a b ha h

/-- **`s3` lists the successors of weight 3.** -/
theorem s3_enc {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v) (h : WLink 7 3 u v) :
    ∃ j, j < 6 ∧ s3 (enc u) j = enc v := by
  have hm := encC.s3_mem u v hu hv h
  unfold s3C bucket at hm
  obtain ⟨j, hj, hjv⟩ := List.mem_map.mp hm
  exact ⟨j, List.mem_range.mp hj, hjv⟩

theorem enc_id : enc [1, 2, 3, 4, 5, 6, 7] = 0 := st_ok.symm

end K5897
end SuperpermLowerBounds
