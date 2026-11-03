import LowerBounds.PEnc
import K5897.Engine

/-!
# A third set of tables for the search of `PSearch.lean`, small enough for the kernel at 7 symbols

Halfar's set A computes everything from the codes of words, and its table of marks has `7 ^ 6`
entries; set B reads tables that are built from the list of all codes by `List.idxOf`. Neither is
fast in the kernel on 7 symbols. In set C a word is the rank of its code (`encR`, a Lehmer code),
and every entry is read from one natural number of `K5897/Tab.lean` with shifts, so that a step of
the search costs a few operations on big numbers; its classes are the numbers below 720, so the
table of marks has 720 entries.

`encC` proves `PS.Enc` for set C from six statements that the kernel evaluates (`decide +kernel`),
each a scan of the 5,040 words: the ranks (`rank_ok`, `rank_code_ok`), the classes (`ci_ok`), the
doors (`nxt_ok`), the successors of weight 3 (`bucket_ok`) and the first word (`st_ok`). The
successors of weight 4 and the list of all words are all 5,040 words; the search of a chain never
reads them.
-/

namespace SuperpermLowerBounds
namespace K5897

open PS
open S (PermW WLink DoorEq code)

/-! ### The tables (those of `Engine.lean`, and the rest of set C) -/

/-- The successors of weight 4: all words (the search of a chain never reads them). -/
def s4C (_ : ℕ) : List ℕ := List.range 5040

/-- All words. -/
def jlC : List ℕ := List.range 5040

/-- The word `1 2 … 7`. -/
def stC : ℕ := 0

/-! ### The coding: a word is the rank of its code -/

/-- Letter `i` of a code of 7 letters, from the left. -/
def dig (c i : ℕ) : ℕ := (c >>> (4 * (6 - i))) % 16

/-- The rank of a permutation code among all, in increasing order (its Lehmer code). -/
def rankC (c : ℕ) : ℕ :=
  (List.range 7).foldl (fun acc i =>
    acc * (7 - i) + ((List.range' (i + 1) (6 - i)).filter fun j => dig c j < dig c i).length) 0

/-- A word is the rank of its code. -/
def encR (u : List ℕ) : ℕ := rankC (code u)

/-! ### What the kernel checks -/

theorem rank_ok : (permCodes 7 7).all (fun c => decide (rankC c < 5040) && codeC (rankC c) == c)
    = true := by decide +kernel

theorem rank_code_ok : (List.range 5040).all (fun j => rankC (codeC j) == j) = true := by
  decide +kernel

theorem ci_ok : (List.range 5040).all (fun i =>
    cidxF 7 (4 * (7 - 1)) (16 ^ (7 - 1) - 1) (codeC i) ==
      cidxF 7 (4 * (7 - 1)) (16 ^ (7 - 1) - 1) (codeC (repC (ciC i)))) = true := by
  decide +kernel

theorem nxt_ok : (List.range 5040).all (fun i =>
    decide (nxtC i < 5040) &&
      codeC (nxtC i) == nxtF (4 * (7 - 1)) (16 ^ (7 - 1) - 1) (codeC i)) = true := by
  decide +kernel

theorem bucket_ok : (List.range 5040).all (fun j =>
    (bucket (key4 (codeC j / 16 ^ 3))).contains j) = true := by
  decide +kernel

theorem st_ok : stC = encR (List.range' 1 7) := by decide +kernel

/-! ### From the checks to `Enc` -/

theorem all_range {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) {i : ℕ} (hi : i < n) :
    f i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- The rank of a word, read back. -/
theorem code_encR {u : List ℕ} (hu : PermW 7 u) : encR u < 5040 ∧ codeC (encR u) = code u := by
  have h := List.all_eq_true.mp rank_ok (code u) (mem_perm (by norm_num) hu)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

/-- The rank of the word with the code of index `j` is `j`. -/
theorem encR_of_code {j : ℕ} (hj : j < 5040) {b : List ℕ} (hb : codeC j = code b) :
    encR b = j := by
  unfold encR
  rw [← hb]
  exact beq_iff_eq.mp (all_range rank_code_ok hj)

/-- **Set C satisfies `Enc`.** -/
theorem encC : Enc 7 encR ciC nxtC s3C s4C jlC stC where
  ci_inj := fun u v hu hv h => by
    obtain ⟨lu, cu⟩ := code_encR hu
    obtain ⟨lv, cv⟩ := code_encR hv
    have eu := beq_iff_eq.mp (all_range ci_ok lu)
    have ev := beq_iff_eq.mp (all_range ci_ok lv)
    rw [cu] at eu
    rw [cv] at ev
    rw [h] at eu
    exact (encA 7 (by norm_num) (by norm_num)).ci_inj u v hu hv (eu.trans ev.symm)
  nxt_eq := fun a b ha h => by
    obtain ⟨la, ca⟩ := code_encR ha
    have hn := all_range nxt_ok la
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hn
    obtain ⟨hlt, heq⟩ := hn
    rw [ca, nxtF_code (by norm_num) (by norm_num) ha h] at heq
    exact (encR_of_code hlt heq).symm
  s3_mem := fun u v hu hv h => by
    obtain ⟨lu, cu⟩ := code_encR hu
    obtain ⟨lv, cv⟩ := code_encR hv
    have ho := ovlF_of_wlink (by norm_num) (by norm_num) (by norm_num) hu hv h
    unfold ovlF at ho
    have ho' := beq_iff_eq.mp ho
    have hb := all_range bucket_ok lv
    unfold s3C exitKey
    rw [cu, ho', ← cv]
    exact List.elem_iff.mp hb
  s4_mem := fun u v hu hv _ => List.mem_range.mpr (code_encR hv).1
  jl_mem := fun v hv => List.mem_range.mpr (code_encR hv).1
  st_eq := st_ok

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.encC
