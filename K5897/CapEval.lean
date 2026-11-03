import K5897.CapRules

/-!
# Evaluation by the kernel: the chain search on 7 symbols with the caps `Tcap` (0 to 72 holes)

One part; 12,976 calls of `go` by the C program `tools/f0.c`, which follows the same rules. No
Mathlib is loaded.
-/

namespace SuperpermLowerBounds
namespace K5897

theorem capEval : part (capRules [Tcap] 0 72 TB TK) 200 = false := by decide +kernel

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.capEval
