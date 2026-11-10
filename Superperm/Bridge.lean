import Superperm.BridgeCore
import Hunter.Bounds

/-!
# The bridge, stated for the Hunter–Raudvere library itself

`Superperm/BridgeCore.lean` proves the bridge for three restated definitions.  Here the
library is imported (`Hunter.Bounds`, commit d452221) and the restatements are shown to be
the library's own definitions, by `rfl`; the bridge theorems follow for `Hunter.Ssuper`.
-/

namespace SuperpermBridge

open SuperpermutationBounds

theorem isPermWord_eq : @HR.IsPermWord = @Hunter.IsPermWord := rfl

theorem isSuperperm_eq : @HR.IsSuperperm = @Hunter.IsSuperperm := rfl

theorem ssuper_eq : @HR.Ssuper = @Hunter.Ssuper := rfl

/-- **Upper bounds transfer**: Pantone's `HasWord k L` is `Hunter.Ssuper k ≤ L`. -/
theorem hunter_hasWord_iff {k L : ℕ} (hk : 0 < k) : HasWord k L ↔ Hunter.Ssuper k ≤ L :=
  hasWord_iff hk

theorem hunter_ssuper_le_of_hasWord {k L : ℕ} (h : HasWord k L) : Hunter.Ssuper k ≤ L :=
  ssuper_le_of_hasWord h

/-- **Lower bounds transfer**: `L ≤ Hunter.Ssuper k` says that every covering word in
Pantone's sense has at least `L` letters. -/
theorem hunter_le_ssuper_iff {k L : ℕ} (hk : 0 < k) :
    L ≤ Hunter.Ssuper k ↔ ∀ w : List (Fin k), Covers w → L ≤ w.length :=
  le_ssuper_iff hk

/-- `Hunter.Ssuper k` is the least length of a covering word in Pantone's sense. -/
theorem hunter_ssuper_eq_sInf {k : ℕ} (hk : 0 < k) :
    Hunter.Ssuper k = sInf {m | ∃ w : List (Fin k), Covers w ∧ w.length = m} :=
  ssuper_eq_sInf hk

end SuperpermBridge

#print axioms SuperpermBridge.hunter_hasWord_iff
#print axioms SuperpermBridge.hunter_le_ssuper_iff
#print axioms SuperpermBridge.hunter_ssuper_eq_sInf
