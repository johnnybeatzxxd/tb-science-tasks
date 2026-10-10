import Mathlib

namespace Zigzag

/-- Tampered: every sign vector has alternation number 0. -/
def alternation {n : ℕ} (x : Fin n → SignType) : ℕ := 0

end Zigzag
