def hello := "world"

def join (f : α → α → β) (a : α) := f a a

def equaliser (f g : α → β) := {a : α // f a = g a}

variable (ι : X → Y)

class Cplx (α : Type u) where
  φ : (X → α) → Y → α
  sec : φ h (ι x) = h x
  proj : φ (λ_ ↦ a) x = a
  diag : φ (λx ↦ φ (hh x) y) y = φ (join hh) y
  braid : φ (λx ↦ φ (hh x) y') y = φ (λx ↦ φ (flip hh x) y) y'

export Cplx (φ sec proj diag braid)

instance [Cplx ι α] [Cplx ι β] : Cplx ι (α × β) where
  φ h y := (φ ι (λx ↦ (h x).1) y, φ ι (λx ↦ (h x).2) y)
  sec {h x} :=
    by repeat rw[sec]
  proj {a x} :=
    by repeat rw[proj]
  diag {hh y} :=
    by repeat rw[diag]
       rfl
  braid {hh y y'} :=
    by rw[braid]
       sorry
