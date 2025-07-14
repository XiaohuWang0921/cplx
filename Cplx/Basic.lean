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

instance : Cplx ι Unit where
  φ _ _ := ()
  sec := by
    intros
    rfl
  proj := by
    intros
    rfl
  diag := by
    intros
    rfl
  braid := by
    intros
    rfl

instance [Cplx ι α] [Cplx ι β] : Cplx ι (α × β) where
  φ h y := (φ ι (λx ↦ (h x).1) y, φ ι (λx ↦ (h x).2) y)
  sec := by
    intros
    repeat rw[sec]
  proj := by
    intros
    repeat rw[proj]
  diag := by
    intros
    repeat rw[diag]
    rfl
  braid := by
    intros
    apply Prod.ext
    dsimp
    rw[braid]
    rfl
    dsimp
    rw[braid]
    rfl

instance {α : Type u} [Cplx ι β] : Cplx ι (α → β) where
  φ h y a := φ ι (flip h a) y
  sec:= by
    intros
    funext
    unfold flip
    rw[sec]
  proj := by
    intros
    funext
    unfold flip
    rw[proj]
  diag := by
    intros
    funext
    unfold flip
    rw[diag]
    rfl
  braid := by
    intros
    funext
    unfold flip
    rw[braid]
    rfl
