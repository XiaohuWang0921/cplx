def hello := "world"

open Function

def join (f : α → α → β) (a : α) := f a a

def Equaliser (f g : α → β) := {a // f a = g a}

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
    ext
    dsimp
    exact braid
    dsimp
    exact braid

instance {α : Type u} [Cplx ι β] : Cplx ι (α → β) where
  φ h y a := φ ι (flip h a) y
  sec := by
    intros
    funext a
    unfold flip
    exact sec
  proj := by
    intros
    funext a
    unfold flip
    exact proj
  diag := by
    intros
    funext a
    unfold flip
    exact diag
  braid := by
    intros
    funext a
    unfold flip
    exact braid

class Coh [Cplx ι α] [Cplx ι β] (f : α → β) where
  prf : φ ι (λx ↦ f (h x)) y = f (φ ι h y)

export Coh (prf)

instance [Cplx ι α] : Coh ι (id : α → α) where
  prf := by
    intros
    dsimp

instance [Cplx ι α] [Cplx ι β] [Cplx ι γ] [Coh ι (f : α → β)] [Coh ι (g : β → γ)] : Coh ι (g ∘ f) where
  prf := by
    intros
    dsimp
    rw[prf]
    rw[prf]

instance [Cplx ι β] [Cplx ι γ] [Coh ι (f : β → γ)] : Coh ι (@comp α β γ f) where
  prf := by
    intros
    funext a
    exact prf

instance [Cplx ι γ] : Coh ι (flip (@comp α β γ) (f : α → β)) where
  prf := by
    intros
    rfl

instance [Cplx ι γ] : Coh ι (@comp α β γ) where
  prf := by
    intros
    rfl

instance [Cplx ι α] [Cplx ι β] [Coh ι (f : α → β)] [Coh ι (g : α → β)] : Cplx ι (Equaliser f g) where
  φ h y := ⟨φ ι (λx ↦ (h x).val) y, by
    have inter : φ ι (λx ↦ f (h x).val) y = φ ι (λx ↦ g (h x).val) y := by
      congr
      funext x
      exact (h x).property

    rw[prf] at inter
    rw[inter]
    exact prf⟩

  sec := by
    unfold Equaliser
    intros
    ext
    exact sec

  proj := by
    unfold Equaliser
    intros
    ext
    exact proj

  diag := by
    unfold Equaliser
    intros
    ext
    exact diag

  braid := by
    unfold Equaliser
    intros
    ext
    exact braid
