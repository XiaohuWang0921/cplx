def hello := "world"

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
    intros h x
    rfl
  proj := by
    intros a x
    rfl
  diag := by
    intros hh y
    rfl
  braid := by
    intros hh y' y
    rfl

instance [Cplx ι α] [Cplx ι β] : Cplx ι (α × β) where
  φ h y := (φ ι (λx ↦ (h x).1) y, φ ι (λx ↦ (h x).2) y)
  sec := by
    intros h x
    repeat rw[sec]
  proj := by
    intros a x
    repeat rw[proj]
  diag := by
    intros hh y
    repeat rw[diag]
    rfl
  braid := by
    intros hh y' y
    ext
    dsimp
    exact braid
    dsimp
    exact braid

instance {α : Type u} [Cplx ι β] : Cplx ι (α → β) where
  φ h y a := φ ι (flip h a) y
  sec := by
    intros h x
    funext a
    unfold flip
    exact sec
  proj := by
    intros a x
    funext a
    unfold flip
    exact proj
  diag := by
    intros hh y
    funext a
    unfold flip
    exact diag
  braid := by
    intros hh y' y
    funext a
    unfold flip
    exact braid

class Coh [Cplx ι α] [Cplx ι β] (f : α → β) where
  coh : φ ι (λx ↦ f (h x)) y = f (φ ι h y)

export Coh (coh)

instance [Cplx ι α] : Coh ι (id : α → α) where
  coh := by
    intros h y
    dsimp

instance [Cplx ι α] [Cplx ι β] [Cplx ι γ] [Coh ι (f : α → β)] [Coh ι (g : β → γ)] : Coh ι (g ∘ f) where
  coh := by
    intros h y
    dsimp
    rw[coh]
    rw[coh]

instance [Cplx ι β] [Cplx ι γ] [Coh ι (f : β → γ)] : Coh ι (@f.comp α β γ) where
  coh := by
    intros h y
    funext a
    exact coh

instance [Cplx ι γ] : Coh ι (λ (g : β → γ) ↦ g.comp f) where
  coh := by
    intros h y
    rfl

instance [Cplx ι γ] : Coh ι (@Function.comp α β γ) where
  coh := by
    intros h y
    rfl

instance [Cplx ι α] [Cplx ι β] [Coh ι (f : α → β)] [Coh ι (g : α → β)] : Cplx ι (Equaliser f g) where
  φ h y := ⟨φ ι (λx ↦ (h x).val) y, calc
    f (φ ι (λx ↦ (h x).val) y) = φ ι (λx ↦ f (h x).val) y := coh.symm
    φ ι (λx ↦ f (h x).val) y = φ ι (λx ↦ g (h x).val) y := by
      congr
      funext x
      exact (h x).property
    φ  ι (λx ↦ g (h x).val) y = g (φ ι (λx ↦ (h x).val) y) := coh⟩

  sec := by
    unfold Equaliser
    intros h x
    ext
    exact sec

  proj := by
    unfold Equaliser
    intros a x
    ext
    exact proj

  diag := by
    unfold Equaliser
    intros hh y
    ext
    exact diag

  braid := by
    unfold Equaliser
    intros hh y' y
    ext
    exact braid

abbrev LeftSemiCoh [Cplx ι α] [Cplx ι γ] (f : α × β → γ) := Coh ι f.curry
abbrev RightSemiCoh [Cplx ι β] [Cplx ι γ] (f : α × β → γ) := Coh ι (λp ↦ f p.swap).curry

instance [Cplx ι α] [Cplx ι β] [Cplx ι γ] [Coh ι (f : α × β → γ)] : LeftSemiCoh ι f where
  coh := by
    intros h y
    unfold instCplxForall
    unfold flip
    funext b
    dsimp
    rw[coh]
    unfold instCplxProd
    dsimp
    congr
    exact proj

instance [Cplx ι α] [Cplx ι β] [Cplx ι γ] [Coh ι (f : α × β → γ)] : RightSemiCoh ι f where
  coh := by
    intros h y
    unfold instCplxForall
    unfold flip
    funext a
    dsimp
    rw[coh]
    unfold instCplxProd
    dsimp
    congr
    exact proj

instance [Cplx ι α] [Cplx ι β] [Cplx ι γ] [LeftSemiCoh ι (f : α × β → γ)] [RightSemiCoh ι f] : Coh ι f where
  coh {h y} := calc
    φ ι (λx ↦ f (h x)) y = φ ι (λx ↦ f.curry (h x).1 (h x).2) y := by rfl
    _ = φ ι (join (λx x' ↦ f.curry (h x).1 (h x').2)) y := by rfl
    _ = φ ι (λx ↦ φ ι (λx' ↦ f.curry (h x).1 (h x').2) y) y := diag.symm
    _ = φ ι (λx ↦ φ ι (λx' ↦ f ((h x').2, (h x).1).swap) y) y := by rfl
    _ = φ ι (λx ↦ φ ι (λx' ↦ (λp ↦ f p.swap).curry (h x').2 (h x).1) y) y := by rfl
    _ = φ ι (λx ↦ φ ι (λx' ↦ (λp ↦ f p.swap).curry (h x').2) y (h x).1) y := by rfl
    _ = φ ι (λx ↦ (λp ↦ f p.swap).curry (φ ι (λx' ↦ (h x').2) y) (h x).1) y := by
      congr
      rw[coh]
    _ = φ ι (λx ↦ f (φ ι (λx' ↦ (h x').2) y, (h x).1).swap) y := by rfl
    _ = φ ι (λx ↦ f ((h x).1, φ ι (λx' ↦ (h x').2) y)) y := by rfl
    _ = φ ι (λx ↦ f.curry (h x).1 (φ ι (λx' ↦ (h x').2) y)) y := by rfl
    _ = φ ι (λx ↦ f.curry (h x).1) y (φ ι (λx ↦ (h x).2) y) := by rfl
    _ = f.curry (φ ι (λx ↦ (h x).1) y) (φ ι (λx ↦ (h x).2) y) := by rw[coh]
    _ = f (φ ι (λx ↦ (h x).1) y, φ ι (λx ↦ (h x).2) y) := by rfl
    _ = f (φ ι (λx ↦ ((h x).1, (h x).2)) y) := by rfl
    _ = f (φ ι h y) := by rfl

instance [Cplx ι α] : Coh ι (φ ι : (X → α) → Y → α) where
  coh := by
    intros h y
    unfold instCplxForall
    dsimp
    funext y'
    exact braid

abbrev CH α β [Cplx ι α] [Cplx ι β] := @Equaliser (α → β) ((X → α) → Y → β) (λf h ↦ φ ι (f ∘ h)) (λf h ↦ f ∘ φ ι h)

instance [Cplx ι α] [Cplx ι β] {f : CH ι α β} : Coh ι f.val where
  coh {h y} := calc
    φ ι (λ x ↦ f.val (h x)) y = (λ f' h' ↦ φ ι (f' ∘ h')) f.val h y := by rfl
    _ = (λ f' h' ↦ f' ∘ φ ι h') f.val h y := by rw[f.property]
    _ = f.val (φ ι h y) := by rfl

def factorise [Cplx ι α] [Cplx ι β] (f : α → β) [Coh ι f] : CH ι α β := ⟨f, by
  funext h y
  dsimp
  unfold Function.comp
  rw[coh]⟩
