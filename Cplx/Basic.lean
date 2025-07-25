def hello := "world"

open Function Prod Subtype

def join (f : α → α → β) (a : α) := f a a

def Equaliser (f g : α → β) := {a // f a = g a}

section Single

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
    repeat rw[coh]

instance [Cplx ι β] [Cplx ι γ] [Coh ι (f : β → γ)] : Coh ι (@f.comp α) where
  coh := by
    intros h y
    funext a
    exact coh

instance [Cplx ι γ] : Coh ι (flip (@comp α β γ) f) where
  coh := by
    intros h y
    rfl

instance [Cplx ι γ] : Coh ι (@comp α β γ) where
  coh := by
    intros h y
    rfl

instance [Cplx ι α] [Cplx ι β] : Coh ι (@fst α β) where
  coh := by
    intros h y
    unfold instCplxProd
    dsimp

instance [Cplx ι α] [Cplx ι β] : Coh ι (@snd α β) where
  coh := by
    intros h y
    unfold instCplxProd
    dsimp

instance [Cplx ι α] [Cplx ι β] [Coh ι (f : α → β)] [Coh ι (g : α → β)] : Cplx ι (Equaliser f g) where
  φ h y := ⟨φ ι (val ∘ h) y, calc
    f (φ ι (val ∘ h) y) = φ ι (λx ↦ f (h x).val) y := coh.symm
    φ ι (λx ↦ f (h x).val) y = φ ι (λx ↦ g (h x).val) y := by
      congr
      funext x
      exact (h x).property
    φ  ι (λx ↦ g (h x).val) y = g (φ ι (val ∘ h) y) := coh⟩

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

instance [Cplx ι α] : Coh ι (φ ι : (X → α) → Y → α) where
  coh := by
    intros h y
    unfold instCplxForall
    dsimp
    funext y'
    exact braid

abbrev CH α β [Cplx ι α] [Cplx ι β] := @Equaliser (α → β) ((X → α) → Y → β) ((φ ι).comp ∘ comp) (flip comp (φ ι) ∘ comp)

instance [Cplx ι α] [Cplx ι β] {f : CH ι α β} : Coh ι f.val where
  coh {h y} := calc
    φ ι (λ x ↦ f.val (h x)) y = ((φ ι).comp ∘ comp) f.val h y := by rfl
    _ = (flip comp (φ ι) ∘ comp) f.val h y := by rw[f.property]
    _ = f.val (φ ι h y) := by rfl

def factorise [Cplx ι α] [Cplx ι β] (f : α → β) [Coh ι f] : CH ι α β := ⟨f, by
  funext h y
  dsimp
  unfold comp flip
  rw[coh]⟩

def cohcurry [Cplx ι α] [Cplx ι β] [Cplx ι γ] (f : α × β → γ) [Coh ι f] (a : α) : CH ι β γ := ⟨f.curry a, by
  funext h y
  unfold curry comp flip
  dsimp
  rw[coh]
  unfold instCplxProd
  dsimp
  rw[proj]⟩

instance [Cplx ι α] [Cplx ι β] [Cplx ι γ] [Coh ι (f : α × β → γ)] : Coh ι (cohcurry ι f) where
  coh := by
    intros h y
    unfold cohcurry curry CH Equaliser instCplxEqualiserOfCoh instCplxForall flip
    ext
    dsimp
    rw[coh]
    unfold instCplxProd
    dsimp
    rw[proj]

def cohuncurry [Cplx ι α] [Cplx ι β] [Cplx ι γ] (f : α → CH ι β γ) [Coh ι f] (p : α × β) : γ := (f p.1).val p.2

instance  [Cplx ι α] [Cplx ι β] [Cplx ι γ] {f : α → CH ι β γ} [Coh ι f] : Coh ι (cohuncurry ι f) where
  coh {h y} := calc
    φ ι (λ x ↦ cohuncurry ι f (h x)) y = φ ι (λ x ↦ (f (h x).1).val (h x).2) y := by rfl
    _ = φ ι (join λ x x' ↦ (f (h x).1).val (h x').2) y := by rfl
    _ = φ ι (λ x ↦ φ ι (λ x' ↦ (f (h x).1).val (h x').2) y) y := by rw[diag]
    _ = φ ι (λ x ↦ (f (h x).1).val (φ ι (λ x' ↦ (h x').2) y)) y := by
      congr
      funext x
      exact coh
    _ = φ ι (λ x ↦ (f (h x).1).val) y (φ ι (λ x ↦ (h x).2) y) := by rfl
    _ = (φ ι (λ x ↦ f (h x).1) y).val (φ ι (λ x ↦ (h x).2) y) := by rfl
    _ = (f (φ ι (λ x ↦ (h x).1) y)).val (φ ι (λ x ↦ (h x).2) y) := by rw[coh]
    _ = (f (φ ι h y).1).val (φ ι h y).2 := by rfl
    _ = cohuncurry ι f (φ ι h y) := by rfl

section Double

variable (η : U → V) (μ : U → X) (ε : X → U) (ν : V → Y)
variable (split : ∀ u, ε (μ u) = u) (square : ∀ u, ν (η u) = ι (μ u))

-- Can't write the following as instances because Lean's too weak to deal with my wisdom.

def cplx_eta [Cplx ι α] : Cplx η α where
  φ h v := φ ι (h ∘ ε) (ν v)
  sec := by
    intros h u
    rw[square]
    unfold comp
    rw[sec]
    rw[split]
  proj := proj
  diag := diag
  braid := braid

def coh_eta [Cplx ι α] [Cplx ι β] [Coh ι (f : α → β)] : @Coh _ _ η _ _ (cplx_eta ι η μ ε ν split square) (cplx_eta ι η μ ε ν split square) f :=
  @Coh.mk _ _ η _ _ (cplx_eta ι η μ ε ν split square) (cplx_eta ι η μ ε ν split square) f (by
    intros
    unfold cplx_eta comp
    dsimp
    exact coh)

end Double

end Single
