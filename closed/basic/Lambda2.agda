module Lambda2 where

open import Function
open import Data.Nat hiding (_<_)
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


data Ty : Set where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  zero : ∀{Γ σ} → Var (Γ < σ) σ
  suc  : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ 

data Tm (Γ : Con) : Ty → Set where 
  var : ∀{σ} → Var Γ σ → Tm Γ σ
  lam : ∀{σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
  app : ∀{σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ

Val : Ty → Set
Val ι    = ℕ
Val (σ ⇒ τ) = Val σ → Val τ

Env : Con → Set
Env Γ = ∀{σ} → Var Γ σ → Val σ


_<<_ : ∀{Γ} → Env Γ → ∀{σ} → Val σ → Env (Γ < σ)
(γ << v) zero = v
(γ << v) (suc x) = γ x 

-- notice that I have written it with 3 explicit arguments rather than
-- two, this is because Env computes to:

-- ∀{Γ} → (∀{σ} → Var Γ σ → Val σ) → ∀{σ} → Val σ → ∀{σ'} → 
-- Var (Γ < σ) σ' → Val σ'

-- which has three explicit arguments.

-- Notice also that the definition of _<<_ looks a bit like lookup ,
-- this is because the new definition of Env is a lookup function in a
-- way, so to define a new longer environment we need to explain how
-- to lockup variables in it.

eval : ∀{Γ σ} → Env Γ → Tm Γ σ → Val σ
eval γ (var t) = γ t
eval γ (lam t) = λ x → eval (γ << x) t
eval γ (app t t') = eval γ t (eval γ t')


-- We are working towards substitution - the operation of replacing
-- variables by terms in a term. First we'll look at renaming which is
-- a simpler function that replaces variables by variables.

-- the type of renamings: functions mapping variables in one context to
-- variables in another

Ren : Con → Con → Set
Ren Δ Γ = ∀{σ} → Var Δ σ → Var Γ σ

-- weakening, takes a existing renaming ρ, and adds a new 0
-- variable. 0 is mapped to 0, for everything else the ρ renaming is
-- used and then incremented by 1.

wk : ∀{Γ Δ σ} → Ren Δ Γ → Ren (Δ < σ) (Γ < σ)
wk ρ zero = zero
wk ρ (suc y) = suc (ρ y)

-- apply a renaming to a term, wk is needed to push the renaming inside 
-- a lambda term. i.e. lambda binds a new variable 0, we don't want to
-- change that but we want to rename any other variables in the body.

ren : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Tm Δ σ → Tm Γ σ
ren ρ (var y) = var (ρ y)
ren ρ (lam y) = lam (ren (wk ρ) y)
ren ρ (app y y') = app (ren ρ y) (ren ρ y')

-- the identity renaming (maps variables to themselves)

renId : ∀{Γ} → Ren Γ Γ
renId = λ x → x 

-- composition of renamings (applies two renamings, one after the other)

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = λ x -> f (g x)

postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} →
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀{a} → B a}{g : ∀{a} → B' a} → 
               (∀ a → f {a} ≅ g {a}) → 
               _≅_ {_}{ {a : A} → B a} f {_}{ {a : A} → B' a} g


-- if you weaken the identity renaming then it should still be the same thing
wkid : ∀{Γ σ τ}(x : Var (Γ < τ) σ) → wk renId x ≅ renId x
wkid zero = refl
wkid (suc y) = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
          {x y z u v w}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ u → y ≅ v → z ≅ w  → f x y z ≅ f u v w
cong₃ f refl refl refl = refl


-- if you rename a terms using the id renaming, then the term shouldn't change
renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅  t
renid (var y) = refl
renid (lam y) = cong lam (trans (cong (λ (f : Ren _ _) → ren f y) 
                                       (iext (λ _ → ext wkid))) 
                                (renid y))
renid (app y y') = cong₂ app (renid y) (renid y') 

-- composing two renamings and then weakening them together should be
-- the same as weakening them individually and then composing them
wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) → 
            wk (renComp f g) x ≅ renComp (wk f) (wk g) x  
wkcomp f g zero = refl
wkcomp f g (suc y) = refl

-- composing renamings and then applying them, should be the same as
-- applying them individually
rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
            ren (renComp f g) t ≅ (ren f ∘ ren g) t
rencomp f g (var y) = refl
rencomp f g (lam y) = cong lam (trans (cong (λ (f : Ren _ _) → ren f y)
                                              (iext λ _ → ext (wkcomp f g)))
                                        (rencomp (wk f) (wk g) y))
rencomp f g (app y y') = cong₂ app (rencomp f g y ) (rencomp f g y' )


Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f zero     = var zero
lift f (suc x) = ren suc (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var y) = f y
sub f (lam y) = lam (sub (lift f) y)
sub f (app y y') = app (sub f y) (sub f y')



subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

liftid : ∀{Γ σ τ}(x : Var (Γ < σ) τ) → lift subId x ≅ subId x
liftid zero = refl
liftid (suc y) = refl



subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ id t
subid (var x)   = refl
subid (app t u) = cong₂ app (subid t) (subid u)
subid (lam t)   = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) 
                                        (iext λ _ → ext liftid)) 
                                  (subid t))


-- time for the mysterious four lemmas:
liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) →
            (lift f ∘ wk g) x ≅ lift (f ∘ g) x
liftwk f g zero = refl
liftwk f g (suc y) = refl

subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
         (sub f ∘ ren g) t ≅ sub (f ∘ g) t
subren f g (var x)   = refl
subren f g (app t u) = cong₂ app (subren f g t) (subren f g u)
subren f g (lam t)   = cong lam (trans (subren (lift f) (wk g) t)
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → ext (liftwk f g))))



renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
               (ren (wk f) ∘ lift g) x ≅ lift (ren f ∘ g) x
renwklift f g zero    = refl
renwklift f g (suc x) = trans (sym (rencomp (wk f) suc (g x))) (rencomp suc f (g x)) 

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f ∘  sub g) t ≅ sub (ren f ∘ g) t
rensub f g (var x)   = refl
rensub f g (app t u) = cong₂ app (rensub f g t) (rensub f g u)
rensub f g (lam t)   = cong lam (trans (rensub (wk f) (lift g) t) 
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → 
                                               ext (renwklift f g))))


liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
           lift (subComp f g) x ≅ subComp (lift f) (lift g) x
liftcomp f g zero    = refl
liftcomp f g (suc x) = 
  proof 
  lift (subComp f g) (suc x) 
  ≅⟨ rensub suc f (g x) ⟩
  sub (ren suc ∘ f) (g x)
  ≅⟨ sym (subren (lift f) suc (g x)) ⟩
  subComp (lift f) (lift g) (suc x) 
  ∎

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≅ (sub f ∘ sub g) t
subcomp f g (var x)   = refl
subcomp f g (app t u) = cong₂ app (subcomp f g t) (subcomp f g u)
subcomp f g (lam t)   = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) 
                                              (iext λ _ → ext (liftcomp f g))) 
                                        (subcomp (lift f) (lift g) t))



wk<< : ∀{Γ Δ}(α : Ren Γ Δ)(β : Env Δ){σ}(v : Val σ) → ∀{ρ}(y : Var(Γ < σ) ρ) → ((β ∘ α) << v) y ≅ ((β << v) ∘ wk α) y
wk<< α β v zero = proof v ≡⟨⟩ v ∎
wk<< α β v (suc y) = proof β (α y) ≡⟨⟩ β (α y) ∎

reneval : ∀{Γ Δ σ}(α : Ren Γ Δ)(β : Env Δ)(t : Tm Γ σ) → eval (β ∘ α) t ≅ (eval β ∘ ren α) t
reneval α β (var x) = proof β (α x) ≡⟨⟩ β (α x) ∎
reneval α β (lam t) = ext λ v →
  proof
  eval ((β ∘ α) << v) t 
  ≅⟨ cong (λ (γ : Env _) → eval γ t) (iext λ σ → ext λ x → wk<< α β v x) ⟩
  eval ((β << v) ∘ (wk α)) t
  ≅⟨ reneval (wk α) (β << v) t ⟩
  eval (β << v) (ren (wk α) t)
  ∎
reneval α β (app t u) = 
  proof
  eval (β ∘ α) t (eval (β ∘ α) u) 
  ≅⟨ cong₂ _$_ (reneval α β t) (reneval α β u) ⟩
  eval β (ren α t) (eval β (ren α u))
  ∎

lifteval : ∀{Γ Δ σ τ}(α : Sub Γ Δ)(β : Env Δ)(v : Val σ)(y : Var (Γ < σ) τ) → ((eval β ∘ α) << v) y ≅ (eval (β << v) ∘ lift α) y
lifteval α β v zero = proof v ≡⟨⟩ v ∎
lifteval α β v (suc y) = 
  proof
  eval β (α y) 
  ≅⟨ reneval suc (β << v) (α y) ⟩
  eval (β << v) (ren suc (α y))
  ∎

subeval : ∀{Γ Δ σ}(α : Sub Γ Δ)(β : Env Δ)(t : Tm Γ σ) → eval (eval β ∘ α) t ≅ (eval β ∘ sub α) t
subeval α β (var x) = proof eval β (α x) ≡⟨⟩ eval β (α x) ∎
subeval α β (lam t) = ext λ v → 
  proof
  eval ((eval β ∘ α) << v) t 
  ≅⟨ cong (λ (γ : Env _) → eval γ t) (iext λ σ → ext (lifteval α β v)) ⟩
  eval (eval (β << v) ∘ lift α) t
  ≅⟨ subeval (lift α) (β << v) t ⟩
  eval (β << v) (sub (lift α) t)
  ∎
subeval α β (app t u) = 
  proof
  eval (eval β ∘ α) t (eval (eval β ∘ α) u)
  ≅⟨ cong₂ _$_ (subeval α β t) (subeval α β u) ⟩
  eval β (sub α t) (eval β (sub α u))
  ∎

