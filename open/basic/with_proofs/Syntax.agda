module Syntax where

open import Function
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
  
mutual
  data Nf (Γ : Con) : Ty → Set where
    nlam  : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne    : Ne Γ ι → Nf Γ ι
   
  data Ne (Γ : Con) : Ty → Set where
    nvar : ∀{σ} → Var Γ σ → Ne Γ σ
    napp : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ
   
-- the type of renamings: functions mapping variables in one context to
-- variables in another

Ren : Con → Con → Set
Ren Δ Γ = ∀{σ} → Var Δ σ → Var Γ σ

-- We are working towards substitution - the operation of replacing
-- variables by terms in a term. First we'll look at renaming which is
-- a simpler function that replaces variables by variables.


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
ren ρ (var x) = var (ρ x)
ren ρ (lam t) = lam (ren (wk ρ) t)
ren ρ (app t u) = app (ren ρ t) (ren ρ u)

-- the identity renaming (maps variables to themselves)

renId : ∀{Γ} → Ren Γ Γ
renId = id

-- composition of renamings (applies two renamings, one after the other)

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g 


cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
          {x y z u v w}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ u → y ≅ v → z ≅ w  → f x y z ≅ f u v w
cong₃ f refl refl refl = refl


mutual
  renNf : ∀{Γ Δ} → Ren Δ Γ →  ∀{σ} → Nf Δ σ → Nf Γ σ
  renNf ρ (nlam n) = nlam (renNf (wk ρ) n)
  renNf ρ (ne n) = ne (renNe ρ n)
    
  renNe : ∀{Γ Δ} → Ren Δ Γ →  ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe ρ (nvar x) = nvar (ρ x)
  renNe ρ (napp t u) = napp (renNe ρ t) (renNf ρ u)
 

postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} →
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀{a} → B a}{g : ∀{a} → B' a} → 
               (∀ a → f {a} ≅ g {a}) → 
               _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g


-- if you weaken the identity renaming then it should still be the same thing
wkid : ∀{Γ σ τ}(x : Var (Γ < τ) σ) → wk renId x ≅ renId x
wkid zero = refl
wkid (suc y) = refl


-- if you rename a terms using the id renaming, then the term shouldn't change
renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅  t
renid (var x) = refl
renid (lam y) = proof
  lam (ren (wk renId) y) 
  ≅⟨ cong lam (cong (λ (f : Ren _ _) → ren f y) (iext (λ _ → ext (λ x → wkid x)))) ⟩
  lam (ren renId y) 
  ≅⟨ cong lam (renid y) ⟩
  lam y
  ∎ 
renid (app t u) = cong₂ app (renid t) (renid u) 


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
rencomp f g (var x) = refl
rencomp f g (lam t) = proof
  lam (ren (wk (f ∘ g)) t) 
  ≅⟨ cong lam (cong (λ (f : Ren _ _) → ren f t) (iext (λ _ → ext λ x → wkcomp f g x))) ⟩
  lam (ren ((wk f) ∘ (wk g)) t) 
  ≅⟨ cong lam (rencomp (wk f) (wk g) t) ⟩
  lam (ren (wk f) (ren (wk g) t))
  ∎
rencomp f g (app t u) = cong₂ app (rencomp f g t ) (rencomp f g u)


mutual
  rennecomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Ne Γ σ) → renNe ρ' (renNe ρ v) ≅ renNe (ρ' ∘ ρ) v
  rennecomp ρ' ρ (nvar x) = refl
  rennecomp ρ' ρ (napp t u) = cong₂ napp (rennecomp ρ' ρ t) (rennfcomp ρ' ρ u)

  rennfcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Nf Γ σ) → renNf ρ' (renNf ρ v) ≅ renNf (ρ' ∘ ρ) v
  rennfcomp ρ' ρ (nlam v) =  proof
    nlam (renNf (wk ρ') (renNf (wk ρ) v)) 
    ≅⟨ cong nlam (rennfcomp (wk ρ') (wk ρ) v) ⟩
    nlam (renNf (wk ρ' ∘ wk ρ) v) 
    ≅⟨ cong nlam (cong (λ (f : Ren _ _) → renNf f v) (iext (λ _ → ext (λ x → sym (wkcomp ρ' ρ x))))) ⟩
    nlam (renNf (wk (ρ' ∘ ρ)) v)
    ∎
  rennfcomp ρ' ρ (ne x) = cong ne (rennecomp ρ' ρ x)

  
mutual
  renNfId : ∀{Γ σ} → (n : Nf Γ σ) → renNf renId n ≅ n
  renNfId (nlam n) = proof
    nlam (renNf (wk renId) n) 
    ≅⟨ cong (λ (f : Ren _ _) → nlam (renNf f n)) (iext λ σ' → ext λ x → wkid x) ⟩ 
    nlam (renNf renId n) 
    ≅⟨ cong nlam (renNfId n) ⟩ 
    nlam n
    ∎
  renNfId (ne x) = cong ne (renNeId x)
  
  renNeId : ∀{Γ σ} → (n : Ne Γ σ) → renNe renId n ≅ n
  renNeId (nvar x) = refl
  renNeId (napp t u) = cong₂ napp (renNeId t) (renNfId u)


Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f zero    = var zero
lift f (suc x) = ren suc (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x) = f x
sub f (lam t) = lam (sub (lift f) t)
sub f (app t u) = app (sub f t) (sub f u)

sub<< : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Δ σ → Sub (Γ < σ) Δ
sub<< f t zero = t
sub<< f t (suc x) = f x

subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g


sub<<-comp : ∀{Γ Δ B σ}(α : Sub Γ Δ)(β : Sub B Γ)(u : Tm Γ σ){τ}(x : Var (B < σ) τ) → subComp α (sub<< β u) x ≅ sub<< (subComp α β) (sub α u) x
sub<<-comp α β u zero = refl
sub<<-comp α β u (suc x) = refl


liftid : ∀{Γ σ τ}(x : Var (Γ < σ) τ) → lift subId x ≅ subId x
liftid zero = refl
liftid (suc y) = refl


subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ id t
subid (var x) = refl
subid (lam t) = proof
  lam (sub (lift var) t) 
  ≅⟨ cong lam (cong (λ (f : Sub _ _) → sub f t) (iext λ _ → ext liftid)) ⟩
  lam (sub subId t) 
  ≅⟨ cong lam (subid t) ⟩
  lam t
  ∎
subid (app t u) = cong₂ app (subid t) (subid u)


-- time for the mysterious four lemmas:
liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) →
            (lift f ∘ wk g) x ≅ lift (f ∘ g) x
liftwk f g zero = refl
liftwk f g (suc y) = refl

subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
         (sub f ∘ ren g) t ≅ sub (f ∘ g) t
subren f g (var x) = refl
subren f g (lam t) = proof
  lam (sub (lift f) (ren (wk g) t)) 
  ≅⟨ cong lam (subren (lift f) (wk g) t) ⟩
  lam (sub (lift f ∘ wk g) t) 
  ≅⟨ cong lam (cong (λ (h : Sub _ _) → sub h t) (iext λ _ → ext (liftwk f g))) ⟩
  lam (sub (lift (f ∘ g)) t)
  ∎
subren f g (app t u) = cong₂ app (subren f g t) (subren f g u)


renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
               (ren (wk f) ∘ lift g) x ≅ lift (ren f ∘ g) x
renwklift f g zero    = refl
renwklift f g (suc x) = trans (sym (rencomp (wk f) suc (g x))) (rencomp suc f (g x)) 

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f ∘  sub g) t ≅ sub (ren f ∘ g) t
rensub f g (var x) = refl
rensub f g (lam t) = proof
  lam (ren (wk f) (sub (lift g) t)) 
  ≅⟨ cong lam (rensub (wk f) (lift g) t) ⟩
  lam (sub (ren (wk f) ∘ (lift g)) t) 
  ≅⟨ cong lam (cong (λ (h : Sub _ _) → sub h t) (iext (λ _ → ext (renwklift f g)))) ⟩
  lam (sub (lift (ren f ∘ g)) t)
  ∎
rensub f g (app t u) = cong₂ app (rensub f g t) (rensub f g u) 


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
subcomp f g (var x) = refl
subcomp f g (lam t) = proof
  lam (sub (lift (sub f ∘ g)) t) 
  ≅⟨ cong lam (cong (λ (h : Sub _ _) → sub h t) (iext λ _ → ext (liftcomp f g))) ⟩
  lam (sub (sub (lift f) ∘ (lift g)) t) 
  ≅⟨ cong lam (subcomp (lift f) (lift g) t) ⟩
  lam (sub (lift f) (sub (lift g) t))
  ∎
subcomp f g (app t u) = cong₂ app (subcomp  f g t) (subcomp f g u)

