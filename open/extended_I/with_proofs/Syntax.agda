module Syntax where

open import Function
open import Data.Nat hiding (_<_; fold)
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


data Ty : Set where
  ι    : Ty
  nat  : Ty
  _⇒_  : Ty → Ty → Ty
  [_]  : Ty → Ty

infixr 10 _⇒_

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vze : ∀{Γ σ} → Var (Γ < σ) σ
  vsu  : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ 

data Tm (Γ : Con) : Ty → Set where 
  var   : ∀{σ} → Var Γ σ → Tm Γ σ
  lam   : ∀{σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
  app   : ∀{σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  ze    : Tm Γ nat
  su    : Tm Γ nat → Tm Γ nat
  rec   : ∀{σ} → Tm Γ σ → Tm Γ (σ ⇒ σ) → Tm Γ nat → Tm Γ σ
  nil   : ∀{σ} → Tm Γ [ σ ]
  cons  : ∀{σ} → Tm Γ σ → Tm Γ [ σ ] → Tm Γ [ σ ]
  fold : ∀{σ τ} →  Tm Γ τ → Tm Γ (σ ⇒ τ ⇒ τ) → Tm Γ [ σ ] → Tm Γ τ

mutual
  data Nf (Γ : Con) : Ty → Set where
    nlam  : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne    : Ne Γ ι → Nf Γ ι
    nenat : Ne Γ nat → Nf Γ nat
    ne[]  : ∀{σ} → Ne Γ [ σ ] → Nf Γ [ σ ] 
    nze   : Nf Γ nat
    nsu   : Nf Γ nat → Nf Γ nat
    nnil  : ∀{σ} → Nf Γ [ σ ]
    ncons : ∀{σ} → Nf Γ σ → Nf Γ [ σ ] → Nf Γ [ σ ]

  data Ne (Γ : Con) : Ty → Set where
    nvar : ∀{σ} → Var Γ σ → Ne Γ σ
    napp : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ
    nrec  : ∀{σ} → Nf Γ σ → Nf Γ (σ ⇒ σ) → Ne Γ nat → Ne Γ σ
    nfold : ∀{σ τ} → Nf Γ τ → Nf Γ (σ ⇒ τ ⇒ τ) → Ne Γ [ σ ] → Ne Γ τ 

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
wk ρ vze = vze
wk ρ (vsu y) = vsu (ρ y)

-- apply a renaming to a term, wk is needed to push the renaming inside 
-- a lambda term. i.e. lambda binds a new variable 0, we don't want to
-- change that but we want to rename any other variables in the body.

ren : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Tm Δ σ → Tm Γ σ
ren ρ (var x) = var (ρ x)
ren ρ (lam t) = lam (ren (wk ρ) t)
ren ρ (app t u) = app (ren ρ t) (ren ρ u)
ren ρ ze = ze
ren ρ (su t) = su (ren ρ t)
ren ρ (rec z f n) = rec (ren ρ z) (ren ρ f) (ren ρ n)
ren ρ nil = nil
ren ρ (cons h t) = cons (ren ρ h) (ren ρ t)
ren ρ (fold z f l) = fold (ren ρ z) (ren ρ f) (ren ρ l) 


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
  renNf ρ (nenat n) = nenat (renNe ρ n)
  renNf ρ (ne[] n) = ne[] (renNe ρ n)
  renNf ρ nze = nze
  renNf ρ (nsu n) = nsu (renNf ρ n)
  renNf ρ nnil = nnil
  renNf ρ (ncons h t) = ncons (renNf ρ h) (renNf ρ t)
  

  renNe : ∀{Γ Δ} → Ren Δ Γ →  ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe ρ (nvar x) = nvar (ρ x)
  renNe ρ (napp t u) = napp (renNe ρ t) (renNf ρ u)
  renNe ρ (nrec z f n) = nrec (renNf ρ z) (renNf ρ f) (renNe ρ n)
  renNe ρ (nfold a f l) = nfold (renNf ρ a) (renNf ρ f) (renNe ρ l)


mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf (nlam n) = lam (embNf n)
  embNf (ne x) = embNe x
  embNf (nenat x) = embNe x
  embNf (ne[] x) = embNe x
  embNf nze = ze
  embNf (nsu n) = su (embNf n)
  embNf nnil = nil
  embNf (ncons h t) = cons (embNf h) (embNf t)

  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (nvar x) = var x
  embNe (napp t u) = app (embNe t) (embNf u)
  embNe (nrec z f n) = rec (embNf z) (embNf f) (embNe n)
  embNe (nfold x f n) = fold (embNf x) (embNf f) (embNe n)


postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} →
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀{a} → B a}{g : ∀{a} → B' a} → 
               (∀ a → f {a} ≅ g {a}) → 
               _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g


-- if you weaken the identity renaming then it should still be the same thing
wkid : ∀{Γ σ τ}(x : Var (Γ < τ) σ) → wk renId x ≅ renId x
wkid vze = refl
wkid (vsu y) = refl


-- if you rename a terms using the id renaming, then the term shouldn't change
renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅ t
renid (var x) = refl
renid (lam y) = proof
  lam (ren (wk renId) y) 
  ≅⟨ cong lam (cong (λ (f : Ren _ _) → ren f y) (iext (λ _ → ext (λ x → wkid x)))) ⟩
  lam (ren renId y) 
  ≅⟨ cong lam (renid y) ⟩
  lam y
  ∎ 
renid (app t u) = cong₂ app (renid t) (renid u) 
renid ze = refl
renid (su t) = cong su (renid t)
renid (rec z f n) = cong₃ rec (renid z) (renid f) (renid n)
renid nil = refl
renid (cons h t) = cong₂ cons (renid h) (renid t)
renid (fold a f l) = cong₃ fold (renid a) (renid f) (renid l)


-- composing two renamings and then weakening them together should be
-- the same as weakening them individually and then composing them
wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) → 
            wk (renComp f g) x ≅ renComp (wk f) (wk g) x  
wkcomp f g vze = refl
wkcomp f g (vsu y) = refl

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
rencomp f g ze = refl
rencomp f g (su t) = cong su (rencomp f g t)
rencomp f g (rec z h n) = cong₃ rec (rencomp f g z) (rencomp f g h) (rencomp f g n)
rencomp f g nil = refl
rencomp f g (cons h t) = cong₂ cons (rencomp f g h) (rencomp f g t)
rencomp f g (fold a fn l) = cong₃ fold (rencomp f g a) (rencomp f g fn) (rencomp f g l)


mutual
  rennecomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Ne Γ σ) → renNe ρ' (renNe ρ v) ≅ renNe (ρ' ∘ ρ) v
  rennecomp ρ' ρ (nvar x) = refl
  rennecomp ρ' ρ (napp t u) = cong₂ napp (rennecomp ρ' ρ t) (rennfcomp ρ' ρ u)
  rennecomp ρ' ρ (nrec z f n) = cong₃ nrec (rennfcomp ρ' ρ z) (rennfcomp ρ' ρ f) (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nfold a f l) = cong₃ nfold (rennfcomp ρ' ρ a) (rennfcomp ρ' ρ f) (rennecomp ρ' ρ l)

  rennfcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Nf Γ σ) → renNf ρ' (renNf ρ v) ≅ renNf (ρ' ∘ ρ) v
  rennfcomp ρ' ρ (nlam v) =  proof
    nlam (renNf (wk ρ') (renNf (wk ρ) v)) 
    ≅⟨ cong nlam (rennfcomp (wk ρ') (wk ρ) v) ⟩
    nlam (renNf (wk ρ' ∘ wk ρ) v) 
    ≅⟨ cong nlam (cong (λ (f : Ren _ _) → renNf f v) (iext (λ _ → ext (λ x → sym (wkcomp ρ' ρ x))))) ⟩
    nlam (renNf (wk (ρ' ∘ ρ)) v)
    ∎
  rennfcomp ρ' ρ (ne x) = cong ne (rennecomp ρ' ρ x)
  rennfcomp ρ' ρ (nenat n) = cong nenat (rennecomp ρ' ρ n)
  rennfcomp ρ' ρ (ne[] l) = cong ne[] (rennecomp ρ' ρ l)
  rennfcomp ρ' ρ nze = refl
  rennfcomp ρ' ρ (nsu v) = cong nsu (rennfcomp ρ' ρ v)
  rennfcomp ρ' ρ nnil = refl
  rennfcomp ρ' ρ (ncons h t) = cong₂ ncons (rennfcomp ρ' ρ h) (rennfcomp ρ' ρ t)



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
  renNfId (nenat n) = cong nenat (renNeId n)
  renNfId (ne[] {_} l) = cong ne[] (renNeId l)
  renNfId nze = refl
  renNfId (nsu n) = cong nsu (renNfId n)   
  renNfId nnil = refl
  renNfId (ncons n n₁) = cong₂ ncons (renNfId n) (renNfId n₁)
  
  renNeId : ∀{Γ σ} → (n : Ne Γ σ) → renNe renId n ≅ n
  renNeId (nvar x) = refl
  renNeId (napp t u) = cong₂ napp (renNeId t) (renNfId u)
  renNeId (nrec z f n) = cong₃ nrec (renNfId z) (renNfId f) (renNeId n)  
  renNeId (nfold a f l) = cong₃ nfold (renNfId a) (renNfId f) (renNeId l)
  
  

Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f vze    = var vze
lift f (vsu x) = ren vsu (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x) = f x
sub f (lam t) = lam (sub (lift f) t)
sub f (app t u) = app (sub f t) (sub f u)
sub f ze = ze
sub f (su n) = su (sub f n)
sub f (rec z g n) = rec (sub f z) (sub f g) (sub f n)
sub f nil = nil
sub f (cons t u) = cons (sub f t) (sub f u)
sub f (fold a fn l) = fold (sub f a) (sub f fn) (sub f l)


sub<< : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Δ σ → Sub (Γ < σ) Δ
sub<< f t vze = t
sub<< f t (vsu x) = f x

subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

liftid : ∀{Γ σ τ}(x : Var (Γ < σ) τ) → lift subId x ≅ subId x
liftid vze = refl
liftid (vsu y) = refl


subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ t
subid (var x) = refl
subid (lam t) = proof
  lam (sub (lift var) t) 
  ≅⟨ cong lam (cong (λ (f : Sub _ _) → sub f t) (iext λ _ → ext liftid)) ⟩
  lam (sub subId t) 
  ≅⟨ cong lam (subid t) ⟩
  lam t
  ∎
subid (app t u) = cong₂ app (subid t) (subid u)
subid ze = refl
subid (su n) = cong su (subid n)
subid (rec z f n) = cong₃ rec (subid z) (subid f) (subid n)
subid nil = refl
subid (cons t t₁) = cong₂ cons (subid t) (subid t₁)
subid (fold a f l) = cong₃ fold (subid a) (subid f) (subid l)


-- time for the mysterious four lemmas:
liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) →
            (lift f ∘ wk g) x ≅ lift (f ∘ g) x
liftwk f g vze = refl
liftwk f g (vsu y) = refl


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
subren f g ze = refl
subren f g (su n) = cong su (subren f g n)
subren f g (rec z h n) = cong₃ rec (subren f g z) (subren f g h) (subren f g n)
subren f g nil = refl
subren f g (cons t t₁) = cong₂ cons (subren f g t) (subren f g t₁)
subren f g (fold a fn l) = cong₃ fold (subren f g a) (subren f g fn) (subren f g l)


renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
               (ren (wk f) ∘ lift g) x ≅ lift (ren f ∘ g) x
renwklift f g vze    = refl
renwklift f g (vsu x) = trans (sym (rencomp (wk f) vsu (g x))) (rencomp vsu f (g x)) 

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
rensub f g ze = refl
rensub f g (su n) = cong su (rensub f g n)
rensub f g (rec z h n) = cong₃ rec (rensub f g z) (rensub f g h) (rensub f g n)
rensub f g nil = refl
rensub f g (cons t t₁) = cong₂ cons (rensub f g t) (rensub f g t₁)
rensub f g (fold a fn l) = cong₃ fold (rensub f g a) (rensub f g fn) (rensub f g l)


liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
           lift (subComp f g) x ≅ subComp (lift f) (lift g) x
liftcomp f g vze    = refl
liftcomp f g (vsu x) = 
  proof 
  lift (subComp f g) (vsu x) 
  ≅⟨ rensub vsu f (g x) ⟩
  sub (ren vsu ∘ f) (g x)
  ≅⟨ sym (subren (lift f) vsu (g x)) ⟩
  subComp (lift f) (lift g) (vsu x) 
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
subcomp f g ze = refl
subcomp f g (su n) = cong su (subcomp f g n)
subcomp f g (rec z h n) = cong₃ rec (subcomp f g z) (subcomp f g h) (subcomp f g n)
subcomp f g nil = refl
subcomp f g (cons t t₁) = cong₂ cons (subcomp f g t) (subcomp f g t₁)
subcomp f g (fold a fn l) = cong₃ fold (subcomp f g a) (subcomp f g fn) (subcomp f g l)

