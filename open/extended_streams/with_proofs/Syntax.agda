{-# OPTIONS --copatterns #-}

module Syntax where

open import Function
open import Data.Nat hiding (_<_)
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


data Ty : Set where
  ι    : Ty
  nat  : Ty
  _⇒_  : Ty → Ty → Ty
  _∧_  : Ty → Ty → Ty
  <_>  : Ty → Ty

infixr 10 _⇒_

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vze  : ∀{Γ σ} → Var (Γ < σ) σ
  vsu  : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ 

data Tm (Γ : Con) : Ty → Set where 
  var  : ∀{σ} → Var Γ σ → Tm Γ σ
  lam  : ∀{σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
  app  : ∀{σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  _,,_ : ∀{σ τ} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ∧ τ)
  fst  : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ σ
  snd  : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ τ
  ze   : Tm Γ nat
  su   : Tm Γ nat → Tm Γ nat
  rec  : ∀{σ} → Tm Γ σ → Tm Γ (σ ⇒ σ) → Tm Γ nat → Tm Γ σ 
  hd   : ∀{σ} → Tm Γ < σ > → Tm Γ σ
  tl   : ∀{σ} → Tm Γ < σ > → Tm Γ < σ >
  unfold : ∀{σ τ} → Tm Γ σ → Tm Γ (σ ⇒ σ ∧ τ) → Tm Γ < τ >


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
ren α (var x) = var (α x)
ren α (lam t) = lam (ren (wk α) t)
ren α (app t u) = app (ren α t) (ren α u)
ren α (t ,, u) = ren α t ,, ren α u
ren α (fst t) = fst (ren α t)
ren α (snd t) = snd (ren α t)
ren α ze = ze
ren α (su t) = su (ren α t)
ren α (rec z f n) = rec (ren α z) (ren α f) (ren α n)
ren α (hd t) = hd (ren α t)
ren α (tl t) = tl (ren α t)
ren α (unfold z f) = unfold (ren α z) (ren α f)
  

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
renid (a ,, b) = cong₂ _,,_ (renid a) (renid b)
renid (fst t) = cong fst (renid t)
renid (snd t) = cong snd (renid t)
renid (hd t) = cong hd (renid t)
renid (tl t) = cong tl (renid t)
renid (unfold z f) = cong₂ unfold (renid z) (renid f)



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
rencomp f g (a ,, b) = cong₂ _,,_ (rencomp f g a) (rencomp f g b)
rencomp f g (fst t) = cong fst (rencomp f g t)
rencomp f g (snd t) = cong snd (rencomp f g t)
rencomp f g (hd t) = cong hd (rencomp f g t)
rencomp f g (tl t) = cong tl (rencomp f g t)
rencomp f g (unfold z fn) = cong₂ unfold (rencomp f g z) (rencomp f g fn)


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
sub f (a ,, b) = sub f a ,, sub f b
sub f (fst t) = fst (sub f t)
sub f (snd t) = snd (sub f t)
sub f (hd t) = hd (sub f t)
sub f (tl t) = tl (sub f t)
sub f (unfold z fn) = unfold (sub f z) (sub f fn)


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
subid (a ,, b) = cong₂ _,,_ (subid a) (subid b)
subid (fst t) = cong fst (subid t)
subid (snd t) = cong snd (subid t)
subid (hd t) = cong hd (subid t)
subid (tl t) = cong tl (subid t)
subid (unfold z f) = cong₂ unfold (subid z) (subid f)



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
subren f g (a ,, b) = cong₂ _,,_ (subren f g a) (subren f g b)
subren f g (fst t) = cong fst (subren f g t)
subren f g (snd t) = cong snd (subren f g t)
subren f g (hd t) = cong hd (subren f g t)
subren f g (tl t) = cong tl (subren f g t)
subren f g (unfold z fn) = cong₂ unfold (subren f g z) (subren f g fn)



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
rensub f g (a ,, b) = cong₂ _,,_ (rensub f g a) (rensub f g b)
rensub f g (fst t) = cong fst (rensub f g t)
rensub f g (snd t) = cong snd (rensub f g t)
rensub f g (hd t) = cong hd (rensub f g t)
rensub f g (tl t) = cong tl (rensub f g t)
rensub f g (unfold z fn) = cong₂ unfold (rensub f g z) (rensub f g fn)



liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
           lift (subComp f g) x ≅ subComp (lift f) (lift g) x
liftcomp f g vze     = refl
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
subcomp f g (a ,, b) = cong₂ _,,_ (subcomp f g a) (subcomp f g b)
subcomp f g (fst t) = cong fst (subcomp f g t)
subcomp f g (snd t) = cong snd (subcomp f g t)
subcomp f g (hd t) = cong hd (subcomp f g t)
subcomp f g (tl t) = cong tl (subcomp f g t)
subcomp f g (unfold z fn) = cong₂ unfold (subcomp f g z) (subcomp f g fn)
