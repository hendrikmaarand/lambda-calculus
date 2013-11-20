module MyLambdaKripke2 where

open import Data.Bool
open import Function
open import Data.Nat hiding (_<_)
open import Relation.Binary.HeterogeneousEquality
open import Data.Product
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
ren ρ (var y) = var (ρ y)
ren ρ (lam y) = lam (ren (wk ρ) y)
ren ρ (app y y') = app (ren ρ y) (ren ρ y')

-- the identity renaming (maps variables to themselves)

renId : ∀{Γ} → Ren Γ Γ
renId = id

-- composition of renamings (applies two renamings, one after the other)

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g 

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
lift f zero    = var zero
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

data _∼_ {Γ σ} : Tm Γ σ → Tm Γ σ → Set where
{-  refl
  sym 
  trans
  beta 
  eta 
  congapp
  conglam
  congvar? -}

-- cut here!

mutual 
  Val : Con → Ty → Set
  Val Γ ι    = ℕ
  Val Γ (σ ⇒ τ) = Σ (∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ) λ f → ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v : Val Δ σ) → renval ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval ρ' v)

  renval : ∀{Γ Δ σ} → Ren Γ Δ → Val Γ σ → Val Δ σ
  renval {Γ} {Δ} {ι} α v = v
  renval {Γ} {Δ} {σ ⇒ τ} α v = (λ {E} β v' → proj₁ v (renComp β α) v') , 
         (λ {Δ₁ Δ' : Con} (ρ : {σ₁ : Ty} → Var Δ σ₁ → Var Δ₁ σ₁) (ρ' : {σ₁ : Ty} → Var Δ₁ σ₁ → Var Δ' σ₁) (v₁ : Val Δ₁ σ) → 
         proof
         renval ρ' (proj₁ v (ρ ∘ α) v₁)
         ≅⟨ proj₂ v {Δ₁} {Δ'} (renComp ρ α) ρ' v₁ ⟩
         proj₁ v (ρ' ∘ ρ ∘ α) (renval ρ' v₁)
         ∎)

Σeq : {A : Set} {A' : Set} {B : A → Set} {B' : A' → Set} → {a : A} → {a' : A'} → a ≅ a' → B ≅ B' → {b : B a} → {b' : B' a'} → b ≅ b' → _,_ {B = B} a b ≅ _,_ {B = B'} a' b'
Σeq refl refl refl = refl

ir : ∀{A A' : Set} → {a : A} → {a' : A'} → {p q : a ≅ a'} → p ≅ q
ir {p = refl} {q = refl} = refl

fixedtypes : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a'' → p ≅ q
fixedtypes {p = refl} {q = refl} refl = refl

renvalcomp : ∀{Γ Δ E σ} → (ρ : Ren Γ Δ) → (ρ' : Ren Δ E) → (v : Val Γ σ) → renval ρ' (renval ρ v) ≅ renval (ρ' ∘ ρ) v 
renvalcomp {Γ} {Δ} {E} {ι} ρ ρ' v = refl
renvalcomp {Γ} {Δ} {E} {σ ⇒ σ₁} ρ ρ' (f , p) = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)

Env : Con → Con → Set
Env Γ Δ = ∀{σ} → Var Γ σ → Val Δ σ


_<<_ : ∀{Γ Δ} → Env Γ Δ → ∀{σ} → Val Δ σ → Env (Γ < σ) Δ
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

  

renval<< : ∀{Γ Δ E σ} → (ρ : Ren Δ E) → (γ : Env Γ Δ) → (v : Val Δ σ) → ∀{τ}(x : Var (Γ < σ) τ) → (renval ρ ∘ (γ << v)) x ≅ ((renval ρ ∘ γ) << renval ρ v) x
renval<< ρ γ v zero = refl
renval<< ρ γ v (suc x) = refl

ifcong : {A : Set}{B : A → Set}{f f' : {a : A} → B a} → _≅_ {_}{ {a : A} → B a } f {_} { {a : A} → B a } f' → (a : A) → f {a} ≅ f' {a}
ifcong refl a = refl


fcong : ∀{A B : Set} → {f f' : A → B} → f ≅ f' → (a : A) → f a ≅ f' a
fcong refl a = refl


mutual
  eval : ∀{Γ Δ σ} → Env Γ Δ → Tm Γ σ → Val Δ σ
  eval γ (var t) = γ t
  eval {Γ} {Δ} {σ ⇒ τ} γ (lam t) = (λ α v → eval ((renval α ∘ γ) << v) t) , (λ ρ ρ' v → 
      proof
      renval ρ' (eval ((renval ρ ∘ γ) << v) t)
      ≅⟨ evallem ((renval ρ ∘ γ) << v) ρ' t ⟩
      eval (renval ρ' ∘ ((renval ρ ∘ γ) << v)) t
      ≅⟨ cong (λ (γ : Env _ _) → eval γ t) (iext (λ τ → ext (renval<< ρ' (renval ρ ∘ γ) v))) ⟩
      eval ((renval ρ' ∘ renval ρ ∘ γ) << renval ρ' v) t
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → eval ((x ∘ γ) << renval ρ' v) t ) (iext λ σ → ext λ v → renvalcomp ρ ρ' v) ⟩
      eval ((renval (ρ' ∘ ρ) ∘ γ) << renval ρ' v) t
      ∎)
  eval γ (app t t') = proj₁ (eval γ t) renId (eval γ t')     

  evallem : ∀{Γ Δ Δ₁ σ} → (γ : Env Γ Δ)(ρ : Ren Δ Δ₁)(t : Tm Γ σ) → renval ρ (eval γ t) ≅ eval (renval ρ ∘ γ) t
  evallem γ ρ (var x) = refl
  evallem γ ρ (lam t) = Σeq 
    (iext λ σ → ext λ (α : Ren _ _) → ext λ v → 
      proof
      eval ((renval (α ∘ ρ) ∘ γ) << v) t
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → eval ((x ∘ γ) << v) t ) (iext λ _ → ext λ v → sym (renvalcomp ρ α v)) ⟩ 
      eval ((renval α ∘ renval ρ ∘ γ) << v) t
      ∎)
    refl 
    (iext λ Δ₁ → iext λ Δ' → ext λ (ρ₁ : Ren _ _) → ext λ (ρ'' : Ren _ _) → ext λ v₁ → fixedtypes (
      proof
      eval ((renval (ρ'' ∘ ρ₁ ∘ ρ) ∘ γ) << renval ρ'' v₁) t
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → eval ((x ∘ γ) << renval ρ'' v₁) t ) (iext λ _ → ext λ v → sym (renvalcomp (ρ₁ ∘ ρ) ρ'' v))  ⟩
      eval ((renval ρ'' ∘ renval (ρ₁ ∘ ρ) ∘ γ) << renval ρ'' v₁) t
      ≅⟨ cong (λ (γ : Env _ _) → eval γ t) (iext (λ _ → ext (λ x → sym (renval<< ρ'' (renval (ρ₁ ∘ ρ) ∘ γ) v₁ x )))) ⟩
      eval (renval ρ'' ∘ ((renval (ρ₁ ∘ ρ) ∘ γ) << v₁)) t
      ≅⟨ sym (evallem ((renval (ρ₁ ∘ ρ) ∘ γ) << v₁) ρ'' t) ⟩
      renval ρ'' (eval ((renval (ρ₁ ∘ ρ) ∘ γ) << v₁) t)
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → renval ρ'' (eval ((x ∘ γ) << v₁) t )) (iext λ _ → ext λ v → sym (renvalcomp ρ ρ₁ v)) ⟩
      renval ρ'' (eval ((renval ρ₁ ∘ renval ρ ∘ γ) << v₁) t)
      ∎))
  evallem {_}{_}{Δ} γ ρ (app {σ}{τ} t u) =
    proof
    renval ρ (proj₁ (eval γ t) id (eval γ u))
    ≅⟨ proj₂ (eval γ t) id ρ (eval γ u)  ⟩
    proj₁ (eval γ t) ρ (renval ρ (eval γ u))
    ≅⟨ cong (proj₁ (eval γ t) ρ) (evallem γ ρ u) ⟩
    proj₁ (eval γ t) ρ (eval (renval ρ ∘ γ) u)
    ≅⟨ cong (λ f → f (eval (renval ρ ∘ γ) u)) (fcong (ifcong (cong proj₁ (evallem γ ρ t)) Δ) id)  ⟩
    proj₁ (eval (renval ρ ∘ γ) t) id (eval (renval ρ ∘ γ) u)
    ∎


wk<< : ∀{Γ Δ E}(α : Ren Γ Δ)(β : Env Δ E){σ}(v : Val E σ) → ∀{ρ}(y : Var(Γ < σ) ρ) → ((β ∘ α) << v) y ≅ ((β << v) ∘ wk α) y
wk<< α β v zero = proof v ≡⟨⟩ v ∎
wk<< α β v (suc y) = proof β (α y) ≡⟨⟩ β (α y) ∎

reneval : ∀{Γ Δ E σ}(α : Ren Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (β ∘ α) t ≅ (eval β ∘ ren α) t
reneval α β (var x) = proof β (α x) ≡⟨⟩ β (α x) ∎
reneval {Γ} {Δ} {E} {σ ⇒ τ} α β (lam t) = Σeq 
  (iext λ Δ' → ext λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((renval α₁ ∘ β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext (wk<< α (renval α₁ ∘ β) v) ) ⟩
    eval (((renval α₁ ∘ β) << v) ∘ wk α) t
    ≅⟨ reneval (wk α) ((renval α₁ ∘ β) << v) t ⟩
    eval ((renval α₁ ∘ β) << v) (ren (wk α) t)
    ∎) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((renval (ρ' ∘ ρ) ∘ β ∘ α) << renval ρ' v) t
    ≅⟨ cong (λ (f : ∀{σ} → Val _ σ → Val _ σ) → eval ((f ∘ β ∘ α) << renval ρ' v) t) (iext (λ _ → ext (λ x → sym (renvalcomp ρ ρ' x)))) ⟩
    eval (((renval ρ' ∘ renval ρ) ∘ β ∘ α) << renval ρ' v) t
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' ((renval ρ ∘ β) ∘ α) v x)) ⟩
    eval (renval ρ' ∘ (((renval ρ ∘ β) ∘ α) << v)) t 
    ≅⟨ sym (evallem (((renval ρ ∘ β) ∘ α) << v) ρ' t) ⟩
    renval ρ' (eval (((renval ρ ∘ β) ∘ α) << v) t)
    ≅⟨ cong (λ (f : Env _ _) → renval ρ' (eval f t)) (iext λ _ → ext λ x → wk<< α (renval ρ ∘ β) v x ) ⟩
    renval ρ' (eval (((renval ρ ∘ β) << v) ∘ wk α) t)
    ≅⟨ cong (renval ρ') (reneval (wk α) ((renval ρ ∘ β) << v) t) ⟩
    renval ρ' (eval ((renval ρ ∘ β) << v) (ren (wk α) t))
    ∎))
reneval {Γ} {Δ} {E} α β (app {σ} {τ} t u) = 
  proof
  ((proj₁ (eval (β ∘ α) t)) renId) (eval (β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (β ∘ α) t)) renId) (reneval α β u) ⟩
  ((proj₁ (eval (β ∘ α) t)) renId) (eval β (ren α u))
  ≅⟨ cong (λ f → f (eval β (ren α u))) (fcong (ifcong (cong proj₁ (reneval α β t)) E) id) ⟩
  (proj₁ (eval β (ren α t)) renId) (eval β (ren α u))           
  ∎

lifteval : ∀{Γ Δ E σ τ}(α : Sub Γ Δ)(β : Env Δ E)(v : Val E σ)(y : Var (Γ < σ) τ) → ((eval β ∘ α) << v) y ≅ (eval (β << v) ∘ lift α) y
lifteval α β v zero = proof v ≡⟨⟩ v ∎
lifteval α β v (suc y) = 
  proof
  eval β (α y) 
  ≅⟨ reneval suc (β << v) (α y) ⟩
  eval (β << v) (ren suc (α y))
  ∎

subeval : ∀{Γ Δ E σ}(α : Sub Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (eval β ∘ α) t ≅ (eval β ∘ sub α) t
subeval α β (var x) = proof eval β (α x) ≡⟨⟩ eval β (α x) ∎
subeval {Γ} {Δ} {E} {σ ⇒ τ} α β (lam t) = Σeq 
  (iext λ Δ' → ext λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((renval α₁ ∘ eval β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval (f << v) t) (iext λ _ → ext λ x → evallem β α₁ (α x)) ⟩
    eval ((eval (renval α₁ ∘ β) ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext (λ _ → ext λ x → lifteval α (renval α₁ ∘ β) v x )) ⟩
    eval (eval ((renval α₁ ∘ β) << v) ∘ lift α) t
    ≅⟨ subeval (lift α) ((renval α₁ ∘ β) << v) t ⟩
    eval ((renval α₁ ∘ β) << v) (sub (lift α) t)
    ∎
  ) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((renval (ρ' ∘ ρ) ∘ eval β ∘ α) << renval ρ' v) t 
    ≅⟨ cong (λ (f : ∀{σ} → Val _ σ → Val _ σ) → eval ((f ∘ eval β ∘ α) << renval ρ' v) t) (iext λ _ → ext λ x → sym (renvalcomp ρ ρ' x)) ⟩
    eval ((renval ρ' ∘ renval ρ ∘ eval β ∘ α) << renval ρ' v) t
    ≅⟨ cong (λ (f : Env _ _ ) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' (renval ρ ∘ eval β ∘ α) v x)) ⟩
    eval (renval ρ' ∘ (renval ρ ∘ eval β ∘ α) << v) t
    ≅⟨ cong (λ (f : ∀{σ} → Tm _ σ → Val _ σ) → eval (renval ρ' ∘ ((f ∘ α) << v)) t) (iext λ _ → ext λ t → evallem β ρ t ) ⟩
    eval (renval ρ' ∘ (eval (renval ρ ∘ β) ∘ α) << v) t
    ≅⟨ sym (evallem ((eval (renval ρ ∘ β) ∘ α) << v) ρ' t)  ⟩
    renval ρ' (eval ((eval (renval ρ ∘ β) ∘ α) << v) t) 
    ≅⟨ cong (λ (f : Env _ _) → renval ρ' (eval f t)) (iext λ _ → ext λ x → lifteval α (renval ρ ∘ β) v x ) ⟩
    renval ρ' (eval (eval ((renval ρ ∘ β) << v) ∘ lift α) t) 
    ≅⟨ cong (renval ρ') (subeval (lift α) ((renval ρ ∘ β) << v) t) ⟩
    renval ρ' (eval ((renval ρ ∘ β) << v) (sub (lift α) t))
    ∎))
subeval {Γ} {Δ} {E} {σ} α β (app t u) = 
  proof
  (proj₁ (eval (eval β ∘ α) t) renId) (eval (eval β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (eval β ∘ α) t) renId)) (subeval α β u) ⟩
  (proj₁ (eval (eval β ∘ α) t) renId) (eval β (sub α u))
  ≅⟨ cong (λ f → f (eval β (sub α u))) (fcong (ifcong (cong proj₁ (subeval α β t)) E) id) ⟩
  (proj₁ (eval β (sub α t)) renId) (eval β (sub α u))
  ∎

-- define reify and reflect
