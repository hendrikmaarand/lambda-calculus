{-# OPTIONS --copatterns #-}

module Values where

open import Syntax
open import NormalForms
open import Utils

open import Data.Nat hiding (_<_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Size

mutual
  data StreamVal (A B : Set) : Set where
    neSV : B → StreamVal A B
    streamSV : A → ∞StreamVal A B → StreamVal A B

  record ∞StreamVal (A B : Set) : Set where
    coinductive
    field vforce : StreamVal A B

open ∞StreamVal public

mutual
  data _SV∼_ {i : Size}{A B : Set} : (s s' : StreamVal A B) → Set where
    neSV∼ : {n n' : B} → n ≅ n' → neSV n SV∼ neSV n'
    sSV∼  : {h h' : A}{t t' : ∞StreamVal A B} → h ≅ h' → t ∞SV⟨ i ⟩∼ t' → streamSV h t SV∼ streamSV h' t' 

  record _∞SV⟨_⟩∼_ {A B}(s : ∞StreamVal A B) i (s' : ∞StreamVal A B) : Set where
    coinductive
    field ∼force : {j : Size< i} →  _SV∼_ {j} (vforce s) (vforce s')

open _∞SV⟨_⟩∼_ public


mutual
  sv-refl : ∀{A B i} → {s : StreamVal A B} → _SV∼_ {i = i} s s
  sv-refl {s = neSV x} = neSV∼ refl
  sv-refl {s = streamSV h t} = sSV∼ refl ∞sv-refl
  
  ∞sv-refl : ∀{A B i} → {s : ∞StreamVal A B} → s ∞SV⟨ i ⟩∼ s
  ∼force (∞sv-refl) = sv-refl

mutual
  sv-sym : ∀{A B i} → {s s' : StreamVal A B} → _SV∼_ {i = i} s s' → _SV∼_ {i = i} s' s
  sv-sym (neSV∼ p) = neSV∼ (sym p)
  sv-sym (sSV∼ h t) = sSV∼ (sym h) (∞sv-sym t)

  ∞sv-sym : ∀{A B i} → {s s' : ∞StreamVal A B} → s ∞SV⟨ i ⟩∼ s' → s' ∞SV⟨ i ⟩∼ s
  ∼force (∞sv-sym {i = i} p) = sv-sym (∼force p)

mutual
  sv-trans : ∀{A B i} → {s s' s'' : StreamVal A B} → _SV∼_ {i = i} s s' → _SV∼_ {i = i} s' s'' → _SV∼_ {i = i} s s''
  sv-trans (neSV∼ x) (neSV∼ x₁) = neSV∼ (trans x x₁) 
  sv-trans (sSV∼ h t) (sSV∼ h' t') = sSV∼ (trans h h') (∞sv-trans t t')

  ∞sv-trans : ∀{A B i} → {s s' s'' : ∞StreamVal A B} → s ∞SV⟨ i ⟩∼ s' → s' ∞SV⟨ i ⟩∼ s'' → s ∞SV⟨ i ⟩∼ s''
  ∼force (∞sv-trans p q) = sv-trans (∼force p) (∼force q)

≅toSV∼ : ∀{A B i} → {s s' : StreamVal A B} → s ≅ s' → _SV∼_ {i} s s'
≅toSV∼ refl = sv-refl

postulate SVEq : ∀{A B} → {s s' : StreamVal A B} → _SV∼_ {∞} s s' → s ≅ s'

mutual
  Val : Con → Ty → Set
  Val Γ ι = Nf Γ ι
  Val Γ nat = Nf Γ nat
  Val Γ (σ ⇒ τ) = Σ (∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ) 
                  λ f → ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v : Val Δ σ) → renval {σ = τ} ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval {σ = σ} ρ' v)
  Val Γ (σ ∧ τ) = Val Γ σ × Val Γ τ
  Val Γ < σ > = StreamVal (Val Γ σ) (Ne Γ < σ >)

  renval : ∀{Γ Δ σ} → Ren Γ Δ → Val Γ σ → Val Δ σ
  renval {Γ} {Δ} {ι} α v   = renNf α v
  renval {Γ} {Δ} {nat} α v = renNf α v
  renval {Γ} {Δ} {σ ⇒ τ} α v = (λ {E} β v' → proj₁ v (renComp β α) v') , 
         (λ {Δ₁ Δ' : Con} (ρ : Ren Δ Δ₁) (ρ' : Ren Δ₁ Δ') (v₁ : Val Δ₁ σ) → 
           proof
           renval {σ = τ} ρ' (proj₁ v (λ {σ} x → ρ (α x)) v₁) 
           ≅⟨ proj₂ v {Δ₁} {Δ'} (renComp ρ α) ρ' v₁ ⟩
           proj₁ v (λ {σ} x → ρ' (ρ (α x))) (renval {σ = σ} ρ' v₁)
           ∎)
  renval {Γ} {Δ} {σ ∧ τ} α v = (renval {σ = σ} α (proj₁ v)) , (renval {σ = τ} α (proj₂ v))
  renval {Γ} {Δ} {< σ >} α v = renvalSV α v
  
  renvalSV : ∀{Γ Δ σ} → Ren Γ Δ → StreamVal (Val Γ σ) (Ne Γ < σ >) → StreamVal (Val Δ σ) (Ne Δ < σ >)
  renvalSV α (neSV x) = neSV (renNe α x)
  renvalSV {σ = σ} α (streamSV h t) = streamSV (renval {σ = σ} α h) (∞renvalSV α t)
  
  ∞renvalSV : ∀{Γ Δ σ} → Ren Γ Δ → ∞StreamVal (Val Γ σ) (Ne Γ < σ >) → ∞StreamVal (Val Δ σ) (Ne Δ < σ >)
  vforce (∞renvalSV {σ = σ} α v) = renvalSV α (vforce v)


mutual
  renvalcomp : ∀{Γ Δ E σ} → {i : Size} → (ρ' : Ren Δ E) → (ρ : Ren Γ Δ) → (v : Val Γ σ) → renval {σ = σ} ρ' (renval {σ = σ} ρ v) ≅ renval {σ = σ} (ρ' ∘ ρ) v 
  renvalcomp {σ = ι}{i} ρ' ρ v = NfEq (rennfcomp ρ' ρ v)
  renvalcomp {σ = nat}{i} ρ' ρ v = NfEq (rennfcomp ρ' ρ v) 
  renvalcomp {σ = σ ⇒ τ} ρ' ρ v = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)
  renvalcomp {σ = σ ∧ τ}{i} ρ' ρ v = cong₂ _,_ (renvalcomp {σ = σ}{i} ρ' ρ (proj₁ v)) (renvalcomp {σ = τ}{i} ρ' ρ (proj₂ v))
  renvalcomp {σ = < σ >}{i} ρ' ρ v = SVEq (renvalcompSV ρ' ρ v)

  renvalcompSV : ∀{Γ Δ E σ} → {i : Size}(ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : StreamVal (Val Γ σ) (Ne Γ < σ >)) → 
               _SV∼_ {i} (renval {σ = < σ >} ρ' (renval {σ = < σ >} ρ v)) (renval {σ = < σ >} (ρ' ∘ ρ) v)
  renvalcompSV {i = i} ρ' ρ (neSV x) = neSV∼ (NeEq (rennecomp ρ' ρ x))
  renvalcompSV {σ = σ}{i} ρ' ρ (streamSV h t) = sSV∼ (renvalcomp {σ = σ}{i} ρ' ρ h) (∞renvalcompSV ρ' ρ t)

  ∞renvalcompSV : ∀{Γ Δ E σ i} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : ∞StreamVal (Val Γ σ) (Ne Γ < σ >)) → 
              ∞renvalSV {σ = σ} ρ' (∞renvalSV {σ = σ} ρ v) ∞SV⟨ i ⟩∼ ∞renvalSV {σ = σ} (ρ' ∘ ρ) v 
  ∼force (∞renvalcompSV {σ = σ} ρ' ρ v) = renvalcompSV ρ' ρ (vforce v)



Env : Con → Con → Set
Env Γ Δ = ∀{σ} → Var Γ σ → Val Δ σ


_<<_ : ∀{Γ Δ} → Env Γ Δ → ∀{σ} → Val Δ σ → Env (Γ < σ) Δ
(γ << v) vze = v
(γ << v) (vsu x) = γ x 

-- notice that I have written it with 3 explicit arguments rather than
-- two, this is because Env computes to:

-- ∀{Γ} → (∀{σ} → Var Γ σ → Val σ) → ∀{σ} → Val σ → ∀{σ'} → 
-- Var (Γ < σ) σ' → Val σ'
 
-- which has three explicit arguments.

-- Notice also that the definition of _<<_ looks a bit like lookup ,
-- this is because the new definition of Env is a lookup function in a
-- way, so to define a new longer environment we need to explain how
-- to lockup variables in it.


renval<< : ∀{Γ Δ E σ} → (ρ : Ren Δ E) → (γ : Env Γ Δ) → (v : Val Δ σ) → ∀{τ}(x : Var (Γ < σ) τ) → 
         (renval {σ = τ} ρ ∘ (γ << v)) x ≅ ((λ {σ'} → renval {σ = σ'} ρ ∘ γ) << renval {σ = σ} ρ v) x
renval<< ρ γ v vze = refl
renval<< ρ γ v (vsu x) = refl