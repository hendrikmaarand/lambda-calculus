module Examples where

open import Data.Nat hiding (_<_)

open import Lambda


open import Level public
  using (Level) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary public
  using (Setoid; module Setoid)

import Relation.Binary.PreorderReasoning
module Pre = Relation.Binary.PreorderReasoning


∼setoid : (Γ : Con)(σ : Ty) → Setoid lzero lzero
∼setoid Γ σ = record
  { Carrier       = Tm Γ σ
  ; _≈_           = _∼_
  ; isEquivalence = record
    { refl  = refl∼
    ; sym   = sym∼
    ; trans = trans∼
    }
  }


module ∼-Reasoning {Γ : Con}{σ : Ty} where
  open Pre (Setoid.preorder (∼setoid Γ σ )) public
    renaming (_≈⟨⟩_ to _∼⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∼⟨_⟩_; begin_ to proof_)


id : ∀{Γ} → Tm Γ (ι ⇒ ι)
id = lam (var vze)

appvars : ∀{Γ} → Tm ((Γ < ι) < (ι ⇒ ι)) ι
appvars = app (var vze) (var (vsu vze))

idapp : ∀{Γ} → Tm (Γ < (ι ⇒ ι)) (ι ⇒ ι)
idapp = app (lam (var vze)) (var vze)


pair : ∀{Γ} → Tm (Γ < (nat ∧ nat)) (nat ∧ nat)
pair = var vze


fst-proj : ∀{Γ} → Tm (Γ < (ι ∧ ι)) (ι ∧ ι)
fst-proj = fst (var vze ,, var vze)

--sub (sub<< var (lam (var vze))) appvars

plus-one : ∀{Γ} → ℕ → Tm Γ nat
plus-one zero = su ze
plus-one (suc n) = su (plus-one n)

stream : ∀{Γ} → Tm Γ < nat >
stream = tup plus-one

stream[1] : ∀{Γ} → Tm Γ nat
stream[1] = proj (suc zero) stream

