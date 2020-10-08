open import Prelude

module Universe.Codes where

 data Atom (n : ℕ) : Set where
   var : Fin n → Atom n
   nat : Atom n

 data All-Atom {#n}(P : Fin #n → Set) : Atom #n → Set where
   here : ∀{i} → P i → All-Atom P (var i)

 ⟦_⟧ₐ_ : {n : ℕ} → Atom n → (Fin n → Set) → Set
 ⟦ var x ⟧ₐ f = f x
 ⟦ nat   ⟧ₐ _ = ℕ

 Prod : ℕ → Set
 Prod n = List (Atom n)

 Sum : ℕ → Set
 Sum n = List (Prod n)

 Fam : ℕ → Set
 Fam n = Vec (Sum n) n

 ⟦_⟧_ : {n : ℕ} → Sum n → (Fin n → Set) → Set
 ⟦ sop ⟧ f = Any (All (flip ⟦_⟧ₐ_ f)) sop

 module Interp {#n}(φ : Fam #n) where

  -- An index into the family
  Ix : Set 
  Ix = Fin #n

  -- An environment is a list of types in the family
  -- TODO: how about literals?
  Env : ℕ → Set
  Env = Vec Ix

  -- Interpretation for atoms
  data A (val : ∀{j} → Env j → Ix → Set) : ∀{k} → Env k → Atom #n → Set where
    var : ∀{k ix}{Γ : Env k} → val Γ ix → A val Γ (var ix)
    nat : ℕ → A val [] nat

  -- A value of type (Val Γ i) represents a value of type lookupᵥ φ i
  -- with /exactly/ length Γ holes; typed accordingly.
  data Val : ∀{j} → Env j → Ix → Set where
    hole : ∀{j}{Γ : Env j} → (v : Fin j) → Val Γ (Vec-lookup Γ v)
    roll : ∀{k}{i : Ix}{Γ : Env k}
         → Any (All (A Val Γ)) (Vec-lookup φ i)
         → Val Γ i


