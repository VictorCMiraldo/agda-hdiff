open import Function
open import Data.Empty
open import Data.Product
  using (∃-syntax; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; pred; _-_) 
  renaming (zero to fz; suc to fs; _<_ to _<Fin_; _≟_ to _≟Fin_)
open import Data.Vec 
  renaming (_++_ to _++ᵥ_; lookup to lookupᵥ; tabulate to Vec-tabulate; updateAt to Vec-updateAt
           ;zip to Vec-zip)
open import Data.Vec.Relation.Unary.All
  renaming (All to Vec-All; map to Vec-All-map; lookup to Vec-All-lookup; tabulate to Vec-All-tabulate)
open import Data.List renaming (length to List-length)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All
  renaming (lookup to All-lookup)
open import Data.List.Relation.Unary.Any
  renaming (map to Any-map; satisfied to Any-satisfied; lookup to Any-lookup; index to Any-index)
open import Data.List.Relation.Unary.Any.Properties
  renaming (lookup-result to Any-lookup-result)
  hiding (swap)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- So... as G. Allais already pointed out: proving linear stuff with Agda is a pain;
-- He set out to use a notion of a /leftover/ in his "Typing with Leftovers" 
-- (https://drops.dagstuhl.de/opus/volltexte/2018/10049/pdf/LIPIcs-TYPES-2017-1.pdf)
--
-- Here, we try to lift that idea to a sop-style mutually recursive family and define
-- a 'Holes' datatype much like in simplistic-generics (https://hackage.haskell.org/package/simplistic-generics-2.0.0/docs/Generics-Simplistic-Deep.html#t:HolesAnn) but such that each variable occurs exaclty once.
module Universe.LinearGenerics where

 ------------------
 -- Agda prelims --

 Any-witness : ∀ {a}{A : Set a}{xs : List A}{P : A → Set}→ Any P xs → Σ A (λ a → P a × a ∈ xs)
 Any-witness (here px) = _ , px , here refl
 Any-witness (there r) 
   with Any-witness r
 ...| a , pa , pr = a , pa , there pr

 Any-zip : ∀{a}{A : Set a}{l : List A}{P Q : A → Set}
         → Any P l → Any Q l
         → Maybe (∃[ x ] (P x × Q x × x ∈ l))
 Any-zip (here px)  (here qx)  = just (_ , (px , qx , here refl))
 Any-zip (there px) (there qx) 
   with Any-zip px qx
 ...| nothing = nothing
 ...| just (r , (p , q , prf)) = just (r , (p , q , there prf))
 Any-zip _ _ = nothing

 ----------------------
 -- Generic Universe --

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

 ----------------------------------------------
 -- Generic Interpretation, fixed a family φ --

 module Interp {#n : ℕ}(φ : Fam #n) where

  -- An index into the family
  Type : Set 
  Type = Fin #n

  defOf : Type → Sum #n
  defOf = lookupᵥ φ

  -- A context is a vector of types
  Ctx : ℕ → Set
  Ctx = Vec Type

  -- Proves that a type is an element of a context
  data _∈Ctx_ (t : Type) : ∀{n} → Ctx n → Set where
    here  : ∀{n}{γ : Ctx n}    → t ∈Ctx (t ∷ γ)
    there : ∀{t' n}{γ : Ctx n} → t ∈Ctx γ → t ∈Ctx (t' ∷ γ)

  ∈Ctx-lookup : ∀{n t}{γ : Ctx n}{P : Type → Set} → Vec-All P γ → t ∈Ctx γ → P t
  ∈Ctx-lookup [] ()
  ∈Ctx-lookup (px ∷ vall) here = px
  ∈Ctx-lookup (px ∷ vall) (there prf) = ∈Ctx-lookup vall prf

  ∈Ctx⇒¬∅ : ∀{t n}{γ : Ctx n} → t ∈Ctx γ → n ≢ 0
  ∈Ctx⇒¬∅ here        = λ ()
  ∈Ctx⇒¬∅ (there prf) = λ ()

  -- Returns the context with the selected type removed
  _-_ : ∀{t n}(γ : Ctx (suc n)) → t ∈Ctx γ → Ctx n
  (_ ∷ Γ) - here        = Γ
  (γ ∷ Γ) - (there prf@(here))    = γ ∷ (Γ - prf)
  (γ ∷ Γ) - (there prf@(there _)) = γ ∷ (Γ - prf)

  ∈Ctx-rm : ∀{n t}{γ : Ctx (suc n)}{P : Type → Set} 
          → Vec-All P γ → (prf : t ∈Ctx γ) → Vec-All P (γ - prf)
  ∈Ctx-rm (px ∷ vall) here = vall
  ∈Ctx-rm (px ∷ vall) (there here) = px ∷ ∈Ctx-rm vall here
  ∈Ctx-rm (px ∷ vall) (there (there prf)) = px ∷ ∈Ctx-rm vall (there prf)

  ∈Ctx-set : ∀{n t}{γ : Ctx n}{P : Type → Set} → Vec-All P γ → (ix : t ∈Ctx γ) → P t → Vec-All P γ 
  ∈Ctx-set (px ∷ vall) here pt = pt ∷ vall
  ∈Ctx-set (px ∷ vall) (there ix) pt = px ∷ ∈Ctx-set vall ix pt

  -- A Type can be fresh or stale; this is called 'Usage' on Allais paper
  data UType : Type → Set where
    fresh stale : ∀{t} → UType t

  -- A 'UCtx' indexes each type in the context with usage information,
  -- this is also called 'Usage' on Allais paper
  data UCtx : ∀{n} → Ctx n → Set where
    []  : UCtx []
    _∷_ : ∀{n t}{ts : Ctx n} → UType t → UCtx ts → UCtx (t ∷ ts)

  UCtx-∷-injective : ∀{t n}{γ : Ctx n}{ut ut' : UType t}{Γ Γ' : UCtx γ}
                   → _≡_ {A = UCtx (t ∷ γ)} (ut ∷ Γ) (ut' ∷ Γ')
                   → ut ≡ ut' × Γ ≡ Γ'
  UCtx-∷-injective refl = refl , refl

  -- There exists a cannonical partial order on variable usage.
  -- If Γ ⊆ Γ', then Γ' uses at least the same varables than Γ
  --
  data _⊆_ : {n : ℕ}{γ : Ctx n} → UCtx γ → UCtx γ → Set where
    empty : [] ⊆ []
    keep  : ∀{t n}{γ : Ctx n}{ut : UType t}{Γ Δ : UCtx γ}
          → Γ ⊆ Δ → (ut ∷ Γ) ⊆ (ut ∷ Δ)
    use   : ∀{t n}{γ : Ctx n}{Γ Δ : UCtx γ}
          → Γ ⊆ Δ → (fresh {t} ∷ Γ) ⊆ (stale {t} ∷ Δ)

  ⊆-refl : ∀{n}{γ : Ctx n}{Γ : UCtx γ} → Γ ⊆ Γ
  ⊆-refl {Γ = []} = empty
  ⊆-refl {Γ = ut ∷ Γ} = keep ⊆-refl

  ⊆-trans : ∀{n}{γ : Ctx n}{Γ Δ Θ : UCtx γ} → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
  ⊆-trans empty empty = empty
  ⊆-trans (keep gd) (keep dt) = keep (⊆-trans gd dt)
  ⊆-trans (keep gd) (use dt) = use (⊆-trans gd dt)
  ⊆-trans (use gd) (keep dt) = use (⊆-trans gd dt)
 
  ⊆-antisym : ∀{n}{γ : Ctx n}{Γ Δ : UCtx γ} → Γ ⊆ Δ → Δ ⊆ Γ → Γ ≡ Δ
  ⊆-antisym empty empty = refl
  ⊆-antisym (keep gd) (keep dg) rewrite ⊆-antisym gd dg = refl
  ⊆-antisym (use gd) ()

  -- Lift removal of elemetns into UCtx
  _-'_ : ∀{t n}{γ : Ctx (suc n)}(Γ : UCtx γ)(prf : t ∈Ctx γ) → UCtx (γ - prf)
  (_ ∷ Γ) -' here        = Γ
  (γ ∷ Γ) -' (there prf@(here))    = γ ∷ (Γ -' prf)
  (γ ∷ Γ) -' (there prf@(there _)) = γ ∷ (Γ -' prf)

  liftCtx : ∀{n : ℕ} → ((t : Type) → UType t) → (γ : Ctx n) → UCtx γ
  liftCtx f []       = []
  liftCtx f (t ∷ ts) = f t ∷ liftCtx f ts

  allFresh : ∀{n : ℕ}(γ : Ctx n) → UCtx γ
  allFresh = liftCtx (λ t → fresh {t})

  allStale : ∀{n : ℕ}(γ : Ctx n) → UCtx γ
  allStale = liftCtx (λ t → stale {t})

  liftCtx-natural : ∀{t' n}(f : (t : Type) → UType t)(γ : Ctx (suc n))(prf : t' ∈Ctx γ)
                  → liftCtx f (γ - prf) ≡ liftCtx f γ -' prf
  liftCtx-natural f (x ∷ γ) here = refl
  liftCtx-natural f (x ∷ γ) (there prf@(here))    = cong (f x ∷_) (liftCtx-natural f γ prf) 
  liftCtx-natural f (x ∷ γ) (there prf@(there _)) = cong (f x ∷_) (liftCtx-natural f γ prf) 

  -- Typing rule for vars: value of type "Φᵥ Γ x t Δ" states that
  -- typing variable x with t in Γ transforms it into Δ = Γ{x := stale}
  data Φᵥ : {n : ℕ}{γ : Ctx n} → UCtx γ → Fin n → Type → UCtx γ → Set where
    z : ∀{n t}{γ : Ctx n}{Γ : UCtx γ} 
      → Φᵥ (fresh {t} ∷ Γ) fz t (stale {t} ∷ Γ)

    s : ∀{n t t'}{ut : UType t}{γ : Ctx n}{Γ Δ : UCtx γ}{x : Fin n}
      → Φᵥ Γ x t' Δ
      → Φᵥ (ut ∷ Γ) (fs x) t' (ut ∷ Δ)
    
  mutual
   data Φₐ : {n : ℕ}{γ : Ctx n} → UCtx γ → Atom #n → UCtx γ → Set where
     var : ∀{n t}{γ : Ctx n}{Γ Δ : UCtx γ}
         → Φₛ Γ t Δ → Φₐ Γ (var t) Δ
     nat : ∀{n}{γ : Ctx n}{Γ : UCtx γ}
         → ℕ → Φₐ Γ nat Γ

   data Φₚ : {n : ℕ}{γ : Ctx n} → UCtx γ → Prod #n → UCtx γ → Set where
     []  : ∀{n}{γ : Ctx n}{Γ : UCtx γ} 
         → Φₚ Γ [] Γ
     _∷_ : ∀{n}{γ : Ctx n}{Γ Δ Θ : UCtx γ}{ps : Prod #n}{p : Atom #n}
         → Φₐ Γ p Δ → Φₚ Δ ps Θ → Φₚ Γ (p ∷ ps) Θ

   data Φₛ : {n : ℕ}{γ : Ctx n} → UCtx γ → Type → UCtx γ → Set where
     hole : ∀{n t}{γ : Ctx n}{Γ Δ : UCtx γ}{v : Fin n} 
          → Φᵥ Γ v t Δ 
          → Φₛ Γ t Δ
     roll : ∀{n t}{γ : Ctx n}{Γ Δ : UCtx γ}
          → Any (λ p → Φₚ Γ p Δ) (defOf t)
          → Φₛ Γ t Δ

   -- Finally, we define an element of a mutually recursive family with
   -- n holes typed according to γ as a Φₛ that receives a list of
   -- fresh resources and transforms them into a list of stale resources.
   El : {n : ℕ} → Ctx n → Type → Set
   El γ t = Φₛ (allFresh γ) t (allStale γ) 

   Val : Type → Set
   Val = El []

   _≟UCtx_ : ∀{n}{γ : Ctx n}(Γ Δ : UCtx γ) → Dec (Γ ≡ Δ)
   _≟UCtx_ []     [] = yes refl
   _≟UCtx_ (fresh ∷ Γ) (fresh ∷ Δ)
     with  Γ ≟UCtx Δ
   ...| yes refl = yes refl
   ...| no  imp  = no (imp ∘ proj₂ ∘ UCtx-∷-injective)
   _≟UCtx_ (stale ∷ Γ) (stale ∷ Δ) 
     with  Γ ≟UCtx Δ
   ...| yes refl = yes refl
   ...| no  imp  = no (imp ∘ proj₂ ∘ UCtx-∷-injective)
   _≟UCtx_ (fresh ∷ Γ) (stale ∷ Δ) = no (λ ())
   _≟UCtx_ (stale ∷ Γ) (fresh ∷ Δ) = no (λ ())

   -------------------
   -- * Weakening * --
   --
   -- This representation supports weakening

   {-# TERMINATING #-}
   weakenₛ : ∀{t t' n}{ut' : UType t'}{γ : Ctx n}{Γ Δ : UCtx γ}
           → Φₛ Γ t Δ → Φₛ (ut' ∷ Γ) t (ut' ∷ Δ)

   weakenₐ : ∀{t t' n}{ut' : UType t'}{γ : Ctx n}{Γ Δ : UCtx γ}
           → Φₐ Γ t Δ → Φₐ (ut' ∷ Γ) t (ut' ∷ Δ)
   weakenₐ (var x) = var (weakenₛ x)
   weakenₐ (nat x) = nat x

   weakenₚ : ∀{t t' n}{ut' : UType t'}{γ : Ctx n}{Γ Δ : UCtx γ}
           → Φₚ Γ t Δ → Φₚ (ut' ∷ Γ) t (ut' ∷ Δ)
   weakenₚ []       = []
   weakenₚ (x ∷ xs) = weakenₐ x ∷ weakenₚ xs

   weakenₛ (hole x) = hole (s x)
   weakenₛ (roll x) = roll (Any-map weakenₚ x)

   weaken : ∀{t n}{γ : Ctx n}{Γ : UCtx γ} → Φₛ [] t [] → Φₛ Γ t Γ
   weaken {Γ = []}    x = x
   weaken {Γ = γ ∷ Γ} x = weakenₛ (weaken x)

   subₛ : ∀{t n}{γ : Ctx n}{Γ Δ : UCtx γ}
        → Φₛ Γ t Δ → Γ ⊆ Δ

   subᵥ : ∀{t n}{v : Fin n}{γ : Ctx n}{Γ Δ : UCtx γ}
        → Φᵥ Γ v t Δ → Γ ⊆ Δ
   subᵥ z     = use ⊆-refl
   subᵥ (s v) = keep (subᵥ v)

   subₐ : ∀{t n}{γ : Ctx n}{Γ Δ : UCtx γ}
           → Φₐ Γ t Δ → Γ ⊆ Δ
   subₐ (var x) = subₛ x
   subₐ (nat x) = ⊆-refl

   subₚ : ∀{t n}{γ : Ctx n}{Γ Δ : UCtx γ}
           → Φₚ Γ t Δ → Γ ⊆ Δ
   subₚ []       = ⊆-refl
   subₚ (x ∷ xs) = ⊆-trans (subₐ x) (subₚ xs)

   subₛ (hole x) = subᵥ x
   subₛ (roll x) = subₚ (proj₂ (Any-satisfied x))

   -------------------
   -- * Framing * --
   --
   -- This representation supports framing too: irrelevant resources can be removed

   frameᵥ : ∀{t n}{v : Fin n}{γ : Ctx n}{Γ : UCtx γ} → Φᵥ Γ v t Γ → ⊥
   frameᵥ (s v) = frameᵥ v

   frameₛ : ∀{t n m}{γ : Ctx n}{γ' : Ctx m}{Γ : UCtx γ}{Δ : UCtx γ'} 
         → Φₛ Γ t Γ → Φₛ Δ t Δ

   frameₐ : ∀{t n m}{γ : Ctx n}{γ' : Ctx m}{Γ : UCtx γ}{Δ : UCtx γ'} 
          → Φₐ Γ t Γ → Φₐ Δ t Δ
   frameₐ (var x) = var (frameₛ x)
   frameₐ (nat x) = nat x

   frameₚ : ∀{t n m}{γ : Ctx n}{γ' : Ctx m}{Γ : UCtx γ}{Δ : UCtx γ'} 
          → Φₚ Γ t Γ → Φₚ Δ t Δ
   frameₚ []      = []
   frameₚ {Γ = Γ} (x ∷ p) with ⊆-antisym (subₐ x) (subₚ p)
   ...| refl = frameₐ x ∷ frameₚ p

   frameₛ (hole x) = ⊥-elim (frameᵥ x)
   frameₛ (roll x) = roll (Any-map frameₚ x)

   -------------------------
   -- * Plugging Values * --
   -- 
   -- Next, we'd like to be able to substitute holes for values

   {-# TERMINATING #-}
   plugₛ : ∀{t t'}{n : ℕ}{γ : Ctx (suc n)}{Γ Δ : UCtx γ}
         → (prf : t' ∈Ctx γ) → Val t'
         → Φₛ Γ t Δ → Φₛ (Γ -' prf) t (Δ -' prf)

   plugₐ : ∀{t' a}{n : ℕ}{γ : Ctx (suc n)}{Γ Δ : UCtx γ}
         → (prf : t' ∈Ctx γ) → Val t'
         → Φₐ Γ a Δ → Φₐ (Γ -' prf) a (Δ -' prf)
   plugₐ prf val (var x) = var (plugₛ prf val x)
   plugₐ prf val (nat x) = nat x

   plugₚ : ∀{t' p}{n : ℕ}{γ : Ctx (suc n)}{Γ Δ : UCtx γ}
         → (prf : t' ∈Ctx γ) → Val t'
         → Φₚ Γ p Δ → Φₚ (Γ -' prf) p (Δ -' prf)
   plugₚ prf val [] = []
   plugₚ prf val (x ∷ p) = plugₐ prf val x ∷ plugₚ prf val p

   -- Var is not supposed to be plugged; weaken
   plugₛ here        val (hole z) = weaken val
   plugₛ (there prf) val (hole (s x))
     with prf
   ...| here       = weakenₛ (plugₛ here val (hole x)) 
   ...| there prf' = weakenₛ (plugₛ (there prf') val (hole x))
   -- Var is supposed to be plugged
   plugₛ here        val (hole (s x)) = hole x
   plugₛ (there prf) val (hole z) 
     with prf
   ...| here       = hole z
   ...| there prf' = hole z
   plugₛ prf val (roll x) = roll (Any-map (plugₚ prf val) x)

   plug : ∀{t t'}{n : ℕ}{γ : Ctx (suc n)} 
        → (prf : t' ∈Ctx γ) → Val t'
        → El γ t 
        → El (γ - prf) t
   plug {γ = γ} prf val el 
     with plugₛ {Γ = allFresh γ} {Δ = allStale γ} prf val el
   ...| res rewrite liftCtx-natural (λ _ → fresh) γ prf 
                  | liftCtx-natural (λ _ → stale) γ prf
                  = res
   
   --------------------------------
   -- * Splitting values

   -- a value of type PathTo i t represents a potential location for a subtree of
   -- type t within a tree of type i.
   data PathTo (i : Type) : Type → Set where
     here  : PathTo i i
     roll  : ∀{t} → Any (Any (All-Atom (flip PathTo t))) (lookupᵥ φ i)
           → PathTo i t

   unplugₛ : ∀{n t u}{γ : Ctx n}{Γ Δ : UCtx γ} → PathTo t u → Φₛ Γ t Δ
          → Maybe (Φₛ (fresh {u} ∷ Γ) t (stale {u} ∷ Δ) × Val u)

   unplugₐ : ∀{n t u}{γ : Ctx n}{Γ Δ : UCtx γ} → All-Atom (flip PathTo u) t
           → Φₐ Γ t Δ → Maybe (Φₐ (fresh {u} ∷ Γ) t (stale {u} ∷ Δ) × Val u)
   unplugₐ (here x) (var x₁)
     with unplugₛ x x₁
   ...| nothing = nothing
   ...| just (r , v) = just (var r , v)

   unplugₚ : ∀{n t u}{γ : Ctx n}{Γ Δ : UCtx γ} → Any (All-Atom (flip PathTo u)) t
           → Φₚ Γ t Δ → Maybe (Φₚ (fresh {u} ∷ Γ) t (stale {u} ∷ Δ) × Val u)
   unplugₚ (here px) (x ∷ p)
     with unplugₐ px x
   ...| nothing = nothing
   ...| just (r , v) = just (r ∷ weakenₚ p , v)
   unplugₚ (there q) (x ∷ p) 
     with unplugₚ q p
   ...| nothing = nothing
   ...| just (r , v) = just (weakenₐ x ∷ r , v)

   unplugₛ {Γ = Γ} {Δ} here x 
     with Γ ≟UCtx Δ
   ...| yes refl = just (hole z , frameₛ x)
   ...| no  _    = nothing
   unplugₛ (roll _) (hole _) = nothing
   unplugₛ (roll p) (roll x)
     with Any-zip p x
   ...| nothing = nothing
   ...| just (pᵢ , (pr , xr , pᵢ∈x)) 
     with unplugₚ pr xr
   ...| nothing = nothing
   ...| just (r , v) = just (roll (Any-map (λ { refl → r }) pᵢ∈x) , v)

   unplug : ∀{n t u}{γ : Ctx n}
          → PathTo t u
          → El γ t
          → Maybe (El (u ∷ γ) t × Val u)
   unplug p el = unplugₛ p el
           
   -- We might be able to translate `hdiff` patience patches
   -- into push-pop edit scripts.

   data EditOp (t : Type) : ∀{n m} → Ctx n → Ctx m → Set where
     push   : ∀{n u}{e : Ctx n} → PathTo t u         → EditOp t e (u ∷ e)
     pop    : ∀{n u}{e : Ctx (suc n)}(ix : u ∈Ctx e) → EditOp t e (e - ix) 
     swap   : ∀{n u}{e : Ctx n}(ix ix' : u ∈Ctx e) → EditOp t e e
     repl   : ∀{n u}{e : Ctx n}(ix : u ∈Ctx e) → Val u → EditOp t e e

  apply-eop : ∀{i k k'}{Γ : Ctx k}{Γ' : Ctx k'}
            → EditOp i Γ Γ'
            → El Γ i → Vec-All Val Γ
            → Maybe (El Γ' i × Vec-All Val Γ')
  apply-eop (swap ix ix') el as = 
    let eix  = ∈Ctx-lookup as ix
        eix' = ∈Ctx-lookup as ix'
     in just (el , ∈Ctx-set (∈Ctx-set as ix eix') ix' eix)
  apply-eop (repl ix val) el as = just (el , ∈Ctx-set as ix val)
  apply-eop (push x)  el as 
    with unplug x el 
  ...| nothing      = nothing
  ...| just (r , v) = just (r , v ∷ as)
  apply-eop (pop ix) el as 
    = just (plug ix (∈Ctx-lookup as ix) el , ∈Ctx-rm as ix)

  data ES (i : Type) : ∀{k k'} → Ctx k → Ctx k' → Set where
    []  : ES i [] []
    _∷_ : ∀{k k' k''}{e : Ctx k}{e' : Ctx k'}{e'' : Ctx k''}
        → EditOp i e e' → ES i e' e'' → ES i e e''

  apply-es : ∀{i k k'}{Γ : Ctx k}{Γ' : Ctx k'}
           → ES i Γ Γ'
           → El Γ i → Vec-All Val Γ
           → Maybe (El Γ' i × Vec-All Val Γ')
  apply-es []       el as = just (el , as)
  apply-es (e ∷ es) el as 
    with apply-eop e el as
  ...| nothing = nothing
  ...| just (el' , as') = apply-es es el' as'

  apply : ∀{i} → ES i [] [] → Val i → Maybe (Val i)
  apply es v with apply-es es v []
  ...| nothing = nothing
  ...| just (e' , _) = just e'

  

 module Example where

  famRose : Fam 2
  famRose = l  ∷ r ∷ []
    where
      l : Sum 2
      l = [] ∷ (var (fs fz) ∷ var fz ∷ []) ∷ []
 
      r : Sum 2
      r = (nat ∷ var fz ∷ []) ∷ []

  open Interp famRose
   
  rose : Type
  rose = fs fz

  list : Type
  list = fz

  r1 : ℕ → El [] rose
  r1 n = roll (here ((nat n) ∷ ((var (roll (here []))) ∷ [])))

  l1 : El (list ∷ rose ∷ []) list
  l1 = roll (there (here (var (hole (s z)) ∷ var (hole z) ∷ [])))

  l2 : El (list ∷ rose ∷ []) list
  l2 = roll (there (here (var (frameₛ (r1 42)) ∷ var l1 ∷ [])))

  l4 : El [] rose → El [] rose → El [] list
  l4 a b = roll (there (here (var a ∷ var (roll (there (here (var b ∷ var (roll (here [])) ∷ [])))) ∷ [])))

  elm : ℕ → PathTo list rose
  elm 0       = roll (there (here (here (here here))))
  elm (suc n) = roll (there (here (there (here (here (elm n))))))

  l3 : Maybe (El (list ∷ rose ∷ []) list)
  l3 with unplug (elm 0) l2 
  ...| nothing      = nothing
  ...| just (r , v) = just (plug here v r)

  mswap : ES list [] []
  mswap = push (elm 0) 
       ∷ push (elm 1)
       ∷ swap here (there here)
       ∷ pop here
       ∷ pop here
       ∷ []

  
  tester : apply mswap (l4 (r1 42) (r1 21)) ≡ just (l4 (r1 21) (r1 42))
  tester = refl
  
