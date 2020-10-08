module Prelude where

  open import Level
    renaming (suc to ℓ+1; zero to ℓ0; _⊔_ to _ℓ⊔_)
    public
  
  open import Agda.Builtin.Unit
    public

  open import Data.Unit.NonEta 
    public

  open import Data.Empty 
    public 

  open import Data.Nat 
    renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
    public

  open import Data.Nat.Properties
    hiding (≡-irrelevant)
    public

  open import Data.List 
    renaming (map to List-map ; filter to List-filter ; lookup to List-lookup)
    hiding (fromMaybe; [_])
    public

  open import Data.List.Properties 
    renaming (≡-dec to List-≡-dec; length-map to List-length-map)
    using (∷-injective)
    public

  open import Data.List.Relation.Unary.Any
    using (Any; here; there)
    renaming (lookup to Any-lookup; map to Any-map; satisfied to Any-satisfied
             ;index to Any-index)
    public

  open import Data.List.Relation.Unary.Any.Properties
    renaming (map⁻ to Any-map⁻)
    using ()
    public

  open import Data.List.Relation.Unary.Any.Properties
    using    (¬Any[])
    renaming ( map⁺      to Any-map⁺
             ; map⁻      to Any-map⁻
             ; concat⁺   to Any-concat⁺
             ; concat⁻   to Any-concat⁻
             )
    public

  open import Data.List.Relation.Unary.All
    using (All; []; _∷_)
    renaming (head to All-head; tail to All-tail; 
              lookup to All-lookup; tabulate to All-tabulate;
              reduce to All-reduce)
    public

  open import Data.List.Relation.Unary.All.Properties
    renaming ( tabulate⁻ to All-tabulate⁻
             ; tabulate⁺ to All-tabulate⁺
             ; map⁺      to All-map⁺
             ; map⁻      to All-map⁻
             )
    public

  open import Data.List.Membership.Propositional
    using (_∈_)
    public 

  open import Data.Vec
    using (Vec; []; _∷_)
    renaming (replicate to Vec-replicate; lookup to Vec-lookup
             ;map to Vec-map; head to Vec-head; tail to Vec-tail
             ;updateAt to Vec-updateAt; tabulate to Vec-tabulate
             ;allFin to Vec-allFin; toList to Vec-toList; fromList to Vec-fromList)
    public

  open import Data.Vec.Properties
    using ()
    renaming (updateAt-minimal to Vec-updateAt-minimal
             ;[]=⇒lookup to Vec-[]=⇒lookup
             ;lookup⇒[]= to Vec-lookup⇒[]=)
    public

  open import Data.List.Relation.Binary.Pointwise 
    using (decidable-≡)
    public

  open import Data.Bool 
    renaming (_≟_ to _≟Bool_)
    hiding (_≤?_; _<_; _<?_; _≤_)
    public

  open import Data.Maybe 
    renaming (map to Maybe-map; zip to Maybe-zip ; _>>=_ to _Maybe->>=_)
    hiding (align; alignWith; zipWith)
    public

  open import Data.Maybe.Relation.Unary.Any
    renaming (Any to Maybe-Any; dec to Maybe-Any-dec)
    hiding (map; zip; zipWith; unzip ; unzipWith)
    public

  maybe-any-⊥ : ∀{a}{A : Set a} → Maybe-Any {A = A} (λ _ → ⊤) nothing → ⊥
  maybe-any-⊥ ()

  open import Data.Maybe.Properties
    using (just-injective)
    renaming (≡-dec to Maybe-≡-dec)
    public

  open import Data.Fin
    using (Fin; suc; zero; fromℕ; fromℕ≤ ; toℕ ; cast)
    renaming (_≟_ to _≟Fin_; _≤_ to _≤Fin_ ; _<_ to _<Fin_; inject₁ to Fin-inject₁; inject+ to Fin-inject+)
    public

  fins : (n : ℕ) → List (Fin n)
  fins n = Vec-toList (Vec-allFin n)

  open import Relation.Binary.PropositionalEquality
    hiding (decSetoid)
    public

  open import Relation.Binary.HeterogeneousEquality
    using (_≅_)
    renaming (cong to ≅-cong; cong₂ to ≅-cong₂)
    public

  open import Relation.Binary.Core
    public
 
  open import Data.Sum
    public
  
  open import Function
    using (_∘_; id; case_of_; _on_; typeOf; flip; const)
    public

  open import Data.Product
    renaming (map to ×-map; map₂ to ×-map₂; <_,_> to split; swap to ×-swap)
    hiding (map₁; zip)
    public

  open import Data.Product.Properties
    public
 
  open import Relation.Nullary
    hiding (Irrelevant)
    public

  open import Relation.Nullary.Negation
    using (contradiction)
    public

  open import Relation.Binary
    using (Setoid)
    public
