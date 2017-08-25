module Examples where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Empty
open import Data.Unit.Base
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid )

open import Helpers
open import AST
open import Execute

----------------------------
-- An valid graphQL query according to specification
--
-- https://github.com/facebook/graphql/blob/master/spec/Section%205%20--%20Validation.md
----------------------------

{-
query getDogName {
  dog {
    name
  }
}
query getOwnerName {
  dog {
    owner {
      name
    }
  }
}
-}

valid₁ : Document
valid₁ = document (
  operationDefinition query "getDogName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₂ "name"
    ])
  ]) ∷
  operationDefinition query "getOwnerName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "owner" (selectionSet [
        field₂ "name"
      ])
    ])
  ])
  ∷ [] )


----------------------------
-- An invalid graphQL query according to specification
----------------------------

{-
query getName {
  dog {
    name
  }
}

query getName {
  dog {
    owner {
      name
    }
  }
}
-}

----------------------------
-- An invalid graphQL query according to specification because both operations have the same name.
-- Compiling this raises a compiler warning
----------------------------
invalid₁ : Document
invalid₁ = document (
  operationDefinition query "getName1" (selectionSet [
    field₁ "dog" (selectionSet [
      field₂ "name"
    ])
  ]) ∷
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "owner" (selectionSet [
        field₂ "name"
      ])
    ])
  ])
  ∷ [] )


----------------------------
-- A simple query
----------------------------

{-

query getDogName {
  dog {
    name 
  }
}

-}

simple : Document
simple = document (
  operationDefinition query "getDogName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₂ "name"
    ])
  ])
  ∷ [] )


----------------------------
-- A query with a fragment
----------------------------

{-
query getName {
  dog {
    ...DogFields
  }
}

fragment DogField on Dog {
  name 
  ... MoreDogFields
}

fragment MoreDogFields on Dog {
  favoriteFood 
}
-}

fragment : Document
fragment = document (
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet [
      fragmentSpread "DogField"
    ])
  ]) ∷
  fragmentDefinition "DogField" (selectionSet (
    (field₂ "name") ∷
    (fragmentSpread "MoreDogFields") ∷ []
  )) ∷
  fragmentDefinition "MoreDogFields"  (selectionSet [
    field₂ "favoriteFood"
  ])
  ∷ [] )

----------------------------
-- The same query as above after inlining the fragments.
----------------------------

{-

query getName {
  dog {
    name 
    favoriteFood
  }
}

-}

fragmentInlined : Document
fragmentInlined = document (
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet (
      (field₂ "name") ∷
      (field₂ "favoriteFood") ∷ []))
  ])
  ∷ [] )

----------------------------
-- Proof the inlined fragment has same outcome as fragment
----------------------------
proof₁ : (executeDocument fragment) ≡ (executeDocument fragmentInlined)
proof₁ = refl

----------------------------
-- Some transformation on a graph QL query that should not alter the outcome
----------------------------
transform : Document -> Document
transform d = d

----------------------------
-- Proof that transform does not alter the outcome
----------------------------
proof₂ : {d : Document} -> (executeDocument d) ≡ (executeDocument (transform d))
proof₂ = refl
