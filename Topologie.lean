import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

open Set 
open Function
/-
variable {X : Type _} {T : Set (Set X)}

def axiome.vide := 
∅ ∈ T

--#check axiome.vide

def axiome.intersec := 
∀ s t,  s ∈ T → t ∈ T → s ∩ t ∈ T

def axiome.union :=
∀ S, (∀ t ∈ S, t ∈ T ) → (sUnion S) ∈ T 

def axiome.total := 
univ ∈ T
-/
--def topologie {X : Type u} {T : Set (Set X)} := 
--@axiome.vide X T → @axiome.union X T → @axiome.intersec X T → @axiome.total X T

class topologie (X : Type u) where
  T : Set (Set X)
  vide : ∅ ∈ T
  intersec : ∀ s t,  s ∈ T → t ∈ T → s ∩ t ∈ T
  union : ∀ S, (∀ t ∈ S, t ∈ T ) → (sUnion S) ∈ T 
  total : univ ∈ T

open topologie

namespace Definitions

def EspaceTopologique := Type 

variable {X : EspaceTopologique} [topologie X]

lemma theoreme.vide : (∅ : Set X) ∈ T := topologie.vide 

lemma theoreme.intersec : ∀ s t : Set X,  s ∈ T → t ∈ T → s ∩ t ∈ T := topologie.intersec

lemma theoreme.union : ∀ S : Set (Set X), (∀ t ∈ S, t ∈ T ) → (sUnion S) ∈ T := topologie.union

lemma theoreme.total : (univ : Set X) ∈ T := topologie.total


-- Une partie ouverte de X est un élément de T
def ouvert (S : Set X) := 
S ∈ T 


-- maintenant pour deaduction :
lemma definition.ouvert : (ouvert S) ↔ (S : Set X) ∈ T  :=
--begin inutile dans lean4
  refl _

-- On a par définition qu'une intersection simple d'ouverts est un ouvert
-- On veut montrer qu'une intersection finie d'ouverts est un ouvert
--lemma theoreme.intersecfinie {h : topologie X} : 

variable {Y : EspaceTopologique} [topologie Y]

def cont (f : X → Y) :=
∀ S : Set Y, ouvert S → ouvert (f ⁻¹' S)

/-
lemma definition.continue : ∀ S : Set Y, ouvert S → ouvert (f ⁻¹' S) := 
refl _-/

def connexe (X : EspaceTopologique) [topologie X] := 
∀ U V : Set X, ouvert U → ouvert V → U ∩ V = ∅ → U ∪ V = univ → U ≠ ∅ → V = ∅


-- lemma definition.connexe

lemma exercice.imageConnexe (f : X → Y) (h1 : cont f) (h2 : connexe X) (h3 : Surjective f) : connexe Y :=
sorry

def connexePartie {X : EspaceTopologique} [topologie X] (A : Set X):= 
∀ U V : Set X, ouvert U → ouvert V → A ∩ U ∩ V = ∅ → A ⊂ U ∪ V → A ∩ U ≠ ∅ → A ∩ V = ∅

lemma exercice.imageConnexePartie (f : X → Y) (h1 : cont f) (h2 : connexe X)  : connexePartie (f '' univ) :=
sorry

--lemma exercice.caractConnex (f : X → {0, 1}) 


inductive Weekday where
  | sunday
  | monday



