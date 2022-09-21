module Lectures.Week1 where

{- Administrivia -}

-- Welcome to CS410 Advanced Functional Programming

-- The team:
--    Fredrik Nordvall Forsberg
--    Sean Watters
--    Georgi Nakov
--    Conor McBride

-- Mattermost:
--   https://mattermost.cis.strath.ac.uk/learning/channels/cs410-22-23

-- One minute papers:
--   please fill them in (will be used for feedback, and taking attendance)

-- Covid:
--   help yourself to a mask
--   if you are sick, STAY HOME; you can watch on Zoom if you have to


-- Timetable:
--   Tue 12noon  lab     LT1221
--   Tue 2pm     lecture LT714    <-- you are here
--   Tue 3pm-5pm lab     LT1221
--   Thu 10am    lecture SW108

-- Assessment: 100% Coursework

--   One   30%  due Monday 10 October  (W4)
--   Two   30%  due Monday 31 October  (W7)
--   Three 40%  due Monday  5 December (W12)

-- Submitting the coursework

-- 1. Make a private repo somewhere, invite me to it
-- 2. Add class repo as new remote
-- 3. Pull from class repo, push to your repo
-- 4. Let me know when you are done
-- 5. Schedule an appointment to discuss at least one coursework

{- Getting started with Agda -}

-- This is a comment

{- And this is a multiline comment.

   Useful key-bindings:

   C-c C-l     load file

 -}

const : {A B : Set} -> A -> B -> A
const a = λ _ → a

data List (X : Set) : Set where
  [] : List X
  _::_ : X -> List X -> List X

append : {X : Set} -> List X -> List X -> List X
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

open import Data.Nat
open import Data.Bool

-- _!!_ : ∀ {A} → List A -> ℕ -> A -- (C)

-- open import Data.Maybe -- (C)

-- precise version -- (F)

-- find : {A : Set}{n : ℕ} -> (A -> Bool) -> Vec A n -> Maybe (Fin n)
