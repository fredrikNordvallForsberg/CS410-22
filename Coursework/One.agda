{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- CS410 Advanced Functional Programming 2022
--
-- Coursework 1
------------------------------------------------------------------------

module Coursework.One where

----------------------------------------------------------------------------
-- COURSEWORK 1 -- WARMING UP, LOGIC, AND GRAY SCALE IMAGE MANIPULATION
--
-- VALUE:     30% (divided over 60 marks, ie each mark is worth 0.5%)
-- DEADLINE:  5pm, Monday 10 October (Week 4)
--
-- SUBMISSION: Create your own clone of CS410 repo somewhere of your
-- choosing (e.g. Gitlab, Github, or Bitbucket), and let Fred know
-- where, so that you can invite the CS410 team to the project. The
-- last commit before the deadline is your submitted version. However
-- do get in touch if you want to negotiate about extensions.
----------------------------------------------------------------------------

-- HINT: These are all the imports from the standard library that you
-- should need, although you might of course have to define your own
-- auxiliary functions. When there is no explicit `using` list, you may
-- go hunting in the module for anything you think you might find useful.

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≤ᵇ_; _+_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Nat.Properties
open import Common.NatProperties using (n≡⌊n+n/2⌋; n≡⌈n+n/2⌉)
open import Data.List
  using (List; []; _∷_; _++_; [_])
  renaming (map to ListMap; splitAt to ListSplitAt)
open import Data.Vec
  using (Vec; []; _∷_; lookup)
  renaming (map to VecMap; toList to VecToList)
open import Data.Fin
  using (Fin; zero; suc; toℕ; fromℕ; inject≤; pred)
  renaming (splitAt to FinSplitAt)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤)
import Data.Maybe -- we refrain from opening this module until we need it
open import Function using (_∘_; id; _$_; case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)
open import Data.String hiding (show) renaming (_++_ to _S++_)
open import Data.Char hiding (show; toℕ; fromℕ)
open import Data.Nat.Show renaming (readMaybe to readMaybeNat; show to showNat)
open import Data.Fin.Show renaming (readMaybe to readMaybeFin; show to showFin)
import Level

-- HINT: your tasks are labelled with the very searchable tag '???'

-- TIP: When you load this file, you will see lots of open goals. You
-- can focus on one at a time by using comments {- ... -} to switch
-- off the later parts of the file until you get there.



------------------------------------------------------------------------
-- SOME GOOD OLD FUNCTIONAL PROGRAMMING: TREESORT (10 MARKS in total)
------------------------------------------------------------------------

-- Here is a datatype of node-labelled binary trees:

data Tree (X : Set) : Set where
  leaf : Tree X
  _<[_]>_ : Tree X -> X -> Tree X -> Tree X


{- ??? 1.1 Implement the insertion of a number into a tree, ensuring that
       the numbers in the tree are in increasing order from left to right;
       make sure to retain duplicates.
   (2 MARKS) -}

insertTree : ℕ -> Tree ℕ -> Tree ℕ
insertTree = {!!}

-- HINT: the import list for Data.Nat above might contain useful things

{- ??? 1.2 Implement the function which takes the elements of a list and
       builds an ordered tree from them, using insertTree.
   (1 MARK) -}

makeTree : List ℕ -> Tree ℕ
makeTree = {!!}

{- ??? 1.3 Implement the function which flattens a tree to a list,
       and combine it with makeTree to implement a sorting function.
   (1 MARKS) -}

flatten : {X : Set} -> Tree X -> List X
flatten = {!!}

treeSort : List ℕ -> List ℕ
treeSort = {!!}

-- TIP: You can uncomment the following test cases to check your work. They
-- should all typecheck if you got it right.

{-
_ : treeSort [ 1 ] ≡ [ 1 ]
_ = refl

_ : treeSort (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : treeSort (3 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : treeSort (3 ∷ 2 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ 3 ∷ [])
_ = refl
-}

{- ??? 1.4 implement a fast version of flatten, taking an accumulating
       parameter, never using ++. It should satisfy

          fastFlatten t xs ≡ flatten t ++ xs

       We can use fastFlatten to build a faster version of tree sort.
   (2 MARKS) -}

fastFlatten : {X : Set} -> Tree X -> List X -> List X
fastFlatten leaf = id
fastFlatten (l <[ x ]> r) = fastFlatten l ∘ (x ∷_) ∘ fastFlatten r

fastTreeSort : List ℕ -> List ℕ
fastTreeSort xs = fastFlatten (makeTree xs) []

-- TIP: You can copy and modify the test cases above to check that
-- also fastTreeSort works as intended.

{- ??? 1.5 *Prove* that fastFlatten correctly implements it
       specification.  You will need to prove an additional fact about
       concatenation separately, and use that in the proof.
   (3 MARKS) -}

fastFlattenCorrect : {X : Set} -> (t : Tree X) -> (xs : List X) ->
                     fastFlatten t xs ≡ (flatten t ++ xs)
fastFlattenCorrect = {!!}

{- ??? 1.6 Use fastFlattenCorrect to prove that treeSort and
       fastTreeSort agree. If you stop and think, you should see that
       there is no need to pattern match here. But, again, you will need
       to prove an additional fact about concatenation.
   (1 MARK) -}

fastTreeSortCorrect : (xs : List ℕ) -> fastTreeSort xs ≡ treeSort xs
fastTreeSortCorrect = {!!}

------------------------------------------------------------------------
-- DOUBLEPLUSGOOD NEGATION (20 MARKS in total)
------------------------------------------------------------------------

module Logic where -- To avoid name clashes, we use a local module here

  {- ??? 1.7 Implement the following operations:
     (2 MARKS) -}

  orAdjunctionFrom : {P Q R : Set} → (P ⊎ Q -> R) -> ((P -> R) × (Q -> R))
  orAdjunctionFrom = {!!}

  orAdjunctionTo : {P Q R : Set} → ((P -> R) × (Q -> R)) -> (P ⊎ Q -> R)
  orAdjunctionTo = {!!}

  {- ??? 1.8 Which of the following operations can be implemented?
         For each operation, either give an implementation, or comment
         it out, leaving a comment explaining why it cannot be
         implemented.

         For full marks, it is not enough to give a handwavy
         explanation why something cannot be implemented -- instead,
         show how implementing the operation would make a known
         non-implementable operation implementable, such as the Law of
         Excluded Middle, or Double Negation Elimination.
     (4 MARKS) -}

  contrapositive : {P Q : Set} → (P → Q) → (¬ Q → ¬ P)
  contrapositive = {!!}

  contrapositiveReverse : {P Q : Set} → (¬ Q → ¬ P) → (P → Q)
  contrapositiveReverse = {!!}

  variation1 : {P Q : Set} → (P → ¬ Q) → (Q → ¬ P)
  variation1 = {!!}

  variation2 : {P Q : Set} → (¬ P → Q) → (¬ Q → P)
  variation2 = {!!}

  {- ??? 1.9 Another principle of classical logic which is not provable in
         Agda is Peirce's Law. However show that its double-negation is
         provable.
     (2 MARKS) -}

  ¬¬Peirce : {P Q : Set} → ¬ ¬ (((P -> Q) -> P) -> P)
  ¬¬Peirce = {!!}

  {- ??? 1.10 For each of the following operations, either give an
         implementation, or comment it out and leave a comment
         explaining why it is impossible to implement.
     (4 MARKS) -}

  deMorgan-∀-from : {A : Set}{R : A -> Set} -> ¬ ((x : A) -> R x) -> Σ[ x ∈ A ] (¬ (R x))
  deMorgan-∀-from = {!!}

  deMorgan-∀-to : {A : Set}{R : A -> Set} -> Σ[ x ∈ A ] (¬ (R x)) -> ¬ ((x : A) -> R x)
  deMorgan-∀-to = {!!}

  deMorgan-∃-from : {A : Set}{R : A -> Set} -> ((x : A) -> (¬ (R x))) -> ¬ (Σ[ x ∈ A ] (R x))
  deMorgan-∃-from = {!!}

  deMorgan-∃-to : {A : Set}{R : A -> Set} -> ¬ (Σ[ x ∈ A ] (R x)) -> (x : A) → (¬ (R x))
  deMorgan-∃-to = {!!}

  {- ??? 1.11 Show that double negation is a /monad/; a concept you
         might remember from Haskell (don't worry if you don't, we'll
         get back to it later!). Concretely, you need to implement the
         following two operations:
     (1 MARK) -}

  return : {P : Set} → P -> ¬ ¬ P
  return = {!!}

  _>>=_ : {P Q : Set} → ¬ ¬ P -> (P -> ¬ ¬ Q) -> ¬ ¬ Q
  (¬¬p >>= f) = {!!}

  -- TIP: if an operation with name _>>=_ is in scope, Agda allows us to
  -- use do-notation (again possibly familiar from Haskell) to write
  --
  --    do
  --      x <- mx
  --      f
  --
  -- instead of mx >>= λ x → f. Here is an example (feel free to play
  -- around and make a hole in the last line to see what is going on):

  ¬¬-map : {P Q : Set} → (P -> Q) -> ¬ ¬ P -> ¬ ¬ Q
  ¬¬-map f ¬¬p = do
    p ← ¬¬p
    return (f p)

  {- ??? 1.12 Use do-notation and/or ¬¬-map to show that
         double negation distributes over 'exists' and 'or' (what about
         functions in the reverse directions?).
     (2 MARKS) -}


  ¬¬-distributes-∃ : {A : Set}{S : A → Set} →
                     Σ[ x ∈ A ] (¬ ¬ (S x)) -> ¬ ¬ (Σ A S)
  ¬¬-distributes-∃ = {!!}

  ¬¬-distributes-⊎ : {P Q : Set} → ¬ ¬ P ⊎ ¬ ¬ Q -> ¬ ¬ (P ⊎ Q)
  ¬¬-distributes-⊎ = {!!}

  {- ??? 1.13 The Fundamental Interconnectedness of All Things. Prove the
         following counter-intuitive fact of classical logic: for any two
         things, one must imply the other.

         HINT: You might want to look up the phrase "material
         implication", and maybe prove a lemma.

         For full marks, also pay attention to style, e.g., layout,
         no excessive brackets, choice of variable names, etc.
     (5 MARKS) -}

  dirkGently : (lem : (X : Set) -> X ⊎ ¬ X) -> {P Q : Set} → (P -> Q) ⊎ (Q -> P)
  dirkGently lem {P} {Q} = {!!}

-----------------------------------------------------------------------
-- maxVal SHADES OF GRAY (30 MARKS in total)
------------------------------------------------------------------------

open Data.Maybe

{- Our final task is to write a commandline program for manipulating
   and displaying grayscale images. This section is deliberately left
   more open-ended for you to practice designing and writing slightly
   larger programs. Most likely you will have to come up with your own
   plan, and implement some auxiliary functions to get there.  -}

{- ??? 1.23 Below, there are four marks available for good style,
       sensible reusable supporting functions, and good comments.
   (4 MARKS) -}

{- Let's get started!

   A (plain) Portable GrayMap (PGM) format
   [http://netpbm.sourceforge.net/doc/pgm.html] representation of a
   grayscale image consists of the following ASCII text:
   * The "magic number" P2;
   * whitespace (space, tabs, line breaks, etc);
   * A natural number w, formatted in decimal as ASCII;
   * whitespace;
   * A natural number h, formatted in decimal as ASCII;
   * whitespace;
   * A natural number maxVal, formatted in decimal as ASCII;
   * h number of rows separated by line breaks, each row consisting of
     w entries separated by whitespace, each entry being a natural
     number smaller than or equal to maxVal.

   Each entry in the raster represents a grayscale pixel value, ranging
   from 0 = black to maxVal = white (note that 0 is black, not white!).
   You can see some examples in the Coursework.Examples.One file, and in the
   Examples directory.
-}

open import Coursework.Examples.One

{- Notice how data earlier in the file determines the format of the
   following data; a dependent type!
-}

{- ??? 1.14 Your first task is to represent a PGM file as an Agda record,
       by completing the following definition with the required fields.
       Use vectors from Data.Vec to represent the rows and columns, and
       finite numbers from Data.Fin to represent the bounded entries.
   (1 MARK) -}

record PlainPGM : Set where
  constructor P2 -- just a suggested name
  field
    -- ADD YOUR FIELDS HERE

{- ??? 1.15 To make sure that you understand the file format, write a function
   that turns a PlainPGM back into a string.
   (2 MARKS) -}

writePGM : PlainPGM -> String
writePGM = {!!}

-- HINT: You might find the modules Data.Nat.Show and Data.Fin.Show useful,
--   as well as Data.String.

{- ??? 1.16 Continuing our quest for understanding, write a function
       which generates an "ASCII art" rendering of a PGM file; you
       will need to decide on some cutoff points for translating
       grayscale pixel intensity into symbols, e.g., you could choose
         100% = '#'
         75%  = '%'
         50%  = '^'
         25%  = '.'
       with even more distinctions if you want.

       Hint: Looking back at the spec, what does 0 represent?
  (3 MARKS) -}

viewPGM : PlainPGM -> String
viewPGM = {!!}

-- HINT: You can now look at a PGM image i by normalising viewPGM in
-- emacs; if you do C-u C-u C-c C-n, emacs will apply the following
-- trivial show function to the resulting string, which will print the
-- newlines correctly:

show : String -> String
show = id

{- ??? 1.17 We also want to be able to read images given to us. Since
       we have no guarantees that the string we are given actually
       represents a valid image, we will have to produce Maybe an
       image. However for debugging ease of use, also implement an "unsafe"
       version which should return an empty image if readPGM fails.
   (4 MARKS) -}

readPGM : String -> Maybe PlainPGM
readPGM = {!!}

unsafeReadPGM : String -> PlainPGM
unsafeReadPGM = {!!}

-- HINT: Again Data.Nat.Show and Data.String are your friends.

-- HINT: It is polite to be forgiving in what you accept, and not
-- insist on newlines over other whitespace to separate lines, for
-- example. And if you look in Data.String, it is sometimes easy to be
-- polite.

-- HINT: Since Maybe also is a monad, Agda allows you to use do
-- notation here, which could be helpful.

{- !!! Congratulations, you have now implemented enough to have a
   working running program!  If you look at the bottom of this file,
   you will see a main function I have prepared for you. You should be
   able to compile this file by selecting "Compile" in the Agda menu
   and then the "GHC" backend, and then run the produced binary on the
   commandline, with the "-ascii" action working. Try it out on one of
   the sample files in the One directory, or your favourite PGM file
   from the Internet! You can use `convert -compress none` to convert
   almost any image into plain PGM format if you have imagemagick
   installed. -}

{- ??? 1.18 Implement "posterization", which literally treats the
       world as black-and-white: if the pixel is <= 50%, make it 0%,
       otherwise make it 100%. Note that we do not need to produce
       Maybe an image here, because we know that the input we get is
       correct.

       After implementing this, the "-posterize" action should work if
       you recompile the program.
   (2 MARKS) -}

posterize : PlainPGM → PlainPGM
posterize = id -- CHANGE THIS!

-- TO PONDER: What happens if you posterize an already posterized image?
-- Can you prove it?


{- ??? 1.19 Implement rotation, which turns an image sideways (you can
       decide if clockwise or anticlockwise).
   (4 MARKS) -}

rotate : PlainPGM → PlainPGM
rotate = id -- CHANGE THIS!

-- HINT: It might be useful to be able to repeat an element to fill up
-- a vector of a given length, and to be able to "apply" a vector full
-- of functions to a vector full of arguments.

{- !!! You should now be able to use the "-rotate" action in your program -}

{- ??? 1.20 Implement shrinking, which halves the size of an image by
       replacing each pixel with the average of its neighbours (you
       don't have to consider the neighbours in all nine directions,
       unless you want to; it is enough to consider for example the
       previous neighbor in both directions).
   (4 MARKS) -}

shrink : PlainPGM → PlainPGM
shrink = id -- CHANGE THIS!

-- HINT: it might be useful to give yourself "random access" to
-- the raster. The function `lookup : ∀ {n} → Vec A n → (Fin n → A)`
-- from Data.Vec makes it possible to see a vector as a function from
-- `Fin n` -- can you go the other way, i.e., implement
-- `tabulate : {n : ℕ} → (Fin n -> A) -> Vec A n`?
-- Another hint: Data.Nat.Properties contain many useful facts.

{- !!! You should now be able to use the "-shrink" action in your program.
   Well done, you have now implemented the basic functionality of the program.
   We now move on to some nice extras. -}

{- ??? 1.21 Allowing comments. The PGM file format actually allows
       comments, in the sense that any content following a hash symbol
       '#' is ignored until the end of the line. Implement this as a
       preprocessing step, so that you can use images downloaded from
       the Internet.
   (1 MARK) -}

stripComments : String → String
stripComments = id -- CHANGE THIS!

{- ??? 1.22 Time for you to shine! Implement a further interesting
       operation on PGM images by changing "-youraction" in the main
       program below. You could e.g. implement inverting, tiling,
       or merging different images, or...
   (5 MARKS) -}

{- Your program here! -}


{- Here follows some stuff for doing IO via Haskell functions; you can
safely ignore until the main function below -}

open import IO using (IO)
import IO.Primitive
open import IO.Finite
open import Foreign.Haskell.Pair

{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.FilePath    #-}
{-# FOREIGN GHC import qualified Data.Text          #-}
{-# FOREIGN GHC import qualified Control.Arrow      #-}

postulate
  primGetArgs : IO.Primitive.IO (List String)
  splitExtension : String → Pair String String

{-# COMPILE GHC primGetArgs = fmap Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC splitExtension = (Data.Text.pack Control.Arrow.*** Data.Text.pack) . System.FilePath.splitExtension . Data.Text.unpack #-}

getArgs : IO (List String)
getArgs = IO.lift primGetArgs

addExtension : Pair String String → String
addExtension (f , ext) = f S++ ext

writeFile' : String → String → IO {Level.zero} ⊤
writeFile' file content = do
  IO.putStrLn ("Writing output to " S++ file) IO.>>= \ _ → writeFile file content

{- Something interesting happening here again! -}

main : IO.Main
main = IO.run $
  getArgs IO.>>= λ where
    (action ∷ file ∷ []) →
      readFile file IO.>>= λ contents →
        case readPGM (stripComments contents)
          of λ { nothing    → IO.putStrLn "Error: malformed input file"
               ; (just pgm) → act action (splitExtension file) pgm }
    _ → IO.putStrLn $ "Usage: One ACTION INPUTFILE" S++ available
  where
    available : String
    available = "\n\nAvailable actions: -ascii -posterize -reflect -rotate"
    act : (action : String) -> (file : Pair String String) -> PlainPGM -> IO ⊤
    act "-ascii" out pgm = IO.putStrLn $ viewPGM pgm
    act "-posterize" (out , ext) pgm =
      writeFile' (addExtension (out S++ "-posterized", ext))
                 (writePGM (posterize pgm))
    act "-shrink" (out , ext) pgm =
      writeFile' (addExtension (out S++ "-shrunk", ext))
                 (writePGM (shrink pgm))
    act "-rotate" (out , ext) pgm =
      writeFile' (addExtension (out S++ "-rotated", ext))
                 (writePGM (rotate pgm))
    act "-youridea" (out , ext) pgm = IO.putStrLn $ "YOUR IDEA HERE?"
    act action out pgm =
      IO.putStrLn $ "Error: unknown action " S++ action S++ available

-- NOTE: You might find that your program is quite inefficient on
-- larger images -- this is okay, for now, although it could be
-- interesting to think about why that is. In general, there is much
-- work to be done to enable efficient compilation of dependently
-- typed programs.


{-
To compile:

  Either do C-c C-x C-c in Emacs (or select "Compile" from the Agda
  menu), and choose the GHC backend, or run

    agda -c One.agda

  on the command line. If you have unfinished holes from further up
  the file, it is easiest to comment them out before compiling.

  To run the resulting program,

    ./One ACTION INPUTFILE
-}
