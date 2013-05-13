{-# LANGUAGE PatternGuards #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  XMonad.StackSet
-- Copyright   :  (c) Don Stewart 2007
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  dons@galois.com
-- Stability   :  experimental
-- Portability :  portable, Haskell 98
--

module XMonad.StackSet where

import Prelude hiding (filter, reverse, (++), elem) -- LIQUID
import Data.Maybe   (listToMaybe,isJust,fromMaybe)
import qualified Data.List as L (deleteBy,find,splitAt,filter,nub)
import Data.List ( (\\) )
import qualified Data.Map  as M (Map,insert,delete,empty)
import qualified Data.Set -- LIQUID

-------------------------------------------------------------------------------
----------------------------- Refinements on  Lists ---------------------------
-------------------------------------------------------------------------------

-- measures

{-@
  measure listDup :: [a] -> (Data.Set.Set a)
  listDup([]) = {v | (? Set_emp (v))}
  listDup(x:xs) = {v | v = ((Set_mem x (listElts xs))?(Set_cup (Set_sng x) (listDup xs)):(listDup xs)) }
  @-}

-- predicates 

{-@ predicate EqElts X Y =
       ((listElts X) = (listElts Y)) @-}

{-@ predicate SubElts X Y =
       (Set_sub (listElts X) (listElts Y)) @-}

{-@ predicate UnionElts X Y Z =
       ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}

{-@ predicate ListElt N LS =
       (Set_mem N (listElts LS)) @-}

{-@ predicate ListUnique LS =
       (Set_emp (listDup LS)) @-}

{-@ predicate ListUniqueDif LS X =
       ((ListUnique LS) && (not (ListElt X LS))) @-}


{-@ predicate ListDisjoint X Y =
       (Set_emp (Set_cap (listElts X) (listElts Y))) @-}


-- types

{-@ type UList a = {v:[a] | (ListUnique v)} @-}

{-@ type UListDif a N = {v:[a] | ((not (ListElt N v)) && (ListUnique v))} @-}



-------------------------------------------------------------------------------
----------------------------- Refinements on Stacks ---------------------------
-------------------------------------------------------------------------------

{-@
data Stack a = Stack { focus :: a   
                     , up    :: UListDif a focus
                     , down  :: UListDif a focus }
@-}

{-@ type UStack a = {v:(Stack a) | (ListDisjoint (getUp v) (getDown v))}@-}

{-@ measure getUp :: forall a. (Stack a) -> [a] 
    getUp (Stack focus up down) = up
  @-}

{-@ measure getDown :: forall a. (Stack a) -> [a] 
    getDown (Stack focus up down) = down
  @-}

{-@ measure getFocus :: forall a. (Stack a) -> a
    getFocus (Stack focus up down) = focus
  @-}

{-@ predicate StackElt N X =
       (Set_mem N (stackElts X)) @-}
        

{-@ predicate StackSetElt N S = (StackSetCurrentElt N S)
  @-}
data StackSet i l a sid sd =
    StackSet { current  :: !(Screen i l a sid sd)    -- ^ currently focused workspace
             , visible  :: [Screen i l a sid sd]     -- ^ non-focused workspaces, visible in xinerama
             , hidden   :: [Workspace i l a]         -- ^ workspaces not visible anywhere
             , floating :: M.Map a RationalRect      -- ^ floating windows
             } deriving (Show, Eq)
-- LIQUID             } deriving (Show, Read, Eq)

{-@ 
data StackSet i l a sid sd =
    StackSet { current  :: (Screen i l a sid sd)   
             , visible  :: [Screen i l a sid sd]   
             , hidden   :: [Workspace i l a]       
             , floating :: M.Map a RationalRect    
             }
@-}

{-@ measure getCurrentScreen :: (StackSet i l a sid sd) -> (Screen i l a sid sd)
    getCurrentScreen(StackSet current v h f) = current @-}


{-@ predicate StackSetCurrentElt N S = 
      (ScreenElt N (getCurrentScreen S))
  @-}


-- | Visible workspaces, and their Xinerama screens.
data Screen i l a sid sd = Screen { workspace :: !(Workspace i l a)
                                  , screen :: !sid
                                  , screenDetail :: !sd }
    deriving (Show, Eq)
-- LIQUID    deriving (Show, Read, Eq)

{-@ 
data Screen i l a sid sd = Screen { workspace :: (Workspace i l a)
                                  , screen :: sid
                                  , screenDetail :: sd }
@-}

{-@ measure getWorkspaceScreen :: (Screen i l a sid sd) -> (Workspace i l a)
    getWorkspaceScreen(Screen w screen s) = w @-}


{-@ predicate ScreenElt N S = 
      (WorkspaceElt N (getWorkspaceScreen S))
  @-}


-- |
-- A workspace is just a tag, a layout, and a stack.
--
data Workspace i l a = Workspace  { tag :: !i, layout :: l, stack :: Maybe (Stack a) }
    deriving (Show, Eq)
--     deriving (Show, Read, Eq)

{-@
data Workspace i l a = Workspace  { tag :: i, layout :: l, stack :: Maybe (UStack a) }
  @-}

{-@ measure getStackWorkspace :: (Workspace i l a) -> (Maybe(Stack a))
    getStackWorkspace(Workspace t l stack) = stack @-}

-- | A structure for window geometries
data RationalRect = RationalRect Rational Rational Rational Rational
    deriving (Show, Read, Eq)

data Stack a = Stack { focus  :: !a        -- focused thing in this set
                     , up     :: [a]       -- clowns to the left
                     , down   :: [a] }     -- jokers to the right
     deriving (Show, Eq)
-- LIQUID      deriving (Show, Read, Eq)


-- | this function indicates to catch that an error is expected
abort :: String -> a
abort x = error $ "xmonad: StackSet: " ++ x
  where [] ++ ys     = ys              -- LIQUID
        (x:xs) ++ ys = x: (xs ++ ys)   -- LIQUID


-- ---------------------------------------------------------------------
--LIQUID -- $construction
--LIQUID 
--LIQUID -- | /O(n)/. Create a new stackset, of empty stacks, with given tags,
--LIQUID -- with physical screens whose descriptions are given by 'm'. The
--LIQUID -- number of physical screens (@length 'm'@) should be less than or
--LIQUID -- equal to the number of workspace tags.  The first workspace in the
--LIQUID -- list will be current.
--LIQUID --
--LIQUID -- Xinerama: Virtual workspaces are assigned to physical screens, starting at 0.
--LIQUID --
--LIQUID new :: (Integral s) => l -> [i] -> [sd] -> StackSet i l a s sd
--LIQUID new l wids m | not (null wids) && length m <= length wids && not (null m)
--LIQUID   = StackSet cur visi unseen M.empty
--LIQUID   where (seen,unseen) = L.splitAt (length m) $ map (\i -> Workspace i l Nothing) wids
--LIQUID         (cur:visi)    = [ Screen i s sd |  (i, s, sd) <- zip3 seen [0..] m ]
--LIQUID                 -- now zip up visibles with their screen id
--LIQUID new _ _ _ = abort "non-positive argument to StackSet.new"
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(w)/. Set focus to the workspace with index \'i\'.
--LIQUID -- If the index is out of range, return the original 'StackSet'.
--LIQUID --
--LIQUID -- Xinerama: If the workspace is not visible on any Xinerama screen, it
--LIQUID -- becomes the current screen. If it is in the visible list, it becomes
--LIQUID -- current.
--LIQUID 
--LIQUID view :: (Eq s, Eq i) => i -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID view i s
--LIQUID     | i == currentTag s = s  -- current
--LIQUID 
--LIQUID     | Just x <- L.find ((i==).tag.workspace) (visible s)
--LIQUID     -- if it is visible, it is just raised
--LIQUID     = s { current = x, visible = current s : L.deleteBy (equating screen) x (visible s) }
--LIQUID 
--LIQUID     | Just x <- L.find ((i==).tag)           (hidden  s) -- must be hidden then
--LIQUID     -- if it was hidden, it is raised on the xine screen currently used
--LIQUID     = s { current = (current s) { workspace = x }
--LIQUID         , hidden = workspace (current s) : L.deleteBy (equating tag) x (hidden s) }
--LIQUID 
--LIQUID     | otherwise = s -- not a member of the stackset
--LIQUID 
--LIQUID   where equating f = \x y -> f x == f y
--LIQUID 
--LIQUID     -- 'Catch'ing this might be hard. Relies on monotonically increasing
--LIQUID     -- workspace tags defined in 'new'
--LIQUID     --
--LIQUID     -- and now tags are not monotonic, what happens here?
--LIQUID 
--LIQUID -- |
--LIQUID -- Set focus to the given workspace.  If that workspace does not exist
--LIQUID -- in the stackset, the original workspace is returned.  If that workspace is
--LIQUID -- 'hidden', then display that workspace on the current screen, and move the
--LIQUID -- current workspace to 'hidden'.  If that workspace is 'visible' on another
--LIQUID -- screen, the workspaces of the current screen and the other screen are
--LIQUID -- swapped.
--LIQUID 
--LIQUID greedyView :: (Eq s, Eq i) => i -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID greedyView w ws
--LIQUID      | any wTag (hidden ws) = view w ws
--LIQUID      | (Just s) <- L.find (wTag . workspace) (visible ws)
--LIQUID                             = ws { current = (current ws) { workspace = workspace s }
--LIQUID                                  , visible = s { workspace = workspace (current ws) }
--LIQUID                                            : L.filter (not . wTag . workspace) (visible ws) }
--LIQUID      | otherwise = ws
--LIQUID    where wTag = (w == ) . tag
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- $xinerama
--LIQUID 
--LIQUID -- | Find the tag of the workspace visible on Xinerama screen 'sc'.
--LIQUID -- 'Nothing' if screen is out of bounds.
--LIQUID lookupWorkspace :: Eq s => s -> StackSet i l a s sd -> Maybe i
--LIQUID lookupWorkspace sc w = listToMaybe [ tag i | Screen i s _ <- current w : visible w, s == sc ]
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- $stackOperations
--LIQUID 
--LIQUID -- |
--LIQUID -- The 'with' function takes a default value, a function, and a
--LIQUID -- StackSet. If the current stack is Nothing, 'with' returns the
--LIQUID -- default value. Otherwise, it applies the function to the stack,
--LIQUID -- returning the result. It is like 'maybe' for the focused workspace.
--LIQUID --
--LIQUID with :: b -> (Stack a -> b) -> StackSet i l a s sd -> b
--LIQUID with dflt f = maybe dflt f . stack . workspace . current
--LIQUID 
--LIQUID -- |
--LIQUID -- Apply a function, and a default value for 'Nothing', to modify the current stack.
--LIQUID --
--LIQUID {- modify :: Maybe (UStack a) -> (UStack a -> Maybe (UStack a)) -> StackSet i l a s sd -> StackSet i l a s sd @-}
--LIQUID modify :: Maybe (Stack a) -> (Stack a -> Maybe (Stack a)) -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID modify d f s = s { current = (current s)
--LIQUID                         { workspace = (workspace (current s)) { stack = with d f s }}}
--LIQUID 
--LIQUID -- |
--LIQUID -- Apply a function to modify the current stack if it isn't empty, and we don't
--LIQUID --  want to empty it.
--LIQUID --
--LIQUID {- modify' :: (UStack a -> UStack a) -> StackSet i l a s sd -> StackSet i l a s sd @-}
--LIQUID modify' :: (Stack a -> Stack a) -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID modify' f = modify Nothing (Just . f)
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(1)/. Extract the focused element of the current stack.
--LIQUID -- Return 'Just' that element, or 'Nothing' for an empty stack.
--LIQUID --
--LIQUID peek :: StackSet i l a s sd -> Maybe a
--LIQUID peek = with Nothing (return . focus)
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(n)/. Flatten a 'Stack' into a list.
--LIQUID --
--LIQUID -- |
--LIQUID -- /O(n)/ Flatten a possibly empty stack into a list.
--LIQUID {- integrate' :: Maybe (UStack a) -> UList a @-}
--LIQUID integrate' :: Maybe (Stack a) -> [a]
--LIQUID integrate' = maybe [] integrate
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(n)/. Turn a list into a possibly empty stack (i.e., a zipper):
--LIQUID -- the first element of the list is current, and the rest of the list
--LIQUID -- is down.
--LIQUID {- differentiate :: UList a -> Maybe (UStack a) @-}
--LIQUID differentiate :: [a] -> Maybe (Stack a)
--LIQUID differentiate []     = Nothing
--LIQUID differentiate (x:xs) = Just $ Stack x [] xs
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(n)/. 'filter p s' returns the elements of 's' such that 'p' evaluates to
--LIQUID -- 'True'.  Order is preserved, and focus moves as described for 'delete'.
--LIQUID --
--LIQUID {- filter :: (a -> Bool) -> UStack a -> Maybe (UStack a) @-}
--LIQUID filter :: (a -> Bool) -> Stack a -> Maybe (Stack a)
--LIQUID filter p (Stack f ls rs) = case filterL p (f:rs) of
--LIQUID     f':rs' -> Just $ Stack f' (filterL p ls) rs'    -- maybe move focus down
--LIQUID     []     -> case filterL p ls of                  -- filter back up
--LIQUID                     f':ls' -> Just $ Stack f' ls' [] -- else up
--LIQUID                     []     -> Nothing
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(s)/. Extract the stack on the current workspace, as a list.
--LIQUID -- The order of the stack is determined by the master window -- it will be
--LIQUID -- the head of the list. The implementation is given by the natural
--LIQUID -- integration of a one-hole list cursor, back to a list.
--LIQUID --
--LIQUID index :: StackSet i l a s sd -> [a]
--LIQUID index = with [] integrate
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(1), O(w) on the wrapping case/.
--LIQUID --
--LIQUID -- focusUp, focusDown. Move the window focus up or down the stack,
--LIQUID -- wrapping if we reach the end. The wrapping should model a 'cycle'
--LIQUID -- on the current stack. The 'master' window, and window order,
--LIQUID -- are unaffected by movement of focus.
--LIQUID --
--LIQUID -- swapUp, swapDown, swap the neighbour in the stack ordering, wrapping
--LIQUID -- if we reach the end. Again the wrapping model should 'cycle' on
--LIQUID -- the current stack.
--LIQUID --
--LIQUID focusUp, focusDown, swapUp, swapDown :: StackSet i l a s sd -> StackSet i l a s sd
--LIQUID focusUp   = modify' focusUp'
--LIQUID focusDown = modify' focusDown'
--LIQUID 
--LIQUID swapUp    = modify' swapUp'
--LIQUID swapDown  = modify' (reverseStack . swapUp' . reverseStack)
--LIQUID 
--LIQUID -- | Variants of 'focusUp' and 'focusDown' that work on a
--LIQUID -- 'Stack' rather than an entire 'StackSet'.
--LIQUID {- focusUp', focusDown' :: UStack a -> UStack a @-}
--LIQUID focusUp', focusDown' :: Stack a -> Stack a
--LIQUID focusUp' (Stack t (l:ls) rs) = Stack l ls (t:rs)
--LIQUID focusUp' (Stack t []     rs) = Stack x xs [] where (x:xs) = reverse (t:rs)
--LIQUID focusDown'                   = reverseStack . focusUp' . reverseStack
--LIQUID 
--LIQUID {- swapUp' :: UStack a -> UStack a @-}
--LIQUID swapUp' :: Stack a -> Stack a
--LIQUID swapUp'  (Stack t (l:ls) rs) = Stack t ls (l:rs)
--LIQUID swapUp'  (Stack t []     rs) = Stack t (reverse rs) []
--LIQUID 
--LIQUID -- | reverse a stack: up becomes down and down becomes up.
--LIQUID {- reverseStack :: UStack a -> UStack a @-}
--LIQUID reverseStack :: Stack a -> Stack a
--LIQUID reverseStack (Stack t ls rs) = Stack t rs ls
--LIQUID 
--LIQUID --
--LIQUID -- | /O(1) on current window, O(n) in general/. Focus the window 'w',
--LIQUID -- and set its workspace as current.
--LIQUID --
--LIQUID focusWindow :: (Eq s, Eq a, Eq i) => a -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID focusWindow w s | Just w == peek s = s
--LIQUID                 | otherwise        = fromMaybe s $ do
--LIQUID                     n <- findTag w s
--LIQUID                     return $ until ((Just w ==) . peek) focusUp (view n s)
--LIQUID 
--LIQUID -- | Get a list of all screens in the 'StackSet'.
--LIQUID screens :: StackSet i l a s sd -> [Screen i l a s sd]
--LIQUID screens s = current s : visible s
--LIQUID 
--LIQUID -- | Get a list of all workspaces in the 'StackSet'.
--LIQUID 
--LIQUID -- | Get a list of all windows in the 'StackSet' in no particular order
--LIQUID allWindows :: Eq a => StackSet i l a s sd -> [a]
--LIQUID allWindows = L.nub . concatMap (integrate' . stack) . workspaces
--LIQUID 
--LIQUID -- | Get the tag of the currently focused workspace.
--LIQUID currentTag :: StackSet i l a s sd -> i
--LIQUID currentTag = tag . workspace . current
--LIQUID 
--LIQUID -- | Is the given tag present in the 'StackSet'?
--LIQUID tagMember :: Eq i => i -> StackSet i l a s sd -> Bool
--LIQUID tagMember t = elem t . map tag . workspaces
--LIQUID 
--LIQUID -- | Rename a given tag if present in the 'StackSet'.
--LIQUID renameTag :: Eq i => i -> i -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID renameTag o n = mapWorkspace rename
--LIQUID     where rename w = if tag w == o then w { tag = n } else w
--LIQUID 
--LIQUID -- | Ensure that a given set of workspace tags is present by renaming
--LIQUID -- existing workspaces and\/or creating new hidden workspaces as
--LIQUID -- necessary.
--LIQUID ensureTags :: Eq i => l -> [i] -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID ensureTags l allt st = et allt (map tag (workspaces st) \\ allt) st
--LIQUID     where et [] _ s = s
--LIQUID           et (i:is) rn s | i `tagMember` s = et is rn s
--LIQUID           et (i:is) [] s = et is [] (s { hidden = Workspace i l Nothing : hidden s })
--LIQUID           et (i:is) (r:rs) s = et is rs $ renameTag r i s
--LIQUID 
--LIQUID -- | Map a function on all the workspaces in the 'StackSet'.
--LIQUID mapWorkspace :: (Workspace i l a -> Workspace i l a) -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID mapWorkspace f s = s { current = updScr (current s)
--LIQUID                      , visible = map updScr (visible s)
--LIQUID                      , hidden  = map f (hidden s) }
--LIQUID     where updScr scr = scr { workspace = f (workspace scr) }
--LIQUID 
--LIQUID -- | Map a function on all the layouts in the 'StackSet'.
--LIQUID mapLayout :: (l -> l') -> StackSet i l a s sd -> StackSet i l' a s sd
--LIQUID mapLayout f (StackSet v vs hs m) = StackSet (fScreen v) (map fScreen vs) (map fWorkspace hs) m
--LIQUID  where
--LIQUID     fScreen (Screen ws s sd) = Screen (fWorkspace ws) s sd
--LIQUID     fWorkspace (Workspace t l s) = Workspace t (f l) s
--LIQUID 
--LIQUID -- | /O(n)/. Is a window in the 'StackSet'?
--LIQUID {- member :: Eq a 
--LIQUID            => x:a 
--LIQUID            -> st:(StackSet i l a s sd) 
--LIQUID            -> {v:Bool| ((Prop v)<=> (StackSetElt x st))}
--LIQUID   @-}
--LIQUID member :: Eq a => a -> StackSet i l a s sd -> Bool
--LIQUID member a s = undefined -- LIQUID isJust (findTag a s)
--LIQUID 
--LIQUID -- | /O(1) on current window, O(n) in general/.
--LIQUID -- Return 'Just' the workspace tag of the given window, or 'Nothing'
--LIQUID -- if the window is not in the 'StackSet'.
--LIQUID findTag :: Eq a => a -> StackSet i l a s sd -> Maybe i
--LIQUID findTag a s = listToMaybe
--LIQUID     [ tag w | w <- workspaces s, has a (stack w) ]
--LIQUID     where has _ Nothing         = False
--LIQUID           has x (Just (Stack t l r)) = x `elem` (t : l ++ r)
--LIQUID

{-@ findTag' :: Eq a 
             => x:a 
             -> w:(Workspace i l a)
             -> {v:Bool|((Prop v) <=> (WorkspaceElt x w)) }
  @-}
findTag' :: Eq a => a -> Workspace i l a -> Bool
findTag' x w = has x (stack w)


{- findTag'' :: Eq a 
              => x:a 
              -> st:(StackSet i l a s sd)
              -> [Workspace i l a]
  @-}
--               -> [{vv:Workspace i l a| (WorkspaceElt x vv)}]

findTag'' :: Eq a => a -> StackSet i l a s sd -> [Workspace i l a]
findTag'' a s = go wps []
   where wps = workspaces s
         go [] ack     = ack
         go (x:xs) ack | findTag' a x = go xs (x:ack)
                       | otherwise    = go xs ack









{-@ measure getWorkspaces :: (StackSet i l a sid sd) -> (Data.Set.Set (Workspace i l a))
    getWorkspaces(StackSet c v h f) = {v | v = (Set_cup (listElts v) (Set_cup (listElts h) (getScreenWorkspaces c)))}
  @-}

{-@ measure getScreenWorkspaces :: (Screen i l a sid sd) -> (Data.Set.Set (Workspace i l a))
    getScreenWorkspaces(Screen w s sd) = {v | v = (Set_sng w)}
  @-}


{-@ workspaces :: st:(StackSet i l a s sd) 
               -> {v:[Workspace i l a] | (listElts v) = (getWorkspaces st)} @-}
workspaces :: StackSet i l a s sd -> [Workspace i l a]
workspaces s = undefined
-- workspaces s = workspace (current s) : map workspace (visible s) ++ hidden s
  where [] ++ ys     = ys              -- LIQUID
        (x:xs) ++ ys = x: (xs ++ ys)   -- LIQUID


-- if the window is not in the 'StackSet'.
-- findTag :: Eq a => a -> StackSet i l a s sd -> Maybe i
-- findTag a s = listToMaybe
--     [ tag w | w <- workspaces s, has a (stack w) ]

{-@ predicate WorkspaceElt N W =
  ((isJust (getStackWorkspace W)) && (StackElt N (fromJust (getStackWorkspace W)))) @-}




{-@ stack :: w:(Workspace i l a) 
          -> {v:(Maybe (UStack a)) | v = (getStackWorkspace w)}@-}

{-@ has :: Eq a 
        => x:a 
        -> st:(Maybe (UStack a))
        -> {v:Bool| ((Prop v) <=> ((isJust st) && (StackElt x (fromJust st)))) }
  @-}
has :: Eq a => a -> Maybe (Stack a) -> Bool
has _ Nothing              = False
has x (Just (Stack t l r)) = x `elem` (t : l ++ r)

{-@ elem :: Eq a 
         => x:a 
         -> xs:[a] 
         -> {v:Bool | ((Prop v) <=> (ListElt x xs))}
  @-}
elem :: Eq a => a -> [a] -> Bool
elem x []     = False
elem x (y:ys) | x == y    = True
              | otherwise = elem x ys 

{-@ measure stackElts :: Stack a -> (Data.Set.Set a)
    stackElts(Stack f up down) = {v | v = (Set_cup (Set_sng f) (Set_cup (listElts up) (listElts down)))}
  @-}


{-@ foo :: x:a -> xs:[a] -> ys:[a] -> {v:[a]  |(listElts v) = (Set_cup (Set_sng x) (Set_cup (listElts xs) (listElts ys))) }
  @-}
foo :: a -> [a] -> [a] -> [a] 
foo = undefined

{- bar :: x:a -> xs:[a] -> ys:[a] -> {v:[a]  |(listElts v) = (Set_cup (Set_sng x) (listElts ys)) }
  @-}
bar :: a -> [a] -> [a] -> [a] 
bar = undefined

infixr 5 ++
{-@ (++) :: xs:(UList a)
         -> ys:{v: UList a | (ListDisjoint v xs)}
         -> {v: UList a | (UnionElts v xs ys)}
  @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x: (xs ++ ys)

 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- $modifyStackset
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(n)/. (Complexity due to duplicate check). Insert a new element
--LIQUID -- into the stack, above the currently focused element. The new
--LIQUID -- element is given focus; the previously focused element is moved
--LIQUID -- down.
--LIQUID --
--LIQUID -- If the element is already in the stackset, the original stackset is
--LIQUID -- returned unmodified.
--LIQUID --
--LIQUID -- Semantics in Huet's paper is that insert doesn't move the cursor.
--LIQUID -- However, we choose to insert above, and move the focus.
--LIQUID --
--LIQUID {- insertUp :: Eq a => a -> StackSet i l a s sd -> StackSet i l a s sd @-}
--LIQUID insertUp :: Eq a => a -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID insertUp a s = if member a s then s else insertUp_ a (Just $ Stack a [] []) s
--LIQUID -- LIQUID insertUp a s = if member a s then s else insert
--LIQUID -- LIQUID   where insert = modify (Just $ Stack a [] []) (Just $ Stack a [] []) (\(Stack t l r) -> Just $ Stack a l (t:r)) s
--LIQUID 
--LIQUID -- LIQUID TODO look this again!
--LIQUID {- insertUp_ :: x:a 
--LIQUID               -> (Maybe (UStack a))  
--LIQUID               -> {v:StackSet i l a s sd | not (StackSetElt x v)}
--LIQUID               -> (StackSet i l a s sd)@-}
--LIQUID insertUp_ :: a 
--LIQUID           -> Maybe (Stack a) 
--LIQUID           -> StackSet i l a s sd 
--LIQUID           -> StackSet i l a s sd
--LIQUID insertUp_ x _ (StackSet (Screen (Workspace i l (Just (Stack t ls rs))) a b ) v h c)
--LIQUID  = (StackSet (Screen (Workspace i l (Just (Stack x ls (t:rs)))) a b) v h c)
--LIQUID insertUp_ _ d (StackSet (Screen (Workspace i l Nothing) a b ) v h c)
--LIQUID  = (StackSet (Screen (Workspace i l d) a b ) v h c)
--LIQUID 
--LIQUID -- insertDown :: a -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID -- insertDown a = modify (Stack a [] []) $ \(Stack t l r) -> Stack a (t:l) r
--LIQUID -- Old semantics, from Huet.
--LIQUID -- >    w { down = a : down w }
--LIQUID 
--LIQUID -- |
--LIQUID -- /O(1) on current window, O(n) in general/. Delete window 'w' if it exists.
--LIQUID -- There are 4 cases to consider:
--LIQUID --
--LIQUID --   * delete on an 'Nothing' workspace leaves it Nothing
--LIQUID --
--LIQUID --   * otherwise, try to move focus to the down
--LIQUID --
--LIQUID --   * otherwise, try to move focus to the up
--LIQUID --
--LIQUID --   * otherwise, you've got an empty workspace, becomes 'Nothing'
--LIQUID --
--LIQUID -- Behaviour with respect to the master:
--LIQUID --
--LIQUID --   * deleting the master window resets it to the newly focused window
--LIQUID --
--LIQUID --   * otherwise, delete doesn't affect the master.
--LIQUID --
--LIQUID delete :: (Ord a, Eq s) => a -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID delete w = sink w . delete' w
--LIQUID 
--LIQUID -- | Only temporarily remove the window from the stack, thereby not destroying special
--LIQUID -- information saved in the 'Stackset'
--LIQUID delete' :: (Eq a, Eq s) => a -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID delete' w s = s { current = removeFromScreen        (current s)
--LIQUID                 , visible = map removeFromScreen    (visible s)
--LIQUID                 , hidden  = map removeFromWorkspace (hidden  s) }
--LIQUID     where removeFromWorkspace ws = ws { stack = stack ws >>= filter (/=w) }
--LIQUID           removeFromScreen scr   = scr { workspace = removeFromWorkspace (workspace scr) }
--LIQUID 
--LIQUID ------------------------------------------------------------------------
--LIQUID 
--LIQUID -- | Given a window, and its preferred rectangle, set it as floating
--LIQUID -- A floating window should already be managed by the 'StackSet'.
--LIQUID float :: Ord a => a -> RationalRect -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID float w r s = s { floating = M.insert w r (floating s) }
--LIQUID 
--LIQUID -- | Clear the floating status of a window
--LIQUID sink :: Ord a => a -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID sink w s = s { floating = M.delete w (floating s) }
--LIQUID 
--LIQUID ------------------------------------------------------------------------
--LIQUID -- $settingMW
--LIQUID 
--LIQUID -- | /O(s)/. Set the master window to the focused window.
--LIQUID -- The old master window is swapped in the tiling order with the focused window.
--LIQUID -- Focus stays with the item moved.
--LIQUID swapMaster :: StackSet i l a s sd -> StackSet i l a s sd
--LIQUID swapMaster = modify' swapMaster_ -- LIQUID $ \ccc -> case ccc of
--LIQUID -- LIQUID     Stack _ [] _  -> ccc    -- already master.
--LIQUID -- LIQUID     Stack t ls rs -> Stack t [] (xs ++ x : rs) where (x:xs) = reverse ls
--LIQUID 
--LIQUID -- LIQUID TODO this should be set to original code if we use invariants
--LIQUID {- swapMaster_ :: UStack a -> UStack a @-}
--LIQUID swapMaster_ :: Stack a -> Stack a
--LIQUID swapMaster_ =  \ccc -> case ccc of
--LIQUID     Stack _ [] _  -> ccc    -- already master.
--LIQUID     Stack t ls rs -> Stack t [] (xs ++ x : rs) where (x:xs) = reverse ls
--LIQUID 
--LIQUID 
--LIQUID -- natural! keep focus, move current to the top, move top to current.
--LIQUID 
--LIQUID -- | /O(s)/. Set the master window to the focused window.
--LIQUID -- The other windows are kept in order and shifted down on the stack, as if you
--LIQUID -- just hit mod-shift-k a bunch of times.
--LIQUID -- Focus stays with the item moved.
--LIQUID shiftMaster :: StackSet i l a s sd -> StackSet i l a s sd
--LIQUID shiftMaster = modify' $ \c -> case c of
--LIQUID     Stack _ [] _ -> c     -- already master.
--LIQUID     Stack t ls rs -> Stack t [] (reverse ls ++ rs)
--LIQUID 
--LIQUID -- | /O(s)/. Set focus to the master window.
--LIQUID focusMaster :: StackSet i l a s sd -> StackSet i l a s sd
--LIQUID focusMaster = modify' focusMaster_ -- LIQUID $ \c -> case c of
--LIQUID -- LIQUID     Stack _ [] _  -> c
--LIQUID -- LIQUID     Stack t ls rs -> Stack x [] (xs ++ t : rs) where (x:xs) = reverse ls
--LIQUID 
--LIQUID {- focusMaster_ :: UStack a -> UStack a @-}
--LIQUID focusMaster_ :: Stack a -> Stack a
--LIQUID focusMaster_ = \c -> case c of
--LIQUID     Stack _ [] _  -> c
--LIQUID     Stack t ls rs -> Stack x [] (xs ++ t : rs) where (x:xs) = reverse ls
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- $composite
--LIQUID 
--LIQUID -- | /O(w)/. shift. Move the focused element of the current stack to stack
--LIQUID -- 'n', leaving it as the focused element on that stack. The item is
--LIQUID -- inserted above the currently focused element on that workspace.
--LIQUID -- The actual focused workspace doesn't change. If there is no
--LIQUID -- element on the current stack, the original stackSet is returned.
--LIQUID --
--LIQUID shift :: (Ord a, Eq s, Eq i) => i -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID shift n s = maybe s (\w -> shiftWin n w s) (peek s)
--LIQUID 
--LIQUID -- | /O(n)/. shiftWin. Searches for the specified window 'w' on all workspaces
--LIQUID -- of the stackSet and moves it to stack 'n', leaving it as the focused
--LIQUID -- element on that stack. The item is inserted above the currently
--LIQUID -- focused element on that workspace.
--LIQUID -- The actual focused workspace doesn't change. If the window is not
--LIQUID -- found in the stackSet, the original stackSet is returned.
--LIQUID shiftWin :: (Ord a, Eq a, Eq s, Eq i) => i -> a -> StackSet i l a s sd -> StackSet i l a s sd
--LIQUID shiftWin n w s = case findTag w s of
--LIQUID                     Just from | n `tagMember` s && n /= from -> go from s
--LIQUID                     _                                        -> s
--LIQUID  where go from = onWorkspace n (insertUp w) . onWorkspace from (delete' w)
--LIQUID 
--LIQUID onWorkspace :: (Eq i, Eq s) => i -> (StackSet i l a s sd -> StackSet i l a s sd)
--LIQUID             -> (StackSet i l a s sd -> StackSet i l a s sd)
--LIQUID onWorkspace n f s = view (currentTag s) . f . view n $ s
--LIQUID 
--LIQUID 
--LIQUID 
--LIQUID 
--LIQUID -------------------------------------------------------------------------------
--LIQUID ------------------------------- Functions on Lists ----------------------------
--LIQUID -------------------------------------------------------------------------------
--LIQUID 
--LIQUID 
--LIQUID 
{-@ reverse :: xs:(UList a)
            -> {v: UList a | (EqElts v xs)} 
  @-}
reverse :: [a] -> [a]
reverse = rev []


{-@ rev :: ack:(UList a) 
        -> xs:{v: UList a | (ListDisjoint ack v)}
        -> {v:UList a |(UnionElts v xs ack)} 
  @-}
rev :: [a] -> [a] -> [a]
rev a []     = a
rev a (x:xs) = rev (x:a) xs 

--LIQUID {- filterL :: (a -> Bool) -> xs:(UList a) -> {v:UList a | (SubElts v xs)} @-}
--LIQUID filterL :: (a -> Bool) -> [a] -> [a]
--LIQUID filterL p [] = []
--LIQUID filterL p (x:xs) | p x       = x : filterL p xs
--LIQUID                  | otherwise = filterL p xs
--LIQUID 

-- QUALIFIERS
{-@ q :: x:a ->  {v:[a] |(not (Set_mem x (listElts v)))} @-}
q :: a -> [a]
q = undefined

{-@ q1 :: xs:[a] ->  {v:a |(not (Set_mem v (listElts xs)))} @-}
q1 :: [a] -> a
q1 = undefined

{-@ q2 :: UStack a -> UList a @-}
q2 :: Stack a -> [a]
q2 = undefined


