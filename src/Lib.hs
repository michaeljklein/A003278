{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Lib where

import Data.Profunctor
import GHC.Generics
import Control.Foldl (Fold(..), FoldM(..), purely, impurely)
import qualified Control.Foldl as F
import Data.Ratio
import Data.Time.Clock
import Data.Maybe
import Data.Bifunctor
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Trans.State.Strict (StateT(..))
import Control.Monad.IO.Class
import Data.List
import Control.Monad
import System.Environment

-- | First differences
diff :: Num a => [a] -> [a]
diff = zipWith(-) =<< tail


-- | Nest a function @n@ times on the input
nest :: Int -> (a -> a) -> a -> a
nest 0 _ x = x
nest 1 f x = f x
nest n f x = nest (n - 1) f (f x)

-- | Finding cycles in series efficiently:
--
-- @
--  Make a map from values in the series to the initial offset of the value and the sizes of gaps between each value.
--    For example:
--      1,1,2,2,2,1,3,1,3,2,1,3,2,1,2,3
--    =>
--      1 => (0, [0,3,1,2,2])
--      2 => (2, [0,0,4,2,1])
--      3 => (6, [1,2,3])
--
--  First, note that there is a cycle containing x only if the sizes of the gaps between x's cycle (constant, i.e. one element cycles are valid).
--
--  Next, note that if (x) cycles with period (p), and if the next (p-1) value after the initial (x) also cycle, with periods p1, p2, .. p(p0 - 1),
--                     then we may be able to combine the cycles into a single one.
--                     In particular, if all other periods divide p0, then it's valid.
--                     If any period is a multiple of p0, we need to continue checking for that period. e.g. if p0 = 2, p1 = 4, then they're compatible iff p3 is compatible with p0
--
--  Since the map transformation results in strictly smaller cycle problems, we recurse on those problems to solve them in a similar way.
--    (with guaranteed termination)
--
--  We can lazily construct the intermediate solutions recursively for all subproblems while traversing each series.
--
--  The problem then becomes of how lazy evaluation affects the time performance, whether some subproblems can be parallelized, and whether there's a better performance order than on-demand.
--
--  - This looks like comonads, especially the duplication and (co?) recursion
--  - We probably also want to store how long the current cycle has been going + how many values we've traversed.
--    This should allow computing cycles for any offset from the front at the same time.
--      (In the stack of gaps, we also store the number of previous equal, cycling values and their period).
--
--  -- valuePositionDiffMap :: (Foldable t, Ord a) => t a -> Map a (Int, [Int])
--  -- valuePositionDiffMap =
--
--  valuePositionDiffMap :: Ord a => Fold a (Map a (Int, [Int]))
--
--  valuePositionDiffMapM :: Ord a => FoldM (State (Map a (Int, [Int]))) a ()
-- @
--
findingCyclesInSeries :: ()
findingCyclesInSeries = ()

-- | Strict `Int`-indexed values
data Indexed a = Indexed
  { indexOf :: {-# UNPACK #-} !Int
  , indexed :: a
  } deriving (Eq, Ord, Show, Read, Functor, Generic, Generic1)

instance Foldable Indexed where
  foldr f x = (`f` x) . indexed
  foldMap f = f . indexed

instance Traversable Indexed where
  traverse f ~(Indexed i x) = Indexed i <$> f x
  sequenceA ~(Indexed i x) = Indexed i <$> x

-- | `uncurry` for `Indexed`
uncurryi :: (Int -> a -> b) -> Indexed a -> b
uncurryi f ~(Indexed i x) = f i x

-- | `curry` for `Indexed`
curryi :: (Indexed a -> b) -> Int -> a -> b
curryi f !i x = f $ Indexed i x

-- | Convert an indexed fold to one that is not indexed, but also returns the length of the input.
ifoldLen :: Fold (Indexed a) b -> Fold a (Indexed b)
ifoldLen f = (`purely` f) $ \stp ini ext -> Fold (\(~(Indexed i x)) -> Indexed (i + 1) . stp x . Indexed i) (Indexed 0 ini) (fmap ext)

-- | Convert an indexed monadic fold to one that is not indexed, but also returns the length of the input.
ifoldLenM :: Monad m => FoldM m (Indexed a) b -> FoldM m a (Indexed b)
ifoldLenM f = (`impurely` f) $ \stp ini ext -> FoldM (\(~(Indexed i x)) -> fmap (Indexed (i + 1)) . stp x . Indexed i) (Indexed 0 <$> ini) (mapM ext)

-- | Add an additional position to a position difference map
stepPositionDiffMap :: Ord a => Int -> a -> Map a (Indexed [Int]) -> Map a (Indexed [Int])
stepPositionDiffMap !i x = M.alter (Just . maybe (Indexed i []) (fmap (i :))) x

-- | Fold into a position difference map
positionDiffMap :: Ord a => Fold a (Indexed (Map a (Indexed [Int])))
positionDiffMap = ifoldLen (Fold (flip $ uncurryi stepPositionDiffMap) mempty id)

-- | Position differences resulting from a series of @a@
newtype PosDiffs a = PosDiffs { getPosDiffs :: Map a (Indexed [Int]) }

-- | `PosDiffs` specialized to integers
newtype IntPosDiffs = IntPosDiffs { getIntPosDiffs :: IntMap (Indexed [Int]) }

{-
So, when we recurse, we start with a layer of a's (PosDiffs) and then all subsequent layers are IntPosDiffs.

- Should we also include a list of values by first occurrence?
  This could make it easier to operate on PosDiffs by allowing us to traverse the list.

- I think it should be an exceptional Cofree,
  where the exception is that cycles to merge up have been found (monads propagate up).
  So the normal layer will look something like:
  Except resultFound (IntMap (Indexed ([Int], Except resultFound (IntMap ..


When we insert a new value, we update the top-level map, propagate the new differences/etc down the comonad, propagating up any solutions to re-merge and continue with.

I believe this is a form of dynamic programming.

(Extend to Reals by binning or by changing how we recognize cycles (e.g. if all values within 1% of each other, make bin for them. OR allow pseudocycles))


-- pseudocycles:
--   (a+b+c+d+e+f+)+
--
-- (1+0+)+
--   10
--   101010
--   110
--   110110110
--   1100
--   1100110011001100

I think you find pseudocycles by tallying the list (tally = fmap (first length . join (,)) . group) and then the cycles of that list without multiplicities are the pseudocycles.
-}


-- | po-cycles (partial-order cycles):
-- the cycles of the comparisions between successive elements.
partialOrderCycles :: ()
partialOrderCycles = ()

-- | Non-empty cycles, composed of an index of rotation and a rotated state.
--
-- @
--  Operations are provided to:
--  - extract/build from index/state
--  - map over each
--  - rotations (succIxF, predIxF, seekIxF)
--  - relative indexing
--
--  Example instances:
--  - cyclically indexed list, vector, etc.
--  - _
-- @
--
class CycleIx (f :: *) a where
  data IxState f a :: *

  -- | For example:
  --
  -- @
  --  data IxF f a = IxF
  --    { ixFindex :: !Int
  --    , ixFstate :: IxState f a
  --    }
  -- @
  --
  data IxF f a :: *

  -- | Half of an isomophism:
  --
  -- @
  --  `uncurry` `toIxF` :: (`Int`, `IxState` f a) -> `IxF` f a
  --  `liftM2` (,) `ixF` `ixState` :: `IxF` f a -> (`Int`, `IxState` f a)
  -- @
  toIxF :: Int -> IxState f a -> IxF f a
  ixF :: IxF f a -> Int
  ixState :: IxF f a -> IxState f a

  mapIxF :: (Int -> Int) -> IxF f a -> IxF f a
  mapIxF f = liftM2 toIxF (f . ixF) ixState

  mapIxState :: (IxState f a -> IxState f a) -> IxF f a -> IxF f a
  mapIxState f = liftM2 toIxF ixF (f . ixState)

  bimapIxF :: (Int -> Int) -> (IxState f a -> IxState f a) -> IxF f a -> IxF f a
  bimapIxF f g = mapIxF f . mapIxState g

  succIxF :: IxF f a -> IxF f a
  succIxF = seekIxF 1

  predIxF :: IxF f a -> IxF f a
  predIxF = seekIxF (-1)

  seekIxF :: Int -> IxF f a -> IxF f a
  seekIxF i = case compare i 0 of
                LT -> nest (negate i) predIxF
                EQ -> id
                GT -> nest i succIxF

  headIxF :: IxF f a -> a
  headIxF = indexIxF 0

  indexIxF :: Int -> IxF f a -> a
  indexIxF i = headIxF . seekIxF i

  buildIxF :: a -> IxF f a

  snocIxF :: a -> IxF f a -> IxF f a

  foldableIxF :: Foldable t => t a -> Maybe (IxF f a)
  foldableIxF = foldl1Maybe (flip snocIxF) buildIxF
    where
      foldl1Maybe f g = foldl (\x y -> Just $ maybe (g y) (`f` y) x) Nothing


-- data Map k a

-- | Non-empty sequences
data Seq1 a

-- | Non-empty sequences of `Int`s
data IntSeq1

data Cycled a = Cycled
  { runCycled :: Map a ValueState
  , cycle :: IxF (Seq1 a) a
  , cycleLen :: Int
  , cycleReps :: Int
  }


data IntCycled = IntCycled
  { runIntCycled :: IntMap ValueState
  , currentCycle :: IntSeq1
  , currentCycleLen :: Int
  , currentCycleReps :: Int
  }

data ValueState = ValueState
  { firstPos :: {-# UNPACK #-} !Int
  , lastPos  :: {-# UNPACK #-} !Int
  , locPositions :: IntCycled
  }

-- | `undefined`
stepCycled :: Ord a => Cycled a -> a -> Cycled a
stepCycled Cycled{..} newVal =
  Cycled undefined undefined undefined undefined


-- | This is a first approximation of a division based "finite differences" data type.
--
-- It will need a way to handle division by zero better.
--
-- @
--   What about saying that the modulo must be in [0..modulus] for non-zero and [1..] for zero?
--   In addition, defining: 0 `div` 0 = 1?
--   Then: prevs, 0, positive, .. -> (0, positive) : ..
--
--   If 0/0 = 1
--     Then: prevs, 0, 0, .. -> (1, 0) : ..
--
--   If 0/0 = 0
--     Then: prevs, 0, 0, .. -> (0, 0) : ..
--
--  0/0 = 0 might be better.. it might be closer to "continuous"
-- @
--
data ProdDiff a = ProdDiff
  { prodDiffHead :: [a]
  , prodDiffTail :: [(a, [a])]
  }

-- | The next `ProdDiff` or `Nothing` if the head is empty
succProdDiffMaybe :: Integral a => ProdDiff a -> Maybe (ProdDiff a)
succProdDiffMaybe ProdDiff{..} = do
  ~(seed, (divs, mods)) <- fmap unzip <$> divMods prodDiffHead
  return $ ProdDiff
    { prodDiffHead = divs
    , prodDiffTail = (seed, mods) : prodDiffTail
    }

-- | `divMods` with known first value (so no `Maybe` and not returned)
divMods1 :: Integral a => a -> [a] -> [(a, a)]
divMods1 _ [] = []
divMods1 x ~(y:ys) = divMod y x : divMods1 y ys

-- | `div`s and `mod`s of previous values, with an initial value,
-- or `Nothing` if the list is empty.
divMods :: Integral a => [a] -> Maybe (a, [(a, a)])
divMods [] = Nothing
divMods [x] = Just (x, [])
divMods ~(x:y:zs) = Just (x, snd <$> scanl (ap (,) . divMod . fst) (y, divMod y x) zs)

-- | The previous `ProdDiff` series or itself if the tail is empty
predProdDiff :: Num a => ProdDiff a -> ProdDiff a
predProdDiff = fromMaybe <*> predProdDiffMaybe

-- | The previous `ProdDiff` series or `Nothing` if the tail is empty
predProdDiffMaybe :: Num a => ProdDiff a -> Maybe (ProdDiff a)
predProdDiffMaybe ProdDiff {..} =
  case prodDiffTail of
    [] -> Nothing
    ~((seed, mods):xs) ->
      Just $
      ProdDiff
        { prodDiffHead = predProdDiffWith seed prodDiffHead mods
        , prodDiffTail = xs
        }

-- | The previous `ProdDiff`, using the given list
predProdDiffWith :: Num a => a -> [a] -> [a] -> [a]
predProdDiffWith seed = -- prodDiffHead' mods =
  fmap (scanl folder seed) . zip
    where
      folder memo ~(div', mod') = memo * div' + mod'


-- | Notes on arithmetic progressions
--
-- @
--  = zipWith (\x mod' ->
--
--  as = [a0, a1, a2, a3, ..]
--
--  divs = [a1 `div` a0, a2 `div` a1, a3 `div` a2, ..]
--  mods = [a1 `mod` a0, a2 `mod` a1, a3 `mod` a2, ..]
--
--  as = [a0, a0 * d1 + mod1, % * d2 + mod2, % * d3 + mod3, ..]
--
--  as :: Set (Positive Integer)
--  if sum [1 / a | a <- as] == infinity
--  then
--  forall (n :: Natural).
--    exists (k :: N).
--      isArithmeticSeries [a !! (k + i) | i <- [0..n]]
--
--  in other words, if
--                    sum . fmap (1 /) == const infinity
--                  then
--                    there are arithmetic progressions of every length.
--
--  For example, all elements are arithmetic progressions of length 1 and all pairs of elements are arithmetic progressions of length 2.
--  @
--
arithmeticProgressionNotes :: ()
arithmeticProgressionNotes = ()

-- | Get akk arithmetic progressions of all lengths
arithProgs :: (Num a, Eq a) => [a] -> [[a]]
arithProgs xs = [2..length xs] >>= (`arithProgsLen` xs)

-- | Check for arithmetic progressions of a given length
arithProgsLen :: (Num a, Eq a) => Int -> [a] -> [[a]]
arithProgsLen n _ | n < 1 = error "n < 1"
arithProgsLen n xs = mapMaybe (predMaybe isArithProg) $ succSeries n xs

-- | Is it an arithmetic progression?
isArithProg :: (Num a, Eq a) => [a] -> Bool
isArithProg = liftM2 (\x -> all (== x)) head tail . diff

-- | `Just` if the predicate returns `True`
{-# INLINE predMaybe #-}
predMaybe :: (a -> Bool) -> a -> Maybe a
predMaybe p x = if p x
                   then Just x
                   else Nothing

-- | @`succSeries` 2@
succPairs = succSeries 2

-- | `takeExactly` @n@ for every `tail` in `tails` and
-- drop `tails` with fewer values
succSeries :: Int -> [a] -> [[a]]
succSeries n = mapMaybe (takeExactly n) . tails

-- | Take exactly the given number of elements or return `Nothing`
takeExactly :: Int -> [a] -> Maybe [a]
takeExactly 0 _  = Just []
takeExactly _ [] = Nothing
takeExactly n ~(x:xs) = (x :) <$> takeExactly (n - 1) xs

-- | An infinite list of prime numbers, using a sieve method
primes :: [Integer]
primes = sieve (2 : [3, 5..])
  where
    sieve (p:xs) = p : sieve [x |x <- xs, x `mod` p > 0]

-- @
--  Want: Series, [1,..]
--    where
--      next value is minimum > maximum such that there are no arithmetic progressions of length 3.
-- @
--
data Universe = Universe
  { maxVal :: {-# UNPACK #-} !Int
  , series :: !IntSet
  } deriving (Eq, Ord, Show)

-- | Initial universe, with @`series` = [1]@
initialUniverse :: Universe
initialUniverse = Universe 1 [1]

-- | The next value in a `Universe`
nextVal :: Universe -> Int
nextVal universe'@Universe{..} = head $ filter (validNextVal universe') [maxVal+1..]

-- | Is the next value valid?
--
-- A value is invalid if its addition to the series would result in an
-- arithmetic progression of length 3.
validNextVal :: Universe -> Int -> Bool
validNextVal Universe {..} x =
  not $ IS.foldl' (\y i -> y || IS.member (2 * i - x) series) False series
  -- (not (odd x && halfPoint `IS.member` series) &&) $
  -- case (2 * maxVal) `compare` x of
  --   LT -> True -- 2 * maxVal < x; maxVal < x - maxVal; maxVal - (x - maxVal) = 2 * maxVal - x < 0 `notElem` xs
  --   EQ -> True -- 2 * maxVal == x; x - maxVal == maxVal; maxVal - maxVal == 0 `notElem` xs
  --   GT ->
      -- case IS.splitMember halfPoint series of
      --   ~(ltSeries, isElem', gtSeries) ->
      --     not isElem' &&
      --     (IS.foldl'
      --        (\y i -> y && ((2 * i - x) `IS.notMember` ltSeries))
      --        True
      --        gtSeries)
  -- where
    -- halfPoint = div (1 + x) 2

-- | Add a value to the series, without checking whether it's valid
addNextVal :: Int -> Universe -> Universe
addNextVal !x Universe{..} = x `Universe` IS.insert x series

-- | Find and add the next value to the `Universe`
stepUniverse :: Universe -> Universe
stepUniverse = liftM2 addNextVal nextVal id

-- | All `Universe`s, starting with the `initialUniverse`
universes :: [Universe]
universes = iterate stepUniverse initialUniverse


someFunc2 :: IO ()
someFunc2 =
  evalMemoT $ do
    let xs =
          onlyEvery 100 . zip [0 ..] . scanl1 (liftM2 (+)) $
          fmap ((1 %) . fromInteger) . rec3M <$> [0 ..]
    mapMTimed_
      (\(i, x) ->
         x >>= \x' ->
           mapM_ (liftIO . print) .
           (\(~(x, (y, z))) -> [x, y, z] :: [Double]) .
           fmap
             (fmap (exp . exp) .
              join (,) . (`asTypeOf` (0.0 :: Double)) . fromRational) $
           (fromInteger i, x'))
      xs

someFunc :: IO ()
someFunc =
  mapMTimed_
    (mapM_ print .
     (\(~(x, (y, z))) -> [x, y, z] :: [Double]) .
     fmap
       (fmap (exp . exp) .
        join (,) . (`asTypeOf` (0.0 :: Double)) . fromRational)) .
  onlyEvery 1000 .
  zip [0 ..] . scanl1 (+) . fmap ((1 %) . fromInteger) . fmap rec3 $
  [0 ..]

-- | Extended idea:
--
-- @
--  Extend idea:
--  - Tree defined as:
--    step prevTree = traverse over complete trees, finding their minimal values
--      for each found, [found..] is a valid extension, forming the next layer of the tree.
--
--  e.g. binary tree, minimal, minimal + 1.
--
--  Maybe it's possible to derive the value from the path.
-- @
--
extendedIdea :: ()
extendedIdea = ()

-- | Only keep one out of every @n@
onlyEvery :: Int -> [a] -> [a]
onlyEvery n xs = case drop n xs of
                   ~(y:ys) -> y : onlyEvery n ys

-- | Example with `mapMTimed_`
exampleMapMTimed_ :: IO ()
exampleMapMTimed_ = do
  m <- read . head <$> getArgs
  mapMTimed_ (printModM m . fmap (fmap (IS.size . series) . join (,))) $ zip [0..] universes
  where
    printModM m xs@(n, ys)
      | mod n m == 0 = print xs
      | otherwise   = print . maxVal $ fst ys

-- (Integer, (Universe, Int)) -> IO ()

-- | `mapM_` where results are `timed` and the timing is printed
-- with the results
mapMTimed_ :: MonadIO m => (a -> m ()) -> [a] -> m ()
mapMTimed_ _ [] = liftIO $ putStrLn "(done)"
mapMTimed_ f ~(x:xs) = do
  seconds <- (/ 1000000000000.0) .fromInteger . toEnum . fromEnum <$> timed (f x)
  liftIO . putStrLn $ unwords ["Took", show (seconds :: Double), "s"]
  mapMTimed_ f xs

-- | Run a monadic action and return its duration
timed :: MonadIO m => m () -> m NominalDiffTime
timed action = do
  timeBefore <- liftIO getCurrentTime
  action
  timeAfter <- liftIO getCurrentTime
  return $ timeAfter `diffUTCTime` timeBefore

-- | Third implementation
--
-- @
--  rec0 n = case divMod n 2 of
--             (n', 0) ->
--
--  a(2k + 2) = a(2k + 1) + 1, a(2^k + 1) = 2*a(2^k).
--
--  it appears that (rec3 x `mod` 3^i) cycles with period 2^i.
--
--  i.e.,
--    rec3 x `mod` 3^i == rec3 (mod x 2^i) `mod` 3^i
-- @
--
rec3 :: Integer -> Integer
rec3 n = loop (n + 1)
  where
    loop :: Integer -> Integer
    loop 0 = 1
    loop m = uncurry (-) . bimap ((3 *) . loop) (2 -) $ divMod m 2

-- | Notes on the recursion:
--
-- @
--  3 * loop (n `div` 2) - (2 - mod n 2)
--  3 * loop (n `div` 2) - 2 + mod n 2
--
--  3 * (3 * loop (n `div` 4) - 2 + mod (n `div` 2) 2) - 2 + mod n 2
--  9 * loop (n `div` 4) - 6 + 3 * mod (n `div` 2) - 2 + mod n 2
--  9 * loop (n `div` 4) - 8 + 3 * mod (n `div` 2) + mod n 2
--
--  9 * (3 * loop (n `div` 8) - 2 + mod (n `div` 4)) - (3 * 2 + 2) + 3 * mod (n `div` 2) + mod n 2
--  27 * loop (n `div` 8) - 9 * 2 + 9 * mod (n `div` 4)) - (3 * 2 + 2) + 3 * mod (n `div` 2) + mod n 2
--  27 * loop (n `div` 8) - (9 * 2 + 3 * 2 + 2) + 9 * mod (n `div` 4) + 3 * mod (n `div` 2) + mod n 2
--
--  3^i * loop (n `div` 2^i) - 2 * sum [3^j | j <- [0..i-1]] + sum [3^j * mod (n `div` 2^j) | j <- [0..i-1]]
--
--  OK
--    So it looks like I screwed up the algebra somewhere, but otherwise the theory seems sound.
--    It looks like I might be able to travel from minBit to maxBit and multiply the 3's as I go instead of computing powers as well.
--
--  This would result in a log2 time algorithm, with a couple additions, multiplications, bitshifts, etc. per bit.
--
--  (1/a + 1/b)
--  (a + b) / (a * b)
--  (a `div` gcd a b + b `div` gcd a b) / lcm a b
--
--  suppose:
--    n = sum [an j * 2^j | j <- [0..m]]
--    where an m = 1
--  then
--    loop hits 0 at i = m
--    loop n = sum [3^j * mod (n `div` 2^j) | j <- [0..i-1]] - 2 * sum [3^j | j <- [0..i-1]]
--    loop n = sum [3^j * (2 - mod (n `div` 2^j) 2) | j <- [0..i-1]]
--
--    loop n = sum [3^j * mod (n `div` 2^j) | j <- [0..i-1]] - 2 * ((3^(i - 1) - 1) / 2)
--    loop n = sum [3^j * mod (n `div` 2^j) | j <- [0..i-1]] + 1 - 3^(i - 1)
--
--  a(n)-1 in ternary = n-1 in binary
-- @
--
notesOnRheRecursion :: ()
notesOnRheRecursion = ()


-- | Simple implementation of a memoization `Monad` transformer to
-- memoize a function of the type:
--
-- @
--  Int -> Integer
-- @
--
type MemoT = StateT (IntMap Integer)

-- | Run `MemoT` with no initially known values
--
-- Return the result along with an `IntMap` containing
-- all computed values
runMemoT :: Monad m => MemoT m a -> m (a, IntMap Integer)
runMemoT = ($ [(0, 1)]) . runStateT

-- | `runMemoT` without the `IntMap` of results
evalMemoT :: Monad m => MemoT m a -> m a
evalMemoT = fmap fst . runMemoT

-- | `rec3` memoized with `MemoT`
rec3M :: Monad m => Integer -> MemoT m Integer
rec3M n = loop (n + 1)
  where
    loop :: Monad m => Integer -> MemoT m Integer
    loop x =
      StateT $ \mp -> do
        let x' = fromEnum x
        case mp IM.!? x' of
          Nothing -> do
            ~(y, mp') <-
              runMemoT $
              uncurry (liftM2 (-)) . bimap (fmap (3 *) . loop) (return . (2 -)) $
              divMod x 2
            return (y, IM.insert (fromEnum x) y mp')
          ~(Just m') -> return (m', mp)

-- | Conjecture on arithmetic progressions
--
-- @
--  conjecture:
--    if each arithmetic-progression free size has a lower bound of the above form, i.e. f n = k * f (div n (progressionSize - 1)) + line (mod n (progressionSize - 1))
--       then since each one forms a lower bound for the minimal series that's ..-free, it forms an uppwer bound for the sum of its reciprocals.
--         but since its guaranteed to be at least exponential..
--
--  a(n) = b(n+1) with b(0)=1, b(2n)=3b(n)-2, b(2n+1)=3b(n)-1
-- @
--
arithProgConjecture :: ()
arithProgConjecture = ()

