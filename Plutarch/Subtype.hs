{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Subtype (
  PSubtype (..),
  HRecP (..),
  pdowncast,
  pupcast,
) where

import Data.Proxy (Proxy (Proxy))

import GHC.TypeLits (KnownNat, Nat, Symbol, natVal, type (+))

import Plutarch.Unsafe (punsafeCoerce, punsafeFrom)

import Plutarch.Bool (pif, (#==))
import Plutarch.ByteString (PByteString)
import Plutarch.Integer (PInteger)
import Plutarch.Unit (PUnit (PUnit))

import Plutarch.Internal.Other (
  DerivePNewtype,
  PInner,
  POpaque,
  PType,
  S,
  Term,
  pcon,
  pdelay,
  pforce,
  plam,
  plet,
  popaque,
  (#),
  type (:-->),
 )

import Plutarch.Trace (ptraceError)

import Plutarch.DataRepr.Internal.HList (HRec (HCons, HNil), HRecGeneric (HRecGeneric), Labeled (Labeled))

import Plutarch.DataRepr.Internal (
  PDataRecord,
  PDataSum,
  PLabeledType ((:=)),
  pdnil,
 )

import Plutarch.List (
  phead,
  pmap,
  ptail,
 )

import Plutarch.Builtin (
  PAsData,
  PBuiltinList,
  PBuiltinMap,
  PBuiltinPair,
  PData,
  PIsData (pfromData),
  pasByteStr,
  pasConstr,
  pasInt,
  pasList,
  pasMap,
  pchooseListBuiltin,
  pdata,
  pforgetData,
  pfstBuiltin,
  ppairDataBuiltin,
  psndBuiltin,
 )

import Plutarch.TermCont (TermCont (TermCont, runTermCont), tcont, unTermCont)

import Plutarch.DataRepr.Internal (PIsDataRepr (PIsDataReprRepr), PIsDataReprInstances)

import Plutarch.Reducible (Reducible (Reduce))

import Data.Functor.Const (Const)

import Data.Kind (Type)

import Data.Coerce (coerce)

----------------------- The class PSubtype ----------------------------------------------

{- |
@PSubtype a b@ represents a subtyping relationship between @a@ and @b@.
Laws:
- @(punsafeCoerce . fst) <$> tcont (pdowncast x) ≡ pure x@
- Any term that is a @b@ should also be a valid @a@.
-}
class PSubtype (a :: PType) (b :: PType) where
  type PSubtypeExcess a b :: PType
  pdowncast' :: forall s r. Term s a -> ((Term s b, Reduce (PSubtypeExcess a b s)) -> Term s r) -> Term s r

pdowncast :: forall b a s r. PSubtype a b => Term s a -> ((Term s b, Reduce (PSubtypeExcess a b s)) -> Term s r) -> Term s r
pdowncast = pdowncast'

pupcast :: forall a b s. PSubtype a b => Term s b -> Term s a
pupcast = punsafeCoerce

----------------------- Reducible and Flip ----------------------------------------------

instance Reducible (f x y) => Reducible (Flip f y x) where
  type Reduce (Flip f y x) = Reduce (f x y)

newtype Flip f a b = Flip (f b a)

----------------------- HRecP and friends -----------------------------------------------

type HRecPApply :: [(Symbol, PType)] -> S -> [(Symbol, Type)]
type family HRecPApply as s where
  HRecPApply ('(name, ty) ': rest) s = '(name, Reduce (ty s)) ': HRecPApply rest s
  HRecPApply '[] s = '[]

newtype HRecP (as :: [(Symbol, PType)]) (s :: S) = HRecP (HRecGeneric (HRecPApply as s))

instance Reducible (HRecP as s) where type Reduce (HRecP as s) = HRecGeneric (HRecPApply as s)

----------------------- PData instances -------------------------------------------------

instance PSubtype PData (PAsData PInteger) where
  type PSubtypeExcess PData (PAsData PInteger) = Flip Term PInteger
  pdowncast' opq = runTermCont $ do
    ver <- tcont $ plet (pasInt # opq)
    pure $ (punsafeCoerce opq, ver)

instance PSubtype PData (PAsData PByteString) where
  type PSubtypeExcess PData (PAsData PByteString) = Flip Term PByteString
  pdowncast' opq = runTermCont $ do
    ver <- tcont $ plet (pasByteStr # opq)
    pure $ (punsafeCoerce opq, ver)

instance
  ( PSubtype PData (PAsData a)
  , PSubtype PData (PAsData b)
  ) =>
  PSubtype PData (PAsData (PBuiltinMap a b))
  where
  type PSubtypeExcess PData (PAsData (PBuiltinMap a b)) = Flip Term (PBuiltinMap a b)
  pdowncast' opq = runTermCont $ do
    verMap <- tcont $ plet (pasMap # opq)
    let verifyPair :: Term _ (PBuiltinPair PData PData :--> PBuiltinPair (PAsData a) (PAsData b))
        verifyPair = plam $ \tup -> unTermCont $ do
          (verfst, _) <- tcont $ pdowncast @(PAsData a) $ pfstBuiltin # tup
          (versnd, _) <- tcont $ pdowncast @(PAsData b) $ psndBuiltin # tup
          pure $ ppairDataBuiltin # verfst # versnd
    ver <- tcont $ plet $ pmap # verifyPair # verMap
    pure (punsafeCoerce opq, ver)

{- |
    This verifies a list to be indeed a list but doesn't recover the inner data
    use this instance instead of the one for `PData (PAsData (PBuiltinList (PAsData a)))`
    as this is O(1) instead of O(n)
-}

-- TODO: add the excess inner type list
instance PSubtype PData (PAsData (PBuiltinList PData)) where
  type PSubtypeExcess PData (PAsData (PBuiltinList PData)) = Flip Term (PBuiltinList PData)
  pdowncast' opq = runTermCont $ do
    ver <- tcont $ plet (pasList # opq)
    pure $ (punsafeCoerce opq, ver)

{- |
    Recover a `PBuiltinList (PAsData a)`
-}
instance
  ( PSubtype PData (PAsData a)
  , PIsData a
  ) =>
  PSubtype PData (PAsData (PBuiltinList (PAsData a)))
  where
  type PSubtypeExcess PData (PAsData (PBuiltinList (PAsData a))) = Flip Term (PBuiltinList (PAsData a))
  pdowncast' opq = runTermCont $ do
    let lst :: Term _ (PBuiltinList PData)
        lst = pasList # opq
        verify :: Term _ (PData :--> PAsData a)
        verify = plam $ \e ->
          unTermCont $ do
            (wrapped, _) <- tcont $ pdowncast @(PAsData a) $ e
            pure wrapped
    ver <- tcont $ plet $ pmap # verify # lst
    pure $ (punsafeCoerce opq, ver)

{- |
    Recover a `PAsData (PBuiltinPair a b)`
-}
instance
  ( PSubtype PData a
  , a ~ PAsData a'
  , PIsData a'
  , PSubtype PData b
  , b ~ PAsData b'
  , PIsData b'
  ) =>
  PSubtype PData (PAsData (PBuiltinPair a b))
  where
  type PSubtypeExcess PData (PAsData (PBuiltinPair a b)) = Flip Term (PBuiltinPair a b)
  pdowncast' opq = runTermCont $ do
    tup <- tcont $ plet (pfromData $ punsafeCoerce opq)
    let fst' :: Term _ a
        fst' = unTermCont $ fst <$> tcont (pdowncast @a $ pforgetData $ pfstBuiltin # tup)
        snd' :: Term _ b
        snd' = unTermCont $ fst <$> tcont (pdowncast @b $ pforgetData $ psndBuiltin # tup)
    ver <- tcont $ plet $ ppairDataBuiltin # fst' # snd'
    pure $ (punsafeCoerce opq, ver)

----------------------- PDataRecord instances -------------------------------------------

-- We could have a more advanced instance but it's not needed really.

newtype ExcessForField (a :: PType) (s :: S) = ExcessForField (Term s (PAsData a), Reduce (PSubtypeExcess PData (PAsData a) s))

instance Reducible (PSubtypeExcess PData (PAsData a) s) => Reducible (ExcessForField a s) where
  type Reduce (ExcessForField a s) = (Term s (PAsData a), Reduce (PSubtypeExcess PData (PAsData a) s))

-- FIXME: Should we always succede? If we always succede, performance would increase a lot.
instance PSubtype (PBuiltinList PData) (PDataRecord '[]) where
  type PSubtypeExcess (PBuiltinList PData) (PDataRecord '[]) = HRecP '[]
  pdowncast' opq = runTermCont $ do
    _ :: Term _ PUnit <-
      tcont . plet . pforce $
        pchooseListBuiltin # opq # pdelay (pcon PUnit) # pdelay (ptraceError "list is longer than zero")
    pure (pdnil, HRecGeneric HNil)

type family UnHRecP (x :: PType) :: [(Symbol, PType)] where
  UnHRecP (HRecP as) = as

instance
  ( PSubtype PData (PAsData pty)
  , PSubtype (PBuiltinList PData) (PDataRecord as)
  , PSubtypeExcess (PBuiltinList PData) (PDataRecord as) ~ HRecP ase
  ) =>
  PSubtype (PBuiltinList PData) (PDataRecord ((name ':= pty) ': as))
  where
  type
    PSubtypeExcess (PBuiltinList PData) (PDataRecord ((name ':= pty) ': as)) =
      HRecP
        ( '(name, ExcessForField pty)
            ': UnHRecP (PSubtypeExcess (PBuiltinList PData) (PDataRecord as))
        )
  pdowncast' opq = runTermCont $ do
    h <- tcont $ plet $ phead # opq
    hv <- tcont $ pdowncast @(PAsData pty) @PData h
    t <- tcont $ plet $ ptail # opq
    tv <- tcont $ pdowncast @(PDataRecord as) @(PBuiltinList PData) t
    pure (punsafeCoerce opq, HRecGeneric (HCons (Labeled hv) (coerce $ snd tv)))

newtype Helper a b s = Helper (a s, b s)

instance (Reducible (a s), Reducible (b s)) => Reducible (Helper a b s) where
  type Reduce (Helper a b s) = (Reduce (a s), Reduce (b s))

instance
  ( PSubtype (PBuiltinList PData) (PDataRecord as)
  , PSubtypeExcess (PBuiltinList PData) (PDataRecord as) ~ HRecP ase
  ) =>
  PSubtype PData (PAsData (PDataRecord as))
  where
  type
    PSubtypeExcess PData (PAsData (PDataRecord as)) =
      Helper (Flip Term (PDataRecord as)) (PSubtypeExcess (PBuiltinList PData) (PDataRecord as))
  pdowncast' opq = runTermCont $ do
    l <- snd <$> (tcont $ pdowncast @(PAsData (PBuiltinList PData)) opq)
    r <- tcont $ pdowncast @(PDataRecord as) l
    pure (punsafeCoerce opq, r)

instance {-# OVERLAPPING #-} SumValidation 0 ys => PSubtype PData (PAsData (PDataSum ys)) where
  type PSubtypeExcess PData (PAsData (PDataSum ys)) = Const ()
  pdowncast' opq = runTermCont $ do
    x <- tcont $ plet $ pasConstr # opq
    constr <- tcont $ plet $ pfstBuiltin # x
    fields <- tcont $ plet $ psndBuiltin # x
    _ <- tcont $ plet $ validateSum @0 @ys constr fields
    pure (punsafeCoerce opq, ())

class SumValidation (n :: Nat) (sum :: [[PLabeledType]]) where
  validateSum :: Term s PInteger -> Term s (PBuiltinList PData) -> Term s POpaque

instance
  {-# OVERLAPPABLE #-}
  forall (n :: Nat) (x :: [PLabeledType]) (xs :: [[PLabeledType]]).
  ( PSubtype (PBuiltinList PData) (PDataRecord x)
  , SumValidation (n + 1) xs
  , KnownNat n
  ) =>
  SumValidation n (x ': xs)
  where
  validateSum constr fields =
    pif
      (fromInteger (natVal $ Proxy @n) #== constr)
      ( unTermCont $ do
          _ <- tcont $ pdowncast @(PDataRecord x) fields
          pure $ popaque $ pcon PUnit
      )
      (validateSum @(n + 1) @xs constr fields)

instance {-# OVERLAPPING #-} SumValidation n '[] where
  validateSum _ _ = ptraceError "reached end of sum while still not having found the constructor"

----------------------- other utility functions -----------------------------------------

{- | if there is an instance to recover something that is unwrapped from something that is
 unwrapped, then there is also the possibility to recover the whole thing but wrapped
-}
instance
  ( PSubtype a b
  , PIsData a
  , PIsData b
  ) =>
  PSubtype (PAsData a) (PAsData b)
  where
  type PSubtypeExcess (PAsData a) (PAsData b) = PSubtypeExcess a b
  pdowncast' opq = runTermCont $ do
    ver' <- snd <$> TermCont (pdowncast @b @a (pfromData opq))
    pure $ (punsafeCoerce opq, ver')

instance PSubtype PData PData where
  type PSubtypeExcess PData PData = Const ()
  pdowncast' opq = runTermCont $ pure $ (opq, ())

instance PSubtype PData (PAsData PData) where
  type PSubtypeExcess PData (PAsData PData) = Const ()
  pdowncast' opq = runTermCont $ pure (pdata opq, ())

----------------------- PIsDataReprInstances instance -----------------------------------

-- | you can instantiate `PSubtype` for your own datatype as demonstrated in the spec
instance
  ( PIsDataRepr a
  , SumValidation 0 (PIsDataReprRepr a)
  , PInner a b ~ PDataSum (PIsDataReprRepr a)
  ) =>
  PSubtype PData (PAsData (PIsDataReprInstances a))
  where
  type PSubtypeExcess PData (PAsData (PIsDataReprInstances a)) = Const ()
  pdowncast' opq = runTermCont $ do
    let reprsum :: Term _ (PDataSum (PIsDataReprRepr a))
        reprsum = pfromData $ unTermCont $ fst <$> TermCont (pdowncast opq)
    pure $ (pdata $ punsafeFrom reprsum, ())

----------------------- DerivePNewtype insatace -----------------------------------------

instance
  ( PSubtype a b
  ) =>
  PSubtype a (DerivePNewtype c b)
  where
  type PSubtypeExcess a (DerivePNewtype c b) = PSubtypeExcess a b
  pdowncast' opq = runTermCont $ (\(inn, exc) -> (punsafeFrom inn, exc)) <$> tcont (pdowncast @b @a opq)
