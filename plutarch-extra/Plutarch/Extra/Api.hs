module Plutarch.Extra.Api (
  getContinuingOutputs,
  findOwnInput,
  findDatum,
) where

import GHC.Records (HasField (getField))

import Plutarch.Api.V1 (
  PAddress,
  PDatum,
  PDatumHash,
  PScriptContext,
  PScriptPurpose (PSpending),
  PTuple,
  PTxInInfo (PTxInInfo),
  PTxInfo,
  PTxOut,
  PTxOutRef (PTxOutRef),
 )
import Plutarch.Prelude

import Plutarch.Extra.Monad (tmatch)

{- | gets a list of continuing outputs by finding
 - its own input and  returning a list of outputs with the same outAddress
-}
getContinuingOutputs :: Term s (PScriptContext :--> PBuiltinList PTxOut)
getContinuingOutputs = phoistAcyclic $
  plam $ \sc -> unTermCont $ do
    let txinfo = pfield @"txInfo" # sc
    tmatch (findOwnInput # sc) >>= \case
      PJust te -> do
        let outs = pfield @"outputs" # txinfo
            resolved = pfield @"resolved" # te
            outAdr = pfield @"address" # resolved
        pure $ pfilter # (matches # outAdr) #$ pmap # plam pfromData # outs
      PNothing ->
        pure $ ptraceError "can't get any continuing outputs"
  where
    matches :: Term s (PAddress :--> PTxOut :--> PBool)
    matches = phoistAcyclic $
      plam $ \adr txOut ->
        adr #== pfield @"address" # txOut

{- | tries to finds the transaction's input
 - by looking for a txininfo in the inputs coresponding to the TxOutRef which the script purpose is spending
-}
findOwnInput :: Term s (PScriptContext :--> PMaybe PTxInInfo)
findOwnInput = phoistAcyclic $
  plam $ \sc -> unTermCont $ do
    ctx <- tcont $ pletFields @["txInfo", "purpose"] sc
    tmatch (getField @"purpose" ctx) >>= \case
      PSpending outRef' -> do
        let outRef = pfield @"_0" # outRef'
        pure $
          pfind # (matches # outRef)
            #$ pmap # plam pfromData
            #$ pfromData
            $ pfield @"inputs" # (getField @"txInfo" ctx)
      _ ->
        pure $ pcon PNothing
  where
    matches :: Term s (PTxOutRef :--> PTxInInfo :--> PBool)
    matches = phoistAcyclic $
      plam $ \outref txininfo -> unTermCont $ do
        PTxOutRef outref' <- tmatch outref
        PTxInInfo txininfo' <- tmatch txininfo
        PTxOutRef inOutRef <- tmatch $ pfield @"outRef" # txininfo'
        pure $
          pfield @"id" # outref' #== pfield @"id" # inOutRef

-- | Looks up a datum by it's hash from the PTxInfo
findDatum :: Term s (PDatumHash :--> PTxInfo :--> PMaybe PDatum)
findDatum = phoistAcyclic $
  plam $ \dh txinfo -> unTermCont $ do
    let txInfoData = pfield @"data" # txinfo
        maybeEnt = pfind # (matches # dh) # txInfoData
    pure $
      pmatch maybeEnt $ \case
        PNothing -> pcon PNothing
        PJust x -> pcon $ PJust $ pfromData $ pfield @"_1" # x
  where
    matches :: Term s (PDatumHash :--> PAsData (PTuple PDatumHash PDatum) :--> PBool)
    matches = phoistAcyclic $
      plam $ \dh dataTupe -> unTermCont $ do
        let tupe = pfromData dataTupe
        pure $
          dh #== pfromData (pfield @"_0" # tupe)
