{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Integration.Scenario.API.Wallets
    ( spec
    ) where

import Prelude

import Cardano.Wallet.Api.Link
    ( Discriminate )
import Cardano.Wallet.Api.Types
    ( AddressAmount (..)
    , ApiCoinSelection
    , ApiT (..)
    , ApiTransaction
    , ApiUtxoStatistics
    , ApiWallet
    , WalletStyle (..)
    )
import Cardano.Wallet.Primitive.AddressDerivation
    ( NetworkDiscriminant (..)
    , PassphraseMaxLength (..)
    , PassphraseMinLength (..)
    )
import Cardano.Wallet.Primitive.AddressDiscovery.Sequential
    ( AddressPoolGap (..) )
import Cardano.Wallet.Primitive.Mnemonic
    ( entropyToMnemonic, genEntropy, mnemonicToText )
import Cardano.Wallet.Primitive.Types
    ( SyncProgress (..), WalletId, walletNameMaxLength, walletNameMinLength )
import Control.Monad
    ( forM_ )
import Data.Aeson
    ( FromJSON )
import Data.Generics.Internal.VL.Lens
    ( view, (^.) )
import Data.Generics.Product.Fields
    ( HasField' )
import Data.Generics.Product.Typed
    ( HasType )
import Data.List.NonEmpty
    ( NonEmpty ((:|)) )
import Data.Proxy
    ( Proxy (..) )
import Data.Quantity
    ( Quantity (..) )
import Data.Text
    ( Text )
import Data.Text.Class
    ( toText )
import GHC.Generics
    ( Generic )
import Numeric.Natural
    ( Natural )
import Test.Hspec
    ( SpecWith, describe, it, shouldBe, shouldNotBe, shouldSatisfy )
import Test.Integration.Framework.DSL
    ( Context (..)
    , Headers (..)
    , Payload (..)
    , emptyIcarusWallet
    , emptyRandomWallet
    , emptyWallet
    , eventually
    , expectErrorMessage
    , expectField
    , expectListField
    , expectListSize
    , expectResponseCode
    , expectWalletUTxO
    , fixtureWallet
    , getFromResponse
    , json
    , listAddresses
    , notDelegating
    , request
    , selectCoins
    , unsafeRequest
    , verify
    , walletId
    , (</>)
    )
import Test.Integration.Framework.TestData
    ( arabicWalletName
    , errMsg403RejectedTip
    , errMsg403WrongPass
    , errMsg404NoWallet
    , errMsg406
    , errMsg415
    , kanjiWalletName
    , mnemonics12
    , mnemonics15
    , mnemonics18
    , mnemonics21
    , mnemonics24
    , mnemonics9
    , payloadWith
    , polishWalletName
    , russianWalletName
    , simplePayload
    , updateNamePayload
    , updatePassPayload
    , wildcardsWalletName
    )

import qualified Cardano.Wallet.Api.Link as Link
import qualified Data.List.NonEmpty as NE
import qualified Data.Text as T
import qualified Network.HTTP.Types.Status as HTTP


spec :: forall t n. (n ~ 'Testnet) => SpecWith (Context t)
spec = do
    it "WALLETS_CREATE_01 - Create a wallet" $ \ctx -> do
        let payload = Json [json| {
                "name": "1st Wallet",
                "mnemonic_sentence": #{mnemonics15},
                "mnemonic_second_factor": #{mnemonics12},
                "passphrase": "Secure Passphrase",
                "address_pool_gap": 30
                } |]
        r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
        verify r
            [ expectResponseCode @IO HTTP.status201
            , expectField
                    (#name . #getApiT . #getWalletName) (`shouldBe` "1st Wallet")
            , expectField
                    (#addressPoolGap . #getApiT . #getAddressPoolGap) (`shouldBe` 30)
            , expectField (#balance . #getApiT . #available) (`shouldBe` Quantity 0)
            , expectField (#balance . #getApiT . #total) (`shouldBe` Quantity 0)
            , expectField (#balance . #getApiT . #reward) (`shouldBe` Quantity 0)

            , expectField #delegation (`shouldBe` notDelegating [])
            , expectField
                    walletId (`shouldBe` "2cf060fe53e4e0593f145f22b858dfc60676d4ab")
            , expectField #passphrase (`shouldNotBe` Nothing)
            ]
        let wid = getFromResponse id r
        eventually "Wallet state = Ready" $ do
            rg <- request @ApiWallet ctx
                (Link.getWallet @'Shelley wid) Default Empty
            expectField (#state . #getApiT) (`shouldBe` Ready) rg

    describe "OWASP_INJECTION_CREATE_WALLET_01 - \
             \SQL injection when creating a wallet" $  do
        let mnemonics =
                [ "pulp", "ten", "light", "rhythm", "replace"
                , "vessel", "slow", "drift", "kingdom", "amazing"
                , "negative", "join", "auction", "ugly", "symptom"] :: [Text]
        let matrix =
                [ ( "new wallet\",'',''); DROP TABLE \"wallet\"; --"
                  , "new wallet\",'',''); DROP TABLE \"wallet\"; --"
                  )
                , ( "new wallet','ŚεℒℇℂƮ’','ŚεℒℇℂƮ’'); DROP TABLE \"wallet\"; --"
                  , "new wallet','\346\949\8466\8455\8450\430\8217',\
                    \'\346\949\8466\8455\8450\430\8217'); DROP TABLE \"wallet\"; --"
                  ) ]
        forM_ matrix $ \(nameIn, nameOut) -> it nameIn $ \ctx -> do
            let payload = Json [json| {
                    "name": #{nameIn},
                    "mnemonic_sentence": #{mnemonics},
                    "passphrase": "12345678910"
                    } |]
            let postWallet = Link.postWallet @'Shelley
            r <- request @ApiWallet ctx postWallet Default payload
            verify r
                [ expectResponseCode @IO HTTP.status201
                , expectField
                    (#name . #getApiT . #getWalletName) (`shouldBe` nameOut)
                , expectField
                    (#addressPoolGap . #getApiT . #getAddressPoolGap) (`shouldBe` 20)
                , expectField
                    (#balance . #getApiT . #available) (`shouldBe` Quantity 0)
                , expectField
                    (#balance . #getApiT . #total) (`shouldBe` Quantity 0)
                , expectField
                    (#balance . #getApiT . #reward) (`shouldBe` Quantity 0)
                , expectField #delegation (`shouldBe` notDelegating [])
                , expectField walletId
                    (`shouldBe` "135bfb99b9f7a0c702bf8c658cc0d9b1a0d797a2")
                , expectField #passphrase (`shouldNotBe` Nothing)
                ]
            let listWallets = Link.listWallets @'Shelley
            eventually "listed wallet's state = Ready" $ do
                rl <- request @[ApiWallet] ctx listWallets Default Empty
                verify rl
                    [ expectResponseCode @IO HTTP.status200
                    , expectListSize 1
                    , expectListField 0 (#state . #getApiT) (`shouldBe` Ready)
                    ]

    it "WALLETS_CREATE_02 - Restored wallet preserves funds" $ \ctx -> do
        wSrc <- fixtureWallet ctx
        -- create wallet
        mnemonics <- mnemonicToText @15 . entropyToMnemonic <$> genEntropy
        let payldCrt = payloadWith "!st created" mnemonics
        rInit <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payldCrt
        verify rInit
            [ expectResponseCode @IO HTTP.status201
            , expectField (#balance . #getApiT . #available) (`shouldBe` Quantity 0)
            , expectField (#balance . #getApiT . #total) (`shouldBe` Quantity 0)
            ]

        --send funds
        let wDest = getFromResponse id rInit
        addrs <- listAddresses ctx wDest
        let destination = (addrs !! 1) ^. #id
        let payload = Json [json|{
                "payments": [{
                    "address": #{destination},
                    "amount": {
                        "quantity": 1,
                        "unit": "lovelace"
                    }
                }],
                "passphrase": "cardano-wallet"
            }|]
        rTrans <- request @(ApiTransaction n) ctx (Link.createTransaction wSrc)
            Default payload
        expectResponseCode @IO HTTP.status202 rTrans

        eventually "Wallet balance is as expected" $ do
            rGet <- request @ApiWallet ctx
                (Link.getWallet @'Shelley wDest) Default Empty
            verify rGet
                [ expectField
                        (#balance . #getApiT . #total) (`shouldBe` Quantity 1)
                , expectField
                        (#balance . #getApiT . #available) (`shouldBe` Quantity 1)
                ]

        -- delete wallet
        rDel <- request @ApiWallet ctx (Link.deleteWallet @'Shelley wDest) Default Empty
        expectResponseCode @IO HTTP.status204 rDel

        -- restore and make sure funds are there
        rRestore <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payldCrt
        expectResponseCode @IO HTTP.status201 rRestore
        eventually "Wallet balance is ok on restored wallet" $ do
            rGet <- request @ApiWallet ctx
                (Link.getWallet @'Shelley wDest) Default Empty
            verify rGet
                [ expectField
                        (#balance . #getApiT . #total) (`shouldBe` Quantity 1)
                , expectField
                        (#balance . #getApiT . #available) (`shouldBe` Quantity 1)
                ]

    it "WALLETS_CREATE_03,09 - Cannot create wallet that exists" $ \ctx -> do
        let payload = Json [json| {
                "name": "Some Wallet",
                "mnemonic_sentence": #{mnemonics21},
                "passphrase": "Secure Passphrase"
                } |]
        r1 <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
        expectResponseCode @IO HTTP.status201 r1

        r2 <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
        verify r2
            [ expectResponseCode @IO HTTP.status409
            , expectErrorMessage ("This operation would yield a wallet with the\
                \ following id: " ++ T.unpack (getFromResponse walletId r1) ++
                " However, I already know of a wallet with this id.")
            ]

    describe "WALLETS_CREATE_04 - Wallet name" $ do
        let walNameMax = T.pack (replicate walletNameMaxLength 'ą')
        let matrix =
                [ ( show walletNameMinLength ++ " char long", "1"
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField
                            (#name . #getApiT . #getWalletName) (`shouldBe` "1")
                    ]
                  )
                , ( show walletNameMaxLength ++ " char long", walNameMax
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField
                            (#name . #getApiT . #getWalletName) (`shouldBe` walNameMax)
                    ]
                  )
                , ( "Russian name", russianWalletName
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` russianWalletName)
                    ]
                  )
                , ( "Polish name", polishWalletName
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` polishWalletName)
                    ]
                  )
                , ( "Kanji name", kanjiWalletName
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` kanjiWalletName)
                    ]
                  )
                , ( "Arabic name", arabicWalletName
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` arabicWalletName)
                    ]
                  )
                , ( "Wildcards name", wildcardsWalletName
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` wildcardsWalletName)
                    ]
                  )
                ]
        forM_ matrix $ \(title, walName, expectations) -> it title $ \ctx -> do
            let payload = Json [json| {
                    "name": #{walName},
                    "mnemonic_sentence": #{mnemonics24},
                    "passphrase": "Secure Passphrase"
                    } |]
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
            verify r expectations

    describe "WALLETS_CREATE_05 - Mnemonics" $ do
        let matrix =
             [ ( "15 mnemonic words", mnemonics15
               , [ expectResponseCode @IO HTTP.status201
                 , expectField walletId
                    (`shouldBe` "b062e8ccf3685549b6c489a4e94966bc4695b75b")
                 ]
               )
             , ( "18 mnemonic words", mnemonics18
               , [ expectResponseCode @IO HTTP.status201
                 , expectField walletId
                    (`shouldBe` "f52ee0daaefd75a0212d70c9fbe15ee8ada9fc11")
                 ]
               )
             , ( "21 mnemonic words" , mnemonics21
               , [ expectResponseCode @IO HTTP.status201
                 , expectField walletId
                    (`shouldBe` "7e8c1af5ff2218f388a313f9c70f0ff0550277e4")
                 ]
               )
             , ( "24 mnemonic words", mnemonics24
               , [ expectResponseCode @IO HTTP.status201
                 , expectField walletId
                    (`shouldBe` "a6b6625cd2bfc51a296b0933f77020991cc80374")
                 ]
               )
             ]

        forM_ matrix $ \(title, mnemonics, expectations) -> it title $ \ctx -> do
            let payload = Json [json| {
                    "name": "Just a łallet",
                    "mnemonic_sentence": #{mnemonics},
                    "passphrase": "Secure Passphrase"
                    } |]
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
            verify r expectations

    describe "WALLETS_CREATE_06 - Mnemonics second factor" $ do
        let matrix =
                 [ ( "9 mnemonic words", mnemonics9
                   , [ expectResponseCode @IO HTTP.status201
                     , expectField walletId
                        (`shouldBe` "4b1a865e39d1006efb99f538b05ea2343b567108")
                     ]
                   )
                 , ( "12 mnemonic words", mnemonics12
                   , [ expectResponseCode @IO HTTP.status201
                     , expectField walletId
                        (`shouldBe` "2cf060fe53e4e0593f145f22b858dfc60676d4ab")
                     ]
                   )
                 ]
        forM_ matrix $ \(title, mnemonics, expectations) -> it title $ \ctx -> do
            let payload = Json [json| {
                    "name": "Just a łallet",
                    "mnemonic_sentence": #{mnemonics15},
                    "mnemonic_second_factor": #{mnemonics},
                    "passphrase": "Secure Passphrase"
                    } |]
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
            verify r expectations

    describe "WALLETS_CREATE_07 - Passphrase" $ do
        let minLength = passphraseMinLength (Proxy @"encryption")
        let maxLength = passphraseMaxLength (Proxy @"encryption")
        let matrix =
                [ ( show minLength ++ " char long"
                  , T.pack (replicate minLength 'ź')
                  , [ expectResponseCode @IO HTTP.status201
                    ]
                  )
                , ( show maxLength ++ " char long"
                , T.pack (replicate maxLength 'ą')
                  , [ expectResponseCode @IO HTTP.status201 ]
                  )
                , ( "Russian passphrase", russianWalletName
                  , [ expectResponseCode @IO HTTP.status201 ]
                  )
                , ( "Polish passphrase", polishWalletName
                  , [ expectResponseCode @IO HTTP.status201 ]
                  )
                , ( "Kanji passphrase", kanjiWalletName
                  , [ expectResponseCode @IO HTTP.status201 ]
                  )
                , ( "Arabic passphrase", arabicWalletName
                  , [ expectResponseCode @IO HTTP.status201 ]
                  )
                , ( "Wildcards passphrase", wildcardsWalletName
                  , [ expectResponseCode @IO HTTP.status201 ]
                  )
                ]
        forM_ matrix $ \(title, passphrase, expectations) -> it title $ \ctx -> do
            let payload = Json [json| {
                    "name": "Secure Wallet",
                    "mnemonic_sentence": #{mnemonics24},
                    "passphrase": #{passphrase}
                    } |]
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
            verify r expectations

    describe "WALLETS_CREATE_08 - address_pool_gap" $ do
        let addrPoolMin = fromIntegral @_ @Int $ getAddressPoolGap minBound
        let addrPoolMax = fromIntegral @_ @Int $ getAddressPoolGap maxBound
        let matrix =
                [ ( show addrPoolMin
                  , addrPoolMin
                  , [ expectResponseCode @IO HTTP.status201
                    , expectField (#addressPoolGap . #getApiT) (`shouldBe` minBound)
                    ]
                  )
                , ( show addrPoolMax
                  , addrPoolMax
                  , [ expectResponseCode @IO HTTP.status201 ]
                  )
                ]
        forM_ matrix $ \(title, addrPoolGap, expectations) -> it title $ \ctx -> do
            let payload = Json [json| {
                    "name": "Secure Wallet",
                    "mnemonic_sentence": #{mnemonics24},
                    "passphrase": "Secure passphrase",
                    "address_pool_gap": #{addrPoolGap}
                    } |]
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
            verify r expectations

    it "WALLETS_CREATE_08 - default address_pool_gap" $ \ctx -> do
        let payload = Json [json| {
                "name": "Secure Wallet",
                "mnemonic_sentence": #{mnemonics21},
                "passphrase": "Secure passphrase"
                } |]
        r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
        verify r
            [ expectResponseCode @IO HTTP.status201
            , expectField
                    (#addressPoolGap . #getApiT . #getAddressPoolGap) (`shouldBe` 20)
            ]

    describe "WALLETS_CREATE_09 - HTTP headers" $ do
        let matrix =
                 [ ( "No HTTP headers -> 415", None
                   , [ expectResponseCode @IO HTTP.status415
                     , expectErrorMessage errMsg415 ]
                   )
                 , ( "Accept: text/plain -> 406"
                   , Headers
                         [ ("Content-Type", "application/json")
                         , ("Accept", "text/plain") ]
                   , [ expectResponseCode @IO HTTP.status406
                     , expectErrorMessage errMsg406 ]
                   )
                 , ( "No Accept -> 201"
                   , Headers [ ("Content-Type", "application/json") ]
                   , [ expectResponseCode @IO HTTP.status201 ]
                   )
                 , ( "No Content-Type -> 415"
                   , Headers [ ("Accept", "application/json") ]
                   , [ expectResponseCode @IO HTTP.status415
                     , expectErrorMessage errMsg415 ]
                   )
                 , ( "Content-Type: text/plain -> 415"
                   , Headers [ ("Content-Type", "text/plain") ]
                   , [ expectResponseCode @IO HTTP.status415
                     , expectErrorMessage errMsg415 ]
                   )
                 ]
        forM_ matrix $ \(title, headers, expectations) -> it title $ \ctx -> do
            let payload = Json [json| {
                    "name": "Secure Wallet",
                    "mnemonic_sentence": #{mnemonics21},
                    "passphrase": "Secure passphrase"
                    } |]
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) headers payload
            verify r expectations

    -- TODO
    -- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
    --
    -- describe "WALLETS_CREATE_09 - Bad request" $ do
    --     let matrix =
    --             [ ( "empty payload", NonJson "" )
    --             , ( "{} payload", NonJson "{}" )
    --             , ( "non-json valid payload"
    --               , NonJson
    --                     "{name: wallet,\
    --                     \ mnemonic_sentence: [pill, hand, ask, useless, asset,\
    --                     \ rely, above, pipe, embark, game, elder, unaware,\
    --                     \ nasty, coach, glad],\
    --                     \ passphrase: 1234567890}"
    --               )
    --             ]

    --     forM_ matrix $ \(name, nonJson) -> it name $ \ctx -> do
    --         let payload = nonJson
    --         r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload
    --         expectResponseCode @IO HTTP.status400 r

    -- it "WALLETS_CREATE_10 - Invalid JSON" $ \ctx -> do
    --     -- This test case is designed to check that we can handle the case where
    --     -- the payload of an API call triggers a JSON parsing error. We want to
    --     -- check that we can produce an appropriate error message.
    --     --
    --     -- We could go to the trouble of testing with many kinds of broken JSON
    --     -- across multiple different endpoints, but for now we simply test one
    --     -- representative endpoint with one simple broken JSON string.
    --     --
    --     -- TODO: Later on, we can generalize this, if necessary.
    --     --
    --     let payloadBad = NonJson "}"
    --     r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default payloadBad
    --     expectResponseCode @IO HTTP.status400 r
    --     expectErrorMessage errMsg400ParseError r

    it "WALLETS_GET_01 - can get wallet details" $ \ctx -> do
        (_, w) <- unsafeRequest @ApiWallet ctx (Link.postWallet @'Shelley) simplePayload

        eventually "I can get all wallet details" $ do
            rg <- request @ApiWallet ctx (Link.getWallet @'Shelley w) Default Empty
            verify rg
                [ expectResponseCode @IO HTTP.status200
                , expectField
                        (#name . #getApiT . #getWalletName) (`shouldBe` "Secure Wallet")
                , expectField
                        (#addressPoolGap . #getApiT . #getAddressPoolGap) (`shouldBe` 20)
                , expectField
                        (#balance . #getApiT . #available) (`shouldBe` Quantity 0)
                , expectField
                        (#balance . #getApiT . #total) (`shouldBe` Quantity 0)
                , expectField
                        (#balance . #getApiT . #reward) (`shouldBe` Quantity 0)
                , expectField (#state . #getApiT) (`shouldBe` Ready)
                , expectField #delegation (`shouldBe` notDelegating [])
                , expectField walletId (`shouldBe` w ^. walletId)
                , expectField #passphrase (`shouldNotBe` Nothing)
                ]

    it "WALLETS_GET_02, WALLETS_DELETE_01 - Deleted wallet is not available" $ \ctx -> do
        w <- emptyWallet ctx
        _ <- request @ApiWallet ctx
            (Link.deleteWallet @'Shelley w) Default Empty
        rg <- request @ApiWallet ctx
            (Link.getWallet @'Shelley w) Default Empty
        expectResponseCode @IO HTTP.status404 rg
        expectErrorMessage (errMsg404NoWallet $ w ^. walletId) rg

    it "WALLETS_LIST_01 - Created a wallet can be listed" $ \ctx -> do
        let payload = Json [json| {
                "name": "Wallet to be listed",
                "mnemonic_sentence": #{mnemonics18},
                "mnemonic_second_factor": #{mnemonics9},
                "passphrase": "Secure Passphrase",
                "address_pool_gap": 20
                } |]
        _ <- unsafeRequest @ApiWallet ctx (Link.postWallet @'Shelley) payload
        rl <- request @[ApiWallet] ctx (Link.listWallets @'Shelley) Default Empty
        verify rl
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 1
            , expectListField 0
                    (#name . #getApiT . #getWalletName)
                    (`shouldBe` "Wallet to be listed")
            , expectListField 0
                    (#addressPoolGap . #getApiT . #getAddressPoolGap) (`shouldBe` 20)
            , expectListField 0
                    (#balance . #getApiT . #available) (`shouldBe` Quantity 0)
            , expectListField 0
                    (#balance . #getApiT . #total) (`shouldBe` Quantity 0)
            , expectListField 0
                    (#balance . #getApiT . #reward) (`shouldBe` Quantity 0)
            , expectListField 0 #delegation (`shouldBe` notDelegating [])
            , expectListField 0 walletId
                    (`shouldBe` "dfe87fcf0560fb57937a6468ea51e860672fad79")
            ]

    it "WALLETS_LIST_01 - Wallets are listed from oldest to newest" $ \ctx -> do
        let walletDetails = [("1", mnemonics15), ("2", mnemonics18)
                    , ("3", mnemonics21)]
        forM_ walletDetails $ \(name, mnemonics) -> do
            let payload = payloadWith name mnemonics
            request @ApiWallet ctx (Link.postWallet @'Shelley) Default payload

        rl <- request @[ApiWallet] ctx (Link.listWallets @'Shelley) Default Empty
        verify rl
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 3
            , expectListField 0
                (#name . #getApiT . #getWalletName) (`shouldBe` "1")
            , expectListField 1
                (#name . #getApiT . #getWalletName) (`shouldBe` "2")
            , expectListField 2
                (#name . #getApiT . #getWalletName) (`shouldBe` "3")
            ]

    it "WALLETS_LIST_02 - Deleted wallet not listed" $ \ctx -> do
        w <- emptyWallet ctx
        _ <- request @ApiWallet ctx (Link.deleteWallet @'Shelley w) Default Empty
        rl <- request @[ApiWallet] ctx (Link.listWallets @'Shelley) Default Empty
        verify rl
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 0
            ]

    it "WALLETS_UPDATE_01 - Updated wallet name is available" $ \ctx -> do

        r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
        let passLastUpdateValue = getFromResponse #passphrase r
        let newName = updateNamePayload "New great name"
        let walId = getFromResponse walletId r
        let expectations = [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` "New great name")
                    , expectField
                            (#addressPoolGap . #getApiT . #getAddressPoolGap)
                            (`shouldBe` 20)
                    , expectField
                            (#balance . #getApiT . #available) (`shouldBe` Quantity 0)
                    , expectField
                            (#balance . #getApiT . #total) (`shouldBe` Quantity 0)
                    , expectField (#state . #getApiT) (`shouldBe` Ready)
                    , expectField #delegation (`shouldBe` notDelegating [])
                    , expectField walletId (`shouldBe` walId)
                    , expectField #passphrase (`shouldBe` passLastUpdateValue)
                    ]
        eventually "Updated wallet name is available" $ do
            ru <- request @ApiWallet ctx
                ("PUT", "v2/wallets" </> walId) Default newName
            verify ru expectations
            rg <- request @ApiWallet ctx
                ("GET", "v2/wallets" </> walId) Default Empty
            verify rg expectations
            rl <- request @[ApiWallet] ctx ("GET", "v2/wallets") Default Empty
            verify rl
                [ expectResponseCode @IO HTTP.status200
                , expectListSize 1
                , expectListField 0
                        (#name . #getApiT . #getWalletName) (`shouldBe` "New great name")
                , expectListField 0
                        (#addressPoolGap . #getApiT . #getAddressPoolGap) (`shouldBe` 20)
                , expectListField 0
                        (#balance . #getApiT . #available) (`shouldBe` Quantity 0)
                , expectListField 0
                        (#balance . #getApiT . #total) (`shouldBe` Quantity 0)
                , expectListField 0 (#state . #getApiT) (`shouldBe` Ready)
                , expectListField 0 #delegation (`shouldBe` notDelegating [])
                , expectListField 0 walletId (`shouldBe` walId)
                , expectListField 0 #passphrase (`shouldBe` passLastUpdateValue)
                ]

    describe "WALLETS_UPDATE_02 - Various names" $ do
        let walNameMax = T.pack (replicate walletNameMaxLength 'ą')
        let matrix =
                [ ( show walletNameMinLength ++ " char long", "1"
                  , [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName) (`shouldBe` "1")
                    ]
                  )
                , ( show walletNameMaxLength ++ " char long", walNameMax
                  , [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName) (`shouldBe` walNameMax)
                    ]
                  )
                , ( "Russian name", russianWalletName
                  , [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` russianWalletName)
                    ]
                  )
                , ( "Polish name", polishWalletName
                  , [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` polishWalletName)
                    ]
                  )
                , ( "Kanji name", kanjiWalletName
                  , [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` kanjiWalletName)
                    ]
                  )
                , ( "Arabic name", arabicWalletName
                  , [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` arabicWalletName)
                    ]
                  )
                , ( "Wildcards name", wildcardsWalletName
                  , [ expectResponseCode @IO HTTP.status200
                    , expectField
                            (#name . #getApiT . #getWalletName)
                            (`shouldBe` wildcardsWalletName)
                    ]
                  )
                ]
        forM_ matrix $ \(title, walName, expectations) -> it title $ \ctx -> do
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
            let newName = updateNamePayload walName
            let endpoint = "v2/wallets" </> (getFromResponse walletId r)
            ru <- request @ApiWallet ctx ("PUT", endpoint) Default newName
            verify ru expectations

    it "WALLETS_UPDATE_03 - Deleted wallet cannot be updated (404)" $ \ctx -> do
        r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
        let wid = getFromResponse walletId r
        let endpoint = "v2/wallets" </> wid
        _ <- request @ApiWallet ctx ("DELETE", endpoint) Default Empty

        let newName = updateNamePayload "new name"
        ru <- request @ApiWallet ctx ("PUT", endpoint) Default newName
        expectResponseCode @IO HTTP.status404 ru
        expectErrorMessage (errMsg404NoWallet wid) ru

    describe "WALLETS_UPDATE_04 - HTTP headers" $ do
        let matrix =
                  [ ( "No HTTP headers -> 415", None
                    , [ expectResponseCode @IO HTTP.status415
                      , expectErrorMessage errMsg415 ]
                    )
                  , ( "Accept: text/plain -> 406"
                    , Headers
                          [ ("Content-Type", "application/json")
                          , ("Accept", "text/plain") ]
                    , [ expectResponseCode @IO HTTP.status406
                      , expectErrorMessage errMsg406 ]
                    )
                  , ( "No Accept -> 200"
                    , Headers [ ("Content-Type", "application/json") ]
                    , [ expectResponseCode @IO HTTP.status200 ]
                    )
                  , ( "No Content-Type -> 415"
                    , Headers [ ("Accept", "application/json") ]
                    , [ expectResponseCode @IO HTTP.status415
                      , expectErrorMessage errMsg415 ]
                    )
                  , ( "Content-Type: text/plain -> 415"
                    , Headers [ ("Content-Type", "text/plain") ]
                    , [ expectResponseCode @IO HTTP.status415
                      , expectErrorMessage errMsg415 ]
                    )
                  ]
        forM_ matrix $ \(title, headers, expectations) -> it title $ \ctx -> do
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
            let newName = updateNamePayload "new name"
            let endpoint = "v2/wallets" </> (getFromResponse walletId r)
            ru <- request @ApiWallet ctx ("PUT", endpoint) headers newName
            verify ru expectations

    it "WALLETS_UPDATE_PASS_01 - passphaseLastUpdate gets updated" $ \ctx -> do
        r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
        let payload = updatePassPayload "Secure passphrase" "New passphrase"
        let endpoint = "v2/wallets" </> (getFromResponse walletId r)
                </> ("passphrase" :: Text)
        rup <- request @ApiWallet ctx ("PUT", endpoint) Default payload
        expectResponseCode @IO HTTP.status204 rup

        let getEndpoint = "v2/wallets" </> (getFromResponse walletId r)
        let originalPassUpdateDateTime = getFromResponse #passphrase r
        rg <- request @ApiWallet ctx ("GET", getEndpoint) Default Empty
        expectField #passphrase (`shouldNotBe` originalPassUpdateDateTime) rg

    describe "WALLETS_UPDATE_PASS_02 - New passphrase values" $ do
        let minLength = passphraseMinLength (Proxy @"encryption")
        let maxLength = passphraseMaxLength (Proxy @"encryption")
        let matrix =
                [ ( show minLength ++ " char long"
                  , T.pack (replicate minLength 'ź')
                  , [ expectResponseCode @IO HTTP.status204
                    ]
                  )
                , ( show maxLength ++ " char long"
                  , T.pack (replicate maxLength 'ą')
                  , [ expectResponseCode @IO HTTP.status204 ]
                  )
                , ( "Russian passphrase", russianWalletName
                  , [ expectResponseCode @IO HTTP.status204 ]
                  )
                , ( "Polish passphrase", polishWalletName
                  , [ expectResponseCode @IO HTTP.status204 ]
                  )
                , ( "Kanji passphrase", kanjiWalletName
                  , [ expectResponseCode @IO HTTP.status204 ]
                  )
                , ( "Arabic passphrase", arabicWalletName
                  , [ expectResponseCode @IO HTTP.status204 ]
                  )
                , ( "Wildcards passphrase", wildcardsWalletName
                  , [ expectResponseCode @IO HTTP.status204 ]
                  )

                -- TODO
                -- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
                --
                -- , ( show (minLength - 1) ++ " char long"
                --   , T.pack (replicate (minLength - 1) 'ż')
                --   , [ expectResponseCode @IO HTTP.status400
                --     , expectErrorMessage "passphrase is too short: expected at\
                --             \ least 10 characters"
                --     ]
                --   )
                -- , ( show (maxLength + 1) ++ " char long"
                --   , T.pack (replicate (maxLength + 1) 'ę')
                --   , [ expectResponseCode @IO HTTP.status400
                --     , expectErrorMessage "passphrase is too long: expected at\
                --             \ most 255 characters"
                --     ]
                --   )
                -- , ( "Empty passphrase", ""
                --    , [ expectResponseCode @IO HTTP.status400
                --      , expectErrorMessage "passphrase is too short: expected at\
                --             \ least 10 characters"
                --      ]
                --   )
                ]
        forM_ matrix $ \(title, passphrase, expectations) -> it title $ \ctx -> do
            r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
            let payload = updatePassPayload "Secure passphrase" passphrase
            let endpoint = "v2/wallets" </> (getFromResponse walletId r)
                    </> ("passphrase" :: Text)
            rup <- request @ApiWallet ctx ("PUT", endpoint) Default payload
            verify rup expectations

    -- TODO
    -- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
    --
    -- describe "WALLETS_UPDATE_PASS_03 - Old passphrase invalid values" $ do
    --     let minLength = passphraseMinLength (Proxy @"encryption")
    --     let maxLength = passphraseMaxLength (Proxy @"encryption")
    --     let matrix =
    --             [ ( show (minLength - 1) ++ " char long"
    --               , T.pack (replicate (minLength - 1) 'ż')
    --               , [ expectResponseCode @IO HTTP.status400
    --                 , expectErrorMessage "passphrase is too short: expected at\
    --                         \ least 10 characters" ]
    --               )
    --             , ( show (maxLength + 1) ++ " char long"
    --               , T.pack (replicate (maxLength + 1) 'ę')
    --               , [ expectResponseCode @IO HTTP.status400
    --                 , expectErrorMessage "passphrase is too long: expected at\
    --                         \ most 255 characters" ]
    --               )
    --             , ( "Empty passphrase", ""
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "passphrase is too short: expected at\
    --                         \ least 10 characters" ]
    --               )
    --             , ( "Incorrect old pass", "Incorrect passphrase"
    --               , [ expectResponseCode @IO HTTP.status403
    --                 , expectErrorMessage errMsg403WrongPass ]
    --               )
    --             ]
    --     forM_ matrix $ \(title, passphrase, expectations) -> it title $ \ctx -> do
    --         r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
    --         let payload = updatePassPayload passphrase "Secure passphrase 2"
    --         let endpoint = "v2/wallets" </> (getFromResponse walletId r)
    --                 </> ("passphrase" :: Text)
    --         rup <- request @ApiWallet ctx ("PUT", endpoint) Default payload
    --         verify rup expectations

    describe "WALLETS_UPDATE_PASS_03 - Can update pass from pass that's boundary\
    \ value" $ do
        let minLength = passphraseMinLength (Proxy @"encryption")
        let maxLength = passphraseMaxLength (Proxy @"encryption")
        let matrix =
                [ ( show minLength ++ " char long"
                  , T.pack (replicate minLength 'ź') )
                , ( show maxLength ++ " char long"
                  , T.pack (replicate maxLength 'ą') )
                , ( "Russian passphrase", russianWalletName )
                , ( "Polish passphrase", polishWalletName )
                , ( "Kanji passphrase", kanjiWalletName )
                , ( "Arabic passphrase", arabicWalletName )
                , ( "Wildcards passphrase", wildcardsWalletName )
                ]
        forM_ matrix $ \(title, oldPass) -> it title $ \ctx -> do
            let createPayload = Json [json| {
                     "name": "Name of the wallet",
                     "mnemonic_sentence": #{mnemonics24},
                     "passphrase": #{oldPass}
                     } |]
            (_, w) <- unsafeRequest @ApiWallet ctx
                (Link.postWallet @'Shelley) createPayload
            let len = passphraseMaxLength (Proxy @"encryption")
            let newPass = T.pack $ replicate len '💘'
            let payload = updatePassPayload oldPass newPass
            rup <- request @ApiWallet ctx
                (Link.putWalletPassphrase w) Default payload
            expectResponseCode @IO HTTP.status204 rup

    -- TODO
    -- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
    --
    -- describe "WALLETS_UPDATE_PASS_02,03 - invalid payloads" $  do
    --     let matrix =
    --             [  ( "[] as new passphrase"
    --                , Json [json| {
    --                     "old_passphrase": "Secure passphrase",
    --                     "new_passphrase": []
    --                       } |]
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "expected Text, encountered Array" ]
    --                )
    --              , ( "[] as old passphrase"
    --                , Json [json| {
    --                    "old_passphrase": [],
    --                    "new_passphrase": "Secure passphrase"
    --                      } |]
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "expected Text, encountered Array" ]
    --                )
    --              , ( "Num as old passphrase"
    --                , Json [json| {
    --                   "old_passphrase": 12345678910,
    --                   "new_passphrase": "Secure passphrase"
    --                      } |]
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "expected Text, encountered Number" ]
    --                )
    --              , ( "Num as new passphrase"
    --                , Json [json| {
    --                   "old_passphrase": "Secure passphrase",
    --                   "new_passphrase": 12345678910
    --                      } |]
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "expected Text, encountered Number" ]
    --                )
    --              , ( "Missing old passphrase"
    --                , Json [json| {
    --                   "new_passphrase": "Secure passphrase"
    --                      } |]
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "key 'old_passphrase' not present" ]
    --                )
    --              , ( "Missing new passphrase"
    --                , Json [json| {
    --                   "old_passphrase": "Secure passphrase"
    --                      } |]
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "key 'new_passphrase' not present" ]
    --               )
    --             ]
    --     forM_ matrix $ \(title, payload, expectations) -> it title $ \ctx -> do
    --         r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
    --         let endpoint = "v2/wallets" </> (getFromResponse walletId r)
    --                 </> ("passphrase" :: Text)
    --         rup <- request @ApiWallet ctx ("PUT", endpoint) Default payload
    --         verify rup expectations

    it "WALLETS_UPDATE_PASS_04 - Deleted wallet is not available" $ \ctx -> do
        r <- request @ApiWallet ctx (Link.postWallet @'Shelley) Default simplePayload
        let payload = updatePassPayload "Secure passphrase" "Secure passphrase2"
        let walId = getFromResponse walletId r
        let delEndp = "v2/wallets" </> walId
        _ <- request @ApiWallet ctx ("DELETE", delEndp) Default Empty
        let updEndp = delEndp </> ("passphrase" :: Text)
        rup <- request @ApiWallet ctx ("PUT", updEndp) Default payload
        expectResponseCode @IO HTTP.status404 rup
        expectErrorMessage (errMsg404NoWallet walId) rup

    describe "WALLETS_UPDATE_PASS_05,06 - Transaction after updating passphrase" $ do
        let oldPass = "cardano-wallet"
        let newPass = "cardano-wallet2"
        let matrix = [ ("Old passphrase -> fail", oldPass
                       , [ expectResponseCode @IO HTTP.status403
                         , expectErrorMessage errMsg403WrongPass ] )
                     , ("New passphrase -> OK", newPass
                       , [ expectResponseCode @IO HTTP.status202 ] )
                     ]

        forM_ matrix $ \(title, pass, expectations) -> it title $ \ctx -> do
            wSrc <- fixtureWallet ctx
            wDest <- emptyWallet ctx
            let payloadUpdate = updatePassPayload oldPass newPass
            rup <- request @ApiWallet ctx (Link.putWalletPassphrase wSrc) Default payloadUpdate
            expectResponseCode @IO HTTP.status204 rup

            addrs <- listAddresses ctx wDest
            let destination = (addrs !! 1) ^. #id
            let payloadTrans = Json [json|{
                    "payments": [{
                        "address": #{destination},
                        "amount": {
                            "quantity": 1,
                            "unit": "lovelace"
                        }
                    }],
                    "passphrase": #{pass}
                    }|]
            r <- request @(ApiTransaction n) ctx (Link.createTransaction wSrc) Default payloadTrans
            verify r expectations

    describe "WALLETS_UPDATE_PASS_07 - HTTP headers" $ do
        let matrix =
                  [ ( "No HTTP headers -> 415", None
                    , [ expectResponseCode @IO HTTP.status415
                      , expectErrorMessage errMsg415 ]
                    )
                  , ( "Accept: text/plain -> 406"
                    , Headers
                          [ ("Content-Type", "application/json")
                          , ("Accept", "text/plain") ]
                    , [ expectResponseCode @IO HTTP.status204 ]
                    )
                  , ( "No Accept -> 204"
                    , Headers [ ("Content-Type", "application/json") ]
                    , [ expectResponseCode @IO HTTP.status204 ]
                    )
                  , ( "No Content-Type -> 415"
                    , Headers [ ("Accept", "application/json") ]
                    , [ expectResponseCode @IO HTTP.status415
                      , expectErrorMessage errMsg415 ]
                    )
                  , ( "Content-Type: text/plain -> 415"
                    , Headers [ ("Content-Type", "text/plain") ]
                    , [ expectResponseCode @IO HTTP.status415
                      , expectErrorMessage errMsg415 ]
                    )
                  ]
        forM_ matrix $ \(title, headers, expectations) -> it title $ \ctx -> do
            (_, w) <- unsafeRequest @ApiWallet ctx (Link.postWallet @'Shelley) simplePayload
            let payload = updatePassPayload "Secure passphrase" "Passphrase"
            let endpoint = Link.putWalletPassphrase w
            rup <- request @ApiWallet ctx endpoint headers payload
            verify rup expectations

    it "WALLETS_COIN_SELECTION_01 - \
        \A singleton payment is included in the coin selection output." $
        \ctx -> do
            source <- fixtureWallet ctx
            target <- emptyWallet ctx
            targetAddress : _ <- fmap (view #id) <$> listAddresses ctx target
            let amount = Quantity 1
            let payment = AddressAmount targetAddress amount
            selectCoins ctx source (payment :| []) >>= flip verify
                [ expectResponseCode HTTP.status200
                , expectField #inputs (`shouldSatisfy` (not . null))
                , expectField #outputs (`shouldSatisfy` ((> 1) . length))
                , expectField #outputs (`shouldSatisfy` (payment `elem`))
                ]

    let satisfy = flip shouldSatisfy
    it "WALLETS_COIN_SELECTION_02 - \
        \Multiple payments are all included in the coin selection output." $
        \ctx -> do
            let paymentCount = 10
            source <- fixtureWallet ctx
            target <- emptyWallet ctx
            targetAddresses <- fmap (view #id) <$> listAddresses ctx target
            let amounts = Quantity <$> [1 ..]
            let payments = NE.fromList
                    $ take paymentCount
                    $ zipWith AddressAmount targetAddresses amounts
            selectCoins ctx source payments >>= flip verify
                [ expectResponseCode
                    HTTP.status200
                , expectField
                    #inputs (`shouldSatisfy` (not . null))
                , expectField
                    #outputs (satisfy $ (> paymentCount) . length)
                , expectField
                    #outputs (satisfy $ flip all payments . flip elem)
                ]

    it "WALLETS_COIN_SELECTION_03 - \
        \Deleted wallet is not available for selection" $ \ctx -> do
        w <- emptyWallet ctx
        (addr:_) <- fmap (view #id) <$> listAddresses ctx w
        let payments = NE.fromList [ AddressAmount addr (Quantity 1) ]
        _ <- request @ApiWallet ctx (Link.deleteWallet @'Shelley w) Default Empty
        selectCoins ctx w payments >>= flip verify
            [ expectResponseCode @IO HTTP.status404
            , expectErrorMessage (errMsg404NoWallet $ w ^. walletId)
            ]

    it "WALLETS_COIN_SELECTION_03 - \
        \Wrong selection method (not 'random')" $ \ctx -> do
        w <- fixtureWallet ctx
        (addr:_) <- fmap (view #id) <$> listAddresses ctx w
        let payments = NE.fromList [ AddressAmount addr (Quantity 1) ]
        let payload = Json [json| { "payments": #{payments} } |]
        let wid = toText $ getApiT $ w ^. #id
        let endpoints = ("POST",) . mconcat <$>
                [ [ "v2/wallets/", wid, "/coin-selections/largest-first" ]
                , [ "v2/wallets/", wid, "/coin-selections" ]
                ]
        forM_ endpoints $ \endpoint -> do
            r <- request @(ApiCoinSelection n) ctx endpoint Default payload
            verify r [ expectResponseCode @IO HTTP.status404 ]

    describe "WALLETS_COIN_SELECTION_04 - HTTP headers" $ do
        let matrix =
                [ ( "No HTTP headers -> 415"
                  , None
                  , [ expectResponseCode @IO HTTP.status415
                    , expectErrorMessage errMsg415
                    ]
                  )
                , ( "Accept: text/plain -> 406"
                  , Headers
                        [ ("Content-Type", "application/json")
                        , ("Accept", "text/plain")
                        ]
                  , [ expectResponseCode @IO HTTP.status406
                    , expectErrorMessage errMsg406
                    ]
                  )
                , ( "No Accept -> 200"
                  , Headers [ ("Content-Type", "application/json") ]
                  , [ expectResponseCode @IO HTTP.status200 ]
                  )
                , ( "No Content-Type -> 415"
                  , Headers [ ("Accept", "application/json") ]
                  , [ expectResponseCode @IO HTTP.status415
                    , expectErrorMessage errMsg415
                    ]
                  )
                , ( "Content-Type: text/plain -> 415"
                  , Headers [ ("Content-Type", "text/plain") ]
                  , [ expectResponseCode @IO HTTP.status415
                    , expectErrorMessage errMsg415
                    ]
                  )
                ]
        forM_ matrix $ \(title, headers, expectations) -> it title $ \ctx -> do
            w <- fixtureWallet ctx
            (addr:_) <- fmap (view #id) <$> listAddresses ctx w
            let payments = NE.fromList [ AddressAmount addr (Quantity 1) ]
            let payload = Json [json| { "payments": #{payments} } |]
            r <- request @(ApiCoinSelection n) ctx (Link.selectCoins w) headers payload
            verify r expectations

    it "WALLETS_UTXO_01 - Wallet's inactivity is reflected in utxo" $ \ctx -> do
        w <- emptyWallet ctx
        rStat <- request @ApiUtxoStatistics ctx (Link.getUTxOsStatistics w) Default Empty
        expectResponseCode @IO HTTP.status200 rStat
        expectWalletUTxO [] (snd rStat)

    it "WALLETS_UTXO_02 - Sending and receiving funds updates wallet's utxo." $ \ctx -> do
        wSrc <- fixtureWallet ctx
        wDest <- emptyWallet ctx

        --send funds
        addrs <- listAddresses ctx wDest
        let destination = (addrs !! 1) ^. #id
        let coins = [13::Natural, 43, 66, 101, 1339]
        let matrix = zip coins [1..]
        forM_ matrix $ \(c, alreadyAbsorbed) -> do
            let payload = Json [json|{
                    "payments": [{
                        "address": #{destination},
                        "amount": {
                            "quantity": #{c},
                            "unit": "lovelace"
                        }
                    }],
                    "passphrase": "cardano-wallet"
                }|]
            rTrans <- request @(ApiTransaction n) ctx (Link.createTransaction wSrc)
                Default payload
            expectResponseCode @IO HTTP.status202 rTrans

            let coinsSent = map fromIntegral $ take alreadyAbsorbed coins
            eventually "Wallet balance is as expected" $ do
                rGet <- request @ApiWallet ctx
                    (Link.getWallet @'Shelley wDest) Default Empty
                verify rGet
                    [ expectField
                            (#balance . #getApiT . #total)
                            (`shouldBe` Quantity (fromIntegral $ sum coinsSent))
                    , expectField
                            (#balance . #getApiT . #available)
                            (`shouldBe` Quantity (fromIntegral $ sum coinsSent))
                    ]

            --verify utxo
            rStat1 <- request @ApiUtxoStatistics ctx
                (Link.getUTxOsStatistics wDest) Default Empty
            expectResponseCode @IO HTTP.status200 rStat1
            expectWalletUTxO coinsSent (snd rStat1)

    it "WALLETS_UTXO_03 - Deleted wallet is not available for utxo" $ \ctx -> do
        w <- emptyWallet ctx
        _ <- request @ApiWallet ctx (Link.deleteWallet @'Shelley w)
            Default Empty
        r <- request @ApiUtxoStatistics ctx (Link.getUTxOsStatistics w)
            Default Empty
        expectResponseCode @IO HTTP.status404 r
        expectErrorMessage (errMsg404NoWallet $ w ^. walletId) r

    describe "WALLETS_UTXO_04 - HTTP headers" $ do
        let matrix =
                [ ( "No HTTP headers -> 200"
                  , None
                  , [ expectResponseCode @IO HTTP.status200 ] )
                , ( "Accept: text/plain -> 406"
                  , Headers
                        [ ("Content-Type", "application/json")
                        , ("Accept", "text/plain") ]
                  , [ expectResponseCode @IO HTTP.status406
                    , expectErrorMessage errMsg406 ]
                  )
                , ( "No Accept -> 200"
                  , Headers [ ("Content-Type", "application/json") ]
                  , [ expectResponseCode @IO HTTP.status200 ]
                  )
                , ( "No Content-Type -> 200"
                  , Headers [ ("Accept", "application/json") ]
                  , [ expectResponseCode @IO HTTP.status200 ]
                  )
                , ( "Content-Type: text/plain -> 200"
                  , Headers [ ("Content-Type", "text/plain") ]
                  , [ expectResponseCode @IO HTTP.status200 ]
                  )
                ]
        forM_ matrix $ \(title, headers, expectations) -> it title $ \ctx -> do
            w <- emptyWallet ctx
            r <- request @ApiUtxoStatistics ctx (Link.getUTxOsStatistics w) headers Empty
            verify r expectations

    it "BYRON_WALLETS_UTXO -\
        \ Cannot show Byron wal utxo with shelley ep (404)" $ \ctx -> do
        w <- emptyRandomWallet ctx
        let wid = w ^. walletId
        let endpoint =
                    "v2/wallets"
                    </> wid
                    </> ("statistics/utxos" :: Text)
        r <- request @ApiUtxoStatistics ctx ("GET", endpoint) Default Empty
        expectResponseCode @IO HTTP.status404 r
        expectErrorMessage (errMsg404NoWallet wid) r

    it "BYRON_WALLETS_UPDATE_PASS -\
        \ Cannot update Byron wal with shelley ep (404)" $ \ctx -> do
        w <- emptyRandomWallet ctx
        let payload = updatePassPayload "Secure passphrase" "Secure passphrase2"
        let wid = w ^. walletId
        let endpoint =
                "v2/wallets"
                </> wid
                </> ("passphrase" :: Text)
        rup <- request @ApiWallet ctx ("PUT", endpoint) Default payload
        expectResponseCode @IO HTTP.status404 rup
        expectErrorMessage (errMsg404NoWallet wid) rup

    it "BYRON_WALLETS_UPDATE -\
        \ Cannot update Byron wal with shelley ep (404)" $ \ctx -> do
        w <- emptyRandomWallet ctx
        let wid = w ^. walletId
        let endpoint = "v2/wallets" </> wid
        let newName = updateNamePayload "new name"
        ru <- request @ApiWallet ctx ("PUT", endpoint) Default newName
        expectResponseCode @IO HTTP.status404 ru
        expectErrorMessage (errMsg404NoWallet wid) ru

    describe "WALLETS_RESYNC_01" $ do
        scenarioWalletResync01_happyPath @'Shelley emptyWallet
        scenarioWalletResync01_happyPath @'Byron emptyRandomWallet
        scenarioWalletResync01_happyPath @'Byron emptyIcarusWallet

    describe "WALLETS_RESYNC_02" $ do
        scenarioWalletResync02_notGenesis @'Shelley emptyWallet
        scenarioWalletResync02_notGenesis @'Byron emptyRandomWallet
        scenarioWalletResync02_notGenesis @'Byron emptyIcarusWallet

    -- TODO
    -- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
    --
    -- describe "WALLETS_RESYNC_03" $ do
    --     scenarioWalletResync03_invalidPayload @'Shelley emptyWallet
    --     scenarioWalletResync03_invalidPayload @'Byron emptyRandomWallet
    --     scenarioWalletResync03_invalidPayload @'Byron emptyIcarusWallet

-- force resync eventually get us back to the same point
scenarioWalletResync01_happyPath
    :: forall style t n wallet.
        ( n ~ 'Testnet
        , Discriminate style
        , HasType (ApiT WalletId) wallet
        , HasField' "state" wallet (ApiT SyncProgress)
        , FromJSON wallet
        , Generic wallet
        , Show wallet
        )
    => (Context t -> IO wallet)
    -> SpecWith (Context t)
scenarioWalletResync01_happyPath fixture = it
  "force resync eventually get us back to the same point" $ \ctx -> do
    w <- fixture ctx

    -- 1. Wait for wallet to be synced
    eventually "Wallet is synced" $ do
        v <- request @wallet ctx (Link.getWallet @style w) Default Empty
        verify v [ expectField @IO #state (`shouldBe` (ApiT Ready)) ]

    -- 2. Force a resync
    let payload = Json [json|{ "epoch_number": 0, "slot_number": 0 }|]
    r <- request @wallet ctx (Link.forceResyncWallet @style w) Default payload
    verify r [ expectResponseCode @IO HTTP.status204 ]

    -- 3. The wallet eventually re-sync
    eventually "Wallet re-syncs successfully" $ do
        v <- request @wallet ctx (Link.getWallet @style w) Default Empty
        verify v [ expectField @IO #state (`shouldBe` (ApiT Ready)) ]

-- force resync eventually get us back to the same point
scenarioWalletResync02_notGenesis
    :: forall style t n wallet.
        ( n ~ 'Testnet
        , Discriminate style
        , HasType (ApiT WalletId) wallet
        , HasField' "state" wallet (ApiT SyncProgress)
        , FromJSON wallet
        , Generic wallet
        , Show wallet
        )
    => (Context t -> IO wallet)
    -> SpecWith (Context t)
scenarioWalletResync02_notGenesis fixture = it
  "given point is not genesis (i.e. (0, 0))" $ \ctx -> do
    w <- fixture ctx

    -- 1. Force a resync on an invalid point (/= from genesis)
    let payload = Json [json|{ "epoch_number": 14, "slot_number": 42 }|]
    r <- request @wallet ctx (Link.forceResyncWallet @style w) Default payload
    verify r
        [ expectResponseCode @IO HTTP.status403
        , expectErrorMessage errMsg403RejectedTip
        ]

-- TODO
-- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
--
-- -- force resync eventually get us back to the same point
-- scenarioWalletResync03_invalidPayload
--     :: forall style t n wallet.
--         ( n ~ 'Testnet
--         , Discriminate style
--         , HasType (ApiT WalletId) wallet
--         , HasField' "state" wallet (ApiT SyncProgress)
--         , FromJSON wallet
--         , Generic wallet
--         , Show wallet
--         )
--     => (Context t -> IO wallet)
--     -> SpecWith (Context t)
-- scenarioWalletResync03_invalidPayload fixture = it
--   "given payload is invalid (camelCase)" $ \ctx -> do
--     w <- fixture ctx
--
--     -- 1. Force a resync using an invalid payload
--     let payload = Json [json|{ "epochNumber": 0, "slot_number": 0 }|]
--     r <- request @wallet ctx (Link.forceResyncWallet @style w) Default payload
--     verify r
--         [ expectResponseCode @IO HTTP.status400
--         , expectErrorMessage "key 'epoch_number' not present"
--         ]
