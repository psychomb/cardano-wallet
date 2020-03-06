{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Integration.Scenario.API.ByronWallets
    ( spec
    ) where

import Prelude

import Cardano.Wallet.Api.Types
    ( ApiByronWallet, ApiByronWalletMigrationInfo (..), WalletStyle (..) )
import Cardano.Wallet.Primitive.AddressDerivation
    ( NetworkDiscriminant (..)
    , PassphraseMaxLength (..)
    , PassphraseMinLength (..)
    )
import Cardano.Wallet.Primitive.Mnemonic
    ( ConsistentEntropy
    , EntropySize
    , MnemonicWords
    , ValidChecksumSize
    , ValidEntropySize
    , entropyToMnemonic
    , genEntropy
    , mnemonicToText
    )
import Cardano.Wallet.Primitive.Types
    ( SyncProgress (..) )
import Control.Monad
    ( forM_, void )
import Data.Generics.Internal.VL.Lens
    ( (^.) )
import Data.Proxy
    ( Proxy (..) )
import Data.Quantity
    ( Quantity (..) )
import Data.Text
    ( Text )
import Test.Hspec
    ( SpecWith, describe, it, runIO, shouldNotBe )
import Test.Hspec.Expectations.Lifted
    ( shouldBe )
import Test.Integration.Framework.DSL
    ( Context (..)
    , Headers (..)
    , Payload (..)
    , emptyByronWalletWith
    , emptyIcarusWallet
    , emptyRandomWallet
    , eventually
    , expectErrorMessage
    , expectField
    , expectListField
    , expectListSize
    , expectResponseCode
    , faucetAmt
    , fixtureIcarusWallet
    , fixturePassphrase
    , fixtureRandomWallet
    , getFromResponse
    , json
    , request
    , unsafeRequest
    , verify
    , walletId
    , (.>)
    )
import Test.Integration.Framework.TestData
    ( arabicWalletName
    , errMsg400NumberOfWords
    , errMsg403NothingToMigrate
    , errMsg404NoWallet
    , kanjiWalletName
    , mnemonics12
    , polishWalletName
    , russianWalletName
    , wildcardsWalletName
    )

import qualified Cardano.Wallet.Api.Link as Link
import qualified Data.Text as T
import qualified Network.HTTP.Types.Status as HTTP

spec :: forall t n. (n ~ 'Testnet) => SpecWith (Context t)
spec = do
    it "BYRON_CALCULATE_01 - \
        \for non-empty wallet calculated fee is > zero."
        $ \ctx -> forM_ [fmap fst . fixtureRandomWallet, fmap fst . fixtureIcarusWallet]
        $ \fixtureByronWallet -> do
            w <- fixtureByronWallet ctx
            let ep = Link.getMigrationInfo w
            r <- request @ApiByronWalletMigrationInfo ctx ep Default Empty
            verify r
                [ expectResponseCode @IO HTTP.status200
                , expectField (#migrationCost . #getQuantity)
                    (.> 0)
                ]

    it "BYRON_CALCULATE_02 - \
        \Cannot calculate fee for empty wallet."
        $ \ctx -> forM_ [emptyRandomWallet, emptyIcarusWallet] $ \emptyByronWallet -> do
            w <- emptyByronWallet ctx
            let ep = Link.getMigrationInfo w
            r <- request @ApiByronWalletMigrationInfo ctx ep Default Empty
            verify r
                [ expectResponseCode @IO HTTP.status403
                , expectErrorMessage (errMsg403NothingToMigrate $ w ^. walletId)
                ]

    it "BYRON_CALCULATE_02 - \
        \Cannot calculate fee for wallet with dust, that cannot be migrated."
        $ \ctx -> do
            -- NOTE
            -- Special mnemonic for which wallet with dust
            -- (1 utxo with 10 lovelace)
            let mnemonics =
                    [ "prison", "census", "discover", "give"
                    , "sound", "behave", "hundred", "cave"
                    , "someone", "orchard", "just", "wild"
                    ] :: [Text]
            let payloadRestore = Json [json| {
                    "name": "Dust Byron Wallet",
                    "mnemonic_sentence": #{mnemonics},
                    "passphrase": #{fixturePassphrase},
                    "style": "random"
                    } |]
            (_, w) <- unsafeRequest @ApiByronWallet ctx
                (Link.postWallet @'Byron) payloadRestore
            let ep = Link.getMigrationInfo w
            r <- request @ApiByronWalletMigrationInfo ctx ep Default Empty
            verify r
                [ expectResponseCode @IO HTTP.status403
                , expectErrorMessage (errMsg403NothingToMigrate $ w ^. walletId)
                ]

    it "BYRON_GET_04, DELETE_01 - Deleted wallet is not available" $ \ctx -> do
        w <- emptyRandomWallet ctx
        _ <- request @ApiByronWallet ctx (Link.deleteWallet @'Byron w) Default Empty
        rg <- request @ApiByronWallet ctx (Link.getWallet @'Byron w) Default Empty
        expectResponseCode @IO HTTP.status404 rg
        expectErrorMessage (errMsg404NoWallet $ w ^. walletId) rg

    it "BYRON_LIST_01 - Byron Wallets are listed from oldest to newest" $
        \ctx -> do
            m1 <- genMnemonics @12
            m2 <- genMnemonics @12
            m3 <- genMnemonics @12
            _ <- emptyByronWalletWith ctx "random" ("b1", m1, "Secure Passphrase")
            _ <- emptyByronWalletWith ctx "random" ("b2", m2, "Secure Passphrase")
            _ <- emptyByronWalletWith ctx "random" ("b3", m3, "Secure Passphrase")

            rl <- request @[ApiByronWallet] ctx (Link.listWallets @'Byron) Default Empty
            verify rl
                [ expectResponseCode @IO HTTP.status200
                , expectListSize 3
                , expectListField 0
                        (#name . #getApiT . #getWalletName) (`shouldBe` "b1")
                , expectListField 1
                        (#name . #getApiT . #getWalletName) (`shouldBe` "b2")
                , expectListField 2
                        (#name . #getApiT . #getWalletName) (`shouldBe` "b3")
                ]

    it "BYRON_LIST_01 - Interleave of Icarus and Random wallets" $ \ctx -> do
        let pwd = "Secure Passphrase"
        genMnemonics @15 >>= \m -> void (emptyByronWalletWith ctx "icarus" ("ica1", m, pwd))
        genMnemonics @12 >>= \m -> void (emptyByronWalletWith ctx "random" ("rnd2", m, pwd))
        genMnemonics @15 >>= \m -> void (emptyByronWalletWith ctx "icarus" ("ica3", m, pwd))
        rl <- request @[ApiByronWallet] ctx (Link.listWallets @'Byron) Default Empty
        verify rl
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 3
            , expectListField 0
                (#name . #getApiT . #getWalletName) (`shouldBe` "ica1")
            , expectListField 1
                (#name . #getApiT . #getWalletName) (`shouldBe` "rnd2")
            , expectListField 2
                (#name . #getApiT . #getWalletName) (`shouldBe` "ica3")
            ]

    describe "BYRON_RESTORE_01, GET_01, LIST_01 - Restore a wallet" $ do
        let scenarioSuccess style mnemonic ctx = do
                let name = "Empty Byron Wallet"
                let payload = Json [json| {
                        "name": #{name},
                        "mnemonic_sentence": #{mnemonic},
                        "passphrase": "Secure Passphrase",
                        "style": #{style}
                    }|]
                let expectations =
                            [ expectField
                                    (#name . #getApiT . #getWalletName) (`shouldBe` name)
                            , expectField (#balance . #available) (`shouldBe` Quantity 0)
                            , expectField (#balance . #total) (`shouldBe` Quantity 0)
                            , expectField #passphrase (`shouldNotBe` Nothing)
                            ]
                -- create
                r <- request @ApiByronWallet ctx
                    (Link.postWallet @'Byron) Default payload
                verify r expectations
                let w = getFromResponse id r

                eventually "wallet is available and ready" $ do
                    -- get
                    rg <- request @ApiByronWallet ctx
                        (Link.getWallet @'Byron w) Default Empty
                    verify rg $
                        (expectField (#state . #getApiT) (`shouldBe` Ready)) : expectations
                    -- list
                    rl <- request @[ApiByronWallet] ctx
                        (Link.listWallets @'Byron) Default Empty
                    verify rl
                        [ expectResponseCode @IO HTTP.status200
                        , expectListSize 1
                        , expectListField 0
                                (#name . #getApiT . #getWalletName) (`shouldBe` name)
                        , expectListField 0
                                (#balance . #available) (`shouldBe` Quantity 0)
                        , expectListField 0
                                (#state . #getApiT) (`shouldBe` Ready)
                        , expectListField 0
                                (#balance . #total) (`shouldBe` Quantity 0)
                        ]

        let scenarioFailure style mnemonic ctx = do
                let payload = Json [json| {
                        "name": "Empty Byron Wallet",
                        "mnemonic_sentence": #{mnemonic},
                        "passphrase": "Secure Passphrase",
                        "style": #{style}
                    }|]
                r <- request @ApiByronWallet ctx
                    (Link.postWallet @'Byron) Default payload
                verify r
                    [ expectResponseCode @IO HTTP.status400
                    , expectErrorMessage errMsg400NumberOfWords
                    ]

        let it' style genMnemonicIO test = do
                mnemonic <- runIO genMnemonicIO
                flip it (test style mnemonic) $ unwords
                    [ style
                    , show (length mnemonic)
                    , "words"
                    ]

        it' "random" (genMnemonics @9)  scenarioFailure -- ❌
        it' "random" (genMnemonics @12) scenarioSuccess -- ✔️
        it' "random" (genMnemonics @15) scenarioFailure -- ❌
        it' "random" (genMnemonics @18) scenarioFailure -- ❌
        it' "random" (genMnemonics @21) scenarioFailure -- ❌
        it' "random" (genMnemonics @24) scenarioFailure -- ❌

        it' "icarus" (genMnemonics @9)  scenarioFailure -- ❌
        it' "icarus" (genMnemonics @12) scenarioFailure -- ❌
        it' "icarus" (genMnemonics @15) scenarioSuccess -- ✔️
        it' "icarus" (genMnemonics @18) scenarioFailure -- ❌
        it' "icarus" (genMnemonics @21) scenarioFailure -- ❌
        it' "icarus" (genMnemonics @24) scenarioFailure -- ❌

        it' "trezor" (genMnemonics @9)  scenarioFailure -- ❌
        it' "trezor" (genMnemonics @12) scenarioSuccess -- ✔️
        it' "trezor" (genMnemonics @15) scenarioSuccess -- ✔️
        it' "trezor" (genMnemonics @18) scenarioSuccess -- ✔️
        it' "trezor" (genMnemonics @21) scenarioSuccess -- ✔️
        it' "trezor" (genMnemonics @24) scenarioSuccess -- ✔️

        it' "ledger" (genMnemonics @9)  scenarioFailure -- ❌
        it' "ledger" (genMnemonics @12) scenarioSuccess -- ✔️
        it' "ledger" (genMnemonics @15) scenarioSuccess -- ✔️
        it' "ledger" (genMnemonics @18) scenarioSuccess -- ✔️
        it' "ledger" (genMnemonics @21) scenarioSuccess -- ✔️
        it' "ledger" (genMnemonics @24) scenarioSuccess -- ✔️

    it "BYRON_RESTORE_02 - One can restore previously deleted wallet" $
        \ctx -> do
            m <- genMnemonics @12
            w <- emptyByronWalletWith ctx "random"
                ("Byron Wallet", m, "Secure Passphrase")
            rd <- request
                @ApiByronWallet ctx (Link.deleteWallet @'Byron w) Default Empty
            expectResponseCode @IO HTTP.status204 rd
            wr <- emptyByronWalletWith ctx "random"
                ("Byron Wallet2", m, "Secure Pa33phrase")
            w ^. walletId `shouldBe` wr ^. walletId

    it "BYRON_RESTORE_03 - Cannot restore wallet that exists" $ \ctx -> do
        mnemonic <- genMnemonics @12
        let payload = Json [json| {
                "name": "Some Byron Wallet",
                "mnemonic_sentence": #{mnemonic},
                "passphrase": "Secure Passphrase",
                "style": "random"
                } |]
        r1 <- request @ApiByronWallet ctx (Link.postWallet @'Byron) Default payload
        expectResponseCode @IO HTTP.status201 r1

        r2 <- request @ApiByronWallet ctx (Link.postWallet @'Byron) Default payload
        verify r2
            [ expectResponseCode @IO HTTP.status409
            , expectErrorMessage ("This operation would yield a wallet with the\
                 \ following id: " ++ T.unpack (getFromResponse walletId r1) ++
                 " However, I already know of a wallet with this id.")
            ]

    -- TODO
    -- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
    --
    -- describe "BYRON_RESTORE_04 - Wallet name" $ do
    --     let walNameMax = T.pack (replicate walletNameMaxLength 'ą')
    --     let matrix =
    --             [ ( show walletNameMinLength ++ " char long", "1"
    --               , [ expectResponseCode @IO HTTP.status201
    --                 , expectField
    --                         (#name . #getApiT . #getWalletName) (`shouldBe` "1")
    --                 ]
    --               )
    --             , ( show walletNameMaxLength ++ " char long", walNameMax
    --               , [ expectResponseCode @IO HTTP.status201
    --                 , expectField
    --                         (#name . #getApiT . #getWalletName) (`shouldBe` walNameMax)
    --                 ]
    --               )
    --             , ( show (walletNameMaxLength + 1) ++ " char long"
    --               , T.pack (replicate (walletNameMaxLength + 1) 'ę')
    --               , [ expectResponseCode @IO HTTP.status400
    --                 , expectErrorMessage "name is too long: expected at\
    --                         \ most 255 characters"
    --                 ]
    --               )
    --             , ( "Empty name", ""
    --                , [ expectResponseCode @IO HTTP.status400
    --                  , expectErrorMessage "name is too short: expected at\
    --                         \ least 1 character"
    --                  ]
    --               )
    --             , ( "Russian name", russianWalletName
    --               , [ expectResponseCode @IO HTTP.status201
    --                 , expectField
    --                         (#name . #getApiT . #getWalletName)
    --                         (`shouldBe` russianWalletName)
    --                 ]
    --               )
    --             , ( "Polish name", polishWalletName
    --               , [ expectResponseCode @IO HTTP.status201
    --                 , expectField
    --                         (#name . #getApiT . #getWalletName)
    --                         (`shouldBe` polishWalletName)
    --                 ]
    --               )
    --             , ( "Kanji name", kanjiWalletName
    --               , [ expectResponseCode @IO HTTP.status201
    --                 , expectField
    --                         (#name . #getApiT . #getWalletName)
    --                         (`shouldBe` kanjiWalletName)
    --                 ]
    --               )
    --             , ( "Arabic name", arabicWalletName
    --               , [ expectResponseCode @IO HTTP.status201
    --                 , expectField
    --                         (#name . #getApiT . #getWalletName)
    --                         (`shouldBe` arabicWalletName)
    --                 ]
    --               )
    --             , ( "Wildcards name", wildcardsWalletName
    --               , [ expectResponseCode @IO HTTP.status201
    --                 , expectField
    --                         (#name . #getApiT . #getWalletName)
    --                         (`shouldBe` wildcardsWalletName)
    --                 ]
    --               )
    --             ]
    --     forM_ matrix $ \(title, walName, expectations) -> it title $ \ctx -> do
    --         let payload = Json [json| {
    --                 "name": #{walName},
    --                 "mnemonic_sentence": #{mnemonics12},
    --                 "passphrase": "Secure Passphrase"
    --                 } |]
    --         r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --         verify r expectations

    -- it "BYRON_RESTORE_04 - [] as name -> fail" $ \ctx -> do
    --     let payload = Json [json| {
    --             "name": [],
    --             "mnemonic_sentence": #{mnemonics12},
    --             "passphrase": "Secure Passphrase"
    --             } |]
    --     r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --     verify r
    --         [ expectResponseCode @IO HTTP.status400
    --         , expectErrorMessage "expected Text, encountered Array"
    --         ]

    -- it "BYRON_RESTORE_04 - Num as name -> fail" $ \ctx -> do
    --     let payload = Json [json| {
    --             "name": 123,
    --             "mnemonic_sentence": #{mnemonics12},
    --             "passphrase": "Secure Passphrase"
    --             } |]
    --     r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --     verify r
    --         [ expectResponseCode @IO HTTP.status400
    --         , expectErrorMessage "expected Text, encountered Number"
    --         ]

    -- it "BYRON_RESTORE_04 - Name param missing -> fail" $ \ctx -> do
    --     let payload = Json [json| {
    --             "mnemonic_sentence": #{mnemonics12},
    --             "passphrase": "Secure Passphrase"
    --             } |]
    --     r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --     verify r
    --         [ expectResponseCode @IO HTTP.status400
    --         , expectErrorMessage "key 'name' not present"
    --         ]

    -- describe "BYRON_RESTORE_05 - Faulty mnemonics" $ do
    --     let matrix =
    --          [ ( "[] as mnemonic_sentence -> fail", []
    --            , [ expectResponseCode @IO HTTP.status400
    --              , expectErrorMessage
    --                 "Invalid number of words: 12 words are expected"
    --              ]
    --            )
    --          , ( "specMnemonicSentence -> fail", specMnemonicByron
    --            , [ expectResponseCode @IO HTTP.status400
    --              , expectErrorMessage "Invalid entropy checksum: please \
    --                   \double-check the last word of your mnemonic sentence."
    --              ]
    --            )
    --          , ( "invalid mnemonics -> fail", invalidMnemonics12
    --            , [ expectResponseCode @IO HTTP.status400
    --              , expectErrorMessage "Invalid entropy checksum: please \
    --                   \double-check the last word of your mnemonic sentence."
    --              ]
    --            )
    --          , ( "Japanese mnemonics -> fail", japaneseMnemonics12
    --            , [ expectResponseCode @IO HTTP.status400
    --              , expectErrorMessage errMsgNotInDictionary
    --              ]
    --            )
    --          , ( "French mnemonics -> fail"
    --            , frenchMnemonics12
    --            , [ expectResponseCode @IO HTTP.status400
    --              , expectErrorMessage errMsgNotInDictionary
    --              ]
    --            )
    --          ]

    --     forM_ matrix $ \(title, mnemonics, expectations) -> it title $
    --         \ctx -> do
    --             let payload = Json [json| {
    --                     "name": "Byron Wallet bye bye",
    --                     "mnemonic_sentence": #{mnemonics},
    --                     "passphrase": "Secure Passphrase"
    --                     } |]
    --             r <- request
    --                 @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --             verify r expectations

    -- it "BYRON_RESTORE_05 - String as mnemonic_sentence -> fail" $ \ctx -> do
    --     let payload = Json [json| {
    --             "name": "ads",
    --             "mnemonic_sentence": "album execute kingdom dumb trip",
    --             "passphrase": "Secure Passphrase"
    --             } |]
    --     r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --     verify r
    --         [ expectResponseCode @IO HTTP.status400
    --         , expectErrorMessage "expected [a], encountered String"
    --         ]

    -- it "BYRON_RESTORE_05 - Num as mnemonic_sentence -> fail" $ \ctx -> do
    --     let payload = Json [json| {
    --             "name": "123",
    --             "mnemonic_sentence": 15,
    --             "passphrase": "Secure Passphrase"
    --             } |]
    --     r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --     verify r
    --         [ expectResponseCode @IO HTTP.status400
    --         , expectErrorMessage "expected [a], encountered Number"
    --         ]

    -- it "BYRON_RESTORE_05 - mnemonic_sentence param missing -> fail" $ \ctx -> do
    --     let payload = Json [json| {
    --             "name": "A name",
    --             "passphrase": "Secure Passphrase"
    --             } |]
    --     r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
    --     verify r
    --         [ expectResponseCode @IO HTTP.status400
    --         , expectErrorMessage "key 'mnemonic_sentence' not present"
    --         ]

    describe "BYRON_RESTORE_06 - Passphrase" $ do
        let minLength = passphraseMinLength (Proxy @"encryption")
        let maxLength = passphraseMaxLength (Proxy @"encryption")
        let matrix =
                [ ( show minLength ++ " char long"
                  , T.pack (replicate minLength 'ź')
                  , [ expectResponseCode @IO HTTP.status201 ]
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
-- TODO
-- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
--
--
--
--                , ( show (minLength - 1) ++ " char long"
--                  , T.pack (replicate (minLength - 1) 'ż')
--                  , [ expectResponseCode @IO HTTP.status400
--                    , expectErrorMessage "passphrase is too short: expected at\
--                            \ least 10 characters"
--                    ]
--                  )
--                , ( show (maxLength + 1) ++ " char long"
--                  , T.pack (replicate (maxLength + 1) 'ę')
--                  , [ expectResponseCode @IO HTTP.status400
--                    , expectErrorMessage "passphrase is too long: expected at\
--                            \ most 255 characters"
--                    ]
--                  )
--                , ( "Empty passphrase", ""
--                   , [ expectResponseCode @IO HTTP.status400
--                     , expectErrorMessage "passphrase is too short: expected at\
--                            \ least 10 characters"
--                     ]
--                  )
--                ]
        forM_ matrix $ \(title, passphrase, expectations) -> it title $
            \ctx -> do
                let payload = Json [json| {
                        "name": "Secure Wallet",
                        "mnemonic_sentence": #{mnemonics12},
                        "passphrase": #{passphrase},
                        "style": "random"
                        } |]
                r <- request
                    @ApiByronWallet ctx (Link.postWallet @'Byron) Default payload
                verify r expectations
--
--    it "BYRON_RESTORE_06 - [] as passphrase -> fail" $ \ctx -> do
--        let payload = Json [json| {
--                "name": "Secure Wallet",
--                "mnemonic_sentence": #{mnemonics12},
--                "passphrase": []
--                } |]
--        r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
--        verify r
--            [ expectResponseCode @IO HTTP.status400
--            , expectErrorMessage "expected Text, encountered Array"
--            ]
--
--    it "BYRON_RESTORE_06 - Num as passphrase -> fail" $ \ctx -> do
--        let payload = Json [json| {
--                "name": "Secure Wallet",
--                "mnemonic_sentence": #{mnemonics12},
--                "passphrase": 777
--                } |]
--        r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
--        verify r
--            [ expectResponseCode @IO HTTP.status400
--            , expectErrorMessage "expected Text, encountered Number"
--            ]
--
--    it "BYRON_RESTORE_06 - passphrase param missing -> fail" $ \ctx -> do
--        let payload = Json [json| {
--                "name": "Secure Wallet",
--                "mnemonic_sentence": #{mnemonics12}
--                } |]
--        r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
--        verify r
--            [ expectResponseCode @IO HTTP.status400
--            , expectErrorMessage "key 'passphrase' not present"
--            ]

-- TODO
-- MOVE TO test/unit/Cardano/Wallet/ApiSpec.hs
--
--    describe "BYRON_RESTORE_07 - Bad request" $ do
--        let matrix =
--                [ ( "empty payload", NonJson "" )
--                , ( "{} payload", NonJson "{}" )
--                , ( "non-json valid payload"
--                  , NonJson
--                        "{name: wallet,\
--                        \ mnemonic_sentence: [pill, hand, ask, useless, asset,\
--                        \ rely, above, pipe, embark, game, elder, unaware,\
--                        \ nasty, coach, glad],\
--                        \ passphrase: 1234567890}"
--                  )
--                ]
--
--        forM_ matrix $ \(name, nonJson) -> it name $ \ctx -> do
--            let payload = nonJson
--            r <- request @ApiByronWallet ctx (Link.postWallet @'Random) Default payload
--            expectResponseCode @IO HTTP.status400 r

    it "BYRON_RESTORE_08 - Icarus wallet with high indexes" $ \ctx -> do
        -- NOTE
        -- Special Icarus mnemonic where address indexes are all after the index
        -- 500. Because we don't have the whole history, restoring sequential
        -- wallets like Icarus ones is tricky from just a snapshot and we need
        -- to use arbitrarily big address pool gaps.
        let mnemonics =
                [ "erosion", "ahead", "vibrant", "air", "day"
                , "timber", "thunder", "general", "dice", "into"
                , "chest", "enrich", "social", "neck", "shine"
                ] :: [Text]
        let payload = Json [json| {
                "name": "High Index Wallet",
                "mnemonic_sentence": #{mnemonics},
                "passphrase": #{fixturePassphrase},
                "style": "icarus"
                } |]

        r <- request @ApiByronWallet ctx (Link.postWallet @'Byron) Default payload
        verify r
            [ expectResponseCode @IO HTTP.status201
            , expectField (#balance . #available) (`shouldBe` Quantity faucetAmt)
            ]

    it "BYRON_RESTORE_09 - Ledger wallet" $ \ctx -> do
        -- NOTE
        -- Special legacy wallets where addresses have been generated from a
        -- seed derived using the auxiliary method used by Ledger.
        let mnemonics =
                [ "vague" , "wrist" , "poet" , "crazy" , "danger" , "dinner"
                , "grace" , "home" , "naive" , "unfold" , "april" , "exile"
                , "relief" , "rifle" , "ranch" , "tone" , "betray" , "wrong"
                ] :: [Text]
        let payload = Json [json| {
                "name": "Ledger Wallet",
                "mnemonic_sentence": #{mnemonics},
                "passphrase": #{fixturePassphrase},
                "style": "ledger"
                } |]

        r <- request @ApiByronWallet ctx (Link.postWallet @'Byron) Default payload
        verify r
            [ expectResponseCode @IO HTTP.status201
            , expectField (#balance . #available) (`shouldBe` Quantity faucetAmt)
            ]
 where
     genMnemonics
        :: forall mw ent csz.
            ( ConsistentEntropy ent mw csz
            , ValidEntropySize ent
            , ValidChecksumSize ent csz
            , ent ~ EntropySize mw
            , mw ~ MnemonicWords ent
            )
        => IO [Text]
     genMnemonics = mnemonicToText . entropyToMnemonic @mw <$> genEntropy
