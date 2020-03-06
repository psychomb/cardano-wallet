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
    ( ApiByronWallet
    , ApiByronWalletMigrationInfo (..)
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
import Data.Aeson.QQ
    ( aesonQQ )
import Data.Generics.Internal.VL.Lens
    ( view, (^.) )
import Data.Maybe
    ( mapMaybe )
import Data.Proxy
    ( Proxy (..) )
import Data.Quantity
    ( Quantity (..) )
import Data.Text
    ( Text )
import Data.Word
    ( Word64 )
import Test.Hspec
    ( SpecWith, describe, it, runIO, shouldNotBe, shouldSatisfy )
import Test.Hspec.Expectations.Lifted
    ( shouldBe )
import Test.Integration.Framework.DSL
    ( Context (..)
    , Headers (..)
    , Payload (..)
    , emptyByronWalletWith
    , emptyIcarusWallet
    , emptyRandomWallet
    , emptyWallet
    , emptyWalletWith
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
    , fixtureWallet
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
    , errMsg400ParseError
    , errMsg403NothingToMigrate
    , errMsg403WrongPass
    , errMsg404NoWallet
    , kanjiWalletName
    , mnemonics12
    , polishWalletName
    , russianWalletName
    , wildcardsWalletName
    )

import qualified Cardano.Wallet.Api.Link as Link
import qualified Cardano.Wallet.Api.Types as ApiTypes
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Network.HTTP.Types.Status as HTTP

spec :: forall t n. (n ~ 'Testnet) => SpecWith (Context t)
spec = do

    -- Compute the fee associated with an API transaction.
    let apiTransactionFee :: ApiTransaction n -> Word64
        apiTransactionFee t =
            inputBalance t - outputBalance t
          where
            inputBalance = fromIntegral
                . sum
                . fmap (view (#amount . #getQuantity))
                . mapMaybe ApiTypes.source
                . view #inputs
            outputBalance = fromIntegral
                . sum
                . fmap (view (#amount . #getQuantity))
                . view #outputs

    it "BYRON_CALCULATE_01 - \
        \for non-empty wallet calculated fee is > zero."
        $ \ctx -> forM_ [fixtureRandomWallet, fixtureIcarusWallet] $ \fixtureByronWallet -> do
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

    it "BYRON_CALCULATE_03 - \
        \Cannot estimate migration for Shelley wallet"
        $ \ctx -> do
            w <- emptyWallet ctx
            let ep = Link.getMigrationInfo w
            r <- request @ApiByronWalletMigrationInfo ctx ep Default Empty
            expectResponseCode @IO HTTP.status404 r
            expectErrorMessage (errMsg404NoWallet $ w ^. walletId) r

    it "BYRON_MIGRATE_01 - \
        \after a migration operation successfully completes, the correct \
        \amount eventually becomes available in the target wallet."
        $ \ctx -> forM_ [fixtureRandomWallet, fixtureIcarusWallet] $ \fixtureByronWallet -> do
            -- Restore a Byron wallet with funds, to act as a source wallet:
            sourceWallet <- fixtureByronWallet ctx
            let originalBalance =
                        view (#balance . #available . #getQuantity) sourceWallet

            -- Create an empty target wallet:
            targetWallet <- emptyWallet ctx

            -- Calculate the expected migration fee:
            r0 <- request @ApiByronWalletMigrationInfo ctx
                (Link.getMigrationInfo sourceWallet) Default Empty
            verify r0
                [ expectResponseCode @IO HTTP.status200
                , expectField #migrationCost (.> Quantity 0)
                ]
            let expectedFee = getFromResponse (#migrationCost . #getQuantity) r0

            -- Perform a migration from the source wallet to the target wallet:
            r1 <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sourceWallet targetWallet)
                Default
                (Json [aesonQQ|{"passphrase": #{fixturePassphrase}}|])
            verify r1
                [ expectResponseCode @IO HTTP.status202
                , expectField id (`shouldSatisfy` (not . null))
                ]

            -- Check that funds become available in the target wallet:
            let expectedBalance = originalBalance - expectedFee
            eventually "Wallet has expectedBalance" $ do
                r2 <- request @ApiWallet ctx
                    (Link.getWallet @'Shelley targetWallet) Default Empty
                verify r2
                    [ expectField
                            (#balance . #getApiT . #available)
                            (`shouldBe` Quantity expectedBalance)
                    , expectField
                            (#balance . #getApiT . #total)
                            (`shouldBe` Quantity expectedBalance)
                    ]

    it "BYRON_MIGRATE_01 - \
        \ migrate a big wallet requiring more than one tx" $ \ctx -> do
        -- NOTE
        -- Special mnemonic for which 500 legacy funds are attached to in the
        -- genesis file.
        --
        -- Out of these 500 coins, 100 of them are of 1 Lovelace and are
        -- expected to be treated as dust. The rest are all worth:
        -- 10,000,000,000 lovelace.
        let mnemonics =
                ["collect", "fold", "file", "clown"
                , "injury", "sun", "brass", "diet"
                , "exist", "spike", "behave", "clip"
                ] :: [Text]
        let payloadRestore = Json [json| {
                "name": "Big Byron Wallet",
                "mnemonic_sentence": #{mnemonics},
                "passphrase": #{fixturePassphrase},
                "style": "random"
                } |]
        (_, wOld) <- unsafeRequest @ApiByronWallet ctx
            (Link.postWallet @'Byron) payloadRestore
        eventually "wallet balance greater than 0" $ do
            request @ApiByronWallet ctx
                (Link.getWallet @'Byron wOld)
                Default
                Empty >>= flip verify
                [ expectField (#balance . #available) (.> Quantity 0)
                ]
        let originalBalance = view (#balance . #available . #getQuantity) wOld

        -- Calculate the expected migration fee:
        rFee <- request @ApiByronWalletMigrationInfo ctx
            (Link.getMigrationInfo wOld)
            Default
            Empty
        verify rFee
            [ expectResponseCode @IO HTTP.status200
            , expectField #migrationCost (.> Quantity 0)
            ]
        let expectedFee = getFromResponse (#migrationCost . #getQuantity) rFee

        -- Migrate to a new empty wallet
        wNew <- emptyWallet ctx
        let payloadMigrate = Json [json|{"passphrase": #{fixturePassphrase}}|]
        request @[ApiTransaction n] ctx
            (Link.migrateWallet wOld wNew)
            Default
            payloadMigrate >>= flip verify
            [ expectResponseCode @IO HTTP.status202
            , expectField id ((`shouldBe` 2). length)
            ]

        -- Check that funds become available in the target wallet:
        let expectedBalance = originalBalance - expectedFee
        eventually "wallet balance = expectedBalance" $ do
            request @ApiWallet ctx
                (Link.getWallet @'Shelley wNew)
                Default
                Empty >>= flip verify
                [ expectField
                        (#balance . #getApiT . #available)
                        ( `shouldBe` Quantity expectedBalance)
                , expectField
                        (#balance . #getApiT . #total)
                        ( `shouldBe` Quantity expectedBalance)
                ]

        -- Analyze the target wallet UTxO distribution
        request @ApiUtxoStatistics ctx (Link.getUTxOsStatistics wNew)
            Default
            Empty >>= flip verify
            [ expectField
                #distribution
                ((`shouldBe` (Just 400)) . Map.lookup 10_000_000_000)
            ]

    it "BYRON_MIGRATE_01 - \
        \a migration operation removes all funds from the source wallet."
        $ \ctx -> forM_ [fixtureRandomWallet, fixtureIcarusWallet] $ \fixtureByronWallet -> do
            -- Restore a Byron wallet with funds, to act as a source wallet:
            sourceWallet <- fixtureByronWallet ctx

            -- Perform a migration from the source wallet to a target wallet:
            targetWallet <- emptyWallet ctx
            r0 <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sourceWallet targetWallet )
                Default
                (Json [json|{"passphrase": #{fixturePassphrase}}|])
            verify r0
                [ expectResponseCode @IO HTTP.status202
                , expectField id (`shouldSatisfy` (not . null))
                ]

            -- Verify that the source wallet has no funds available:
            r1 <- request @ApiByronWallet ctx
                (Link.getWallet @'Byron sourceWallet) Default Empty
            verify r1
                [ expectResponseCode @IO HTTP.status200
                , expectField (#balance . #available) (`shouldBe` Quantity 0)
                ]

    it "BYRON_MIGRATE_02 - \
        \migrating an empty wallet should fail."
        $ \ctx -> forM_ [emptyRandomWallet, emptyIcarusWallet] $ \emptyByronWallet -> do
            sourceWallet <- emptyByronWallet ctx
            targetWallet <- emptyWallet ctx
            let payload = Json [json|{"passphrase": "Secure Passphrase"}|]
            let ep = Link.migrateWallet sourceWallet targetWallet
            r <- request @[ApiTransaction n] ctx ep Default payload
            let srcId = sourceWallet ^. walletId
            verify r
                [ expectResponseCode @IO HTTP.status403
                , expectErrorMessage (errMsg403NothingToMigrate srcId)
                ]

    it "BYRON_MIGRATE_02 - \
        \migrating wallet with dust should fail."
        $ \ctx -> do
            -- NOTE
            -- Special mnemonic for which wallet with dust
            -- (5 utxos with 60 lovelace in total)
            let mnemonics =
                    [ "suffer", "decorate", "head", "opera"
                    , "yellow", "debate", "visa", "fire"
                    , "salute", "hybrid", "stone", "smart"
                    ] :: [Text]
            let payloadRestore = Json [json| {
                    "name": "Dust Byron Wallet",
                    "mnemonic_sentence": #{mnemonics},
                    "passphrase": #{fixturePassphrase},
                    "style": "random"
                    } |]
            (_, sourceWallet) <- unsafeRequest @ApiByronWallet ctx
                (Link.postWallet @'Byron) payloadRestore
            eventually "wallet balance greater than 0" $ do
                request @ApiByronWallet ctx
                    (Link.getWallet @'Byron sourceWallet)
                    Default
                    Empty >>= flip verify
                    [ expectField (#balance . #available) (.> Quantity 0)
                    ]

            targetWallet <- emptyWallet ctx
            let payload = Json [json|{"passphrase": #{fixturePassphrase}}|]
            let ep = Link.migrateWallet sourceWallet targetWallet
            r <- request @[ApiTransaction n] ctx ep Default payload
            let srcId = sourceWallet ^. walletId
            verify r
                [ expectResponseCode @IO HTTP.status403
                , expectErrorMessage (errMsg403NothingToMigrate srcId)
                ]

    it "BYRON_MIGRATE_03 - \
        \actual fee for migration is the same as the predicted fee."
        $ \ctx -> forM_ [fixtureRandomWallet, fixtureIcarusWallet] $ \fixtureByronWallet -> do
            -- Restore a Byron wallet with funds.
            sourceWallet <- fixtureByronWallet ctx

            -- Request a migration fee prediction.
            let ep0 = (Link.getMigrationInfo sourceWallet)
            r0 <- request @ApiByronWalletMigrationInfo ctx ep0 Default Empty
            verify r0
                [ expectResponseCode @IO HTTP.status200
                , expectField #migrationCost (.> Quantity 0)
                ]

            -- Perform the migration.
            targetWallet <- emptyWallet ctx
            let payload = Json [json|{"passphrase": #{fixturePassphrase}}|]
            let ep1 = Link.migrateWallet sourceWallet targetWallet
            r1 <- request @[ApiTransaction n] ctx ep1 Default payload
            verify r1
                [ expectResponseCode @IO HTTP.status202
                , expectField id (`shouldSatisfy` (not . null))
                ]

            -- Verify that the fee prediction was correct.
            let actualFee = fromIntegral $ sum $ apiTransactionFee
                    <$> getFromResponse id r1
            let predictedFee =
                    getFromResponse (#migrationCost . #getQuantity) r0
            actualFee `shouldBe` predictedFee

    it "BYRON_MIGRATE_04 - migration fails with a wrong passphrase"
        $ \ctx -> forM_ [fixtureRandomWallet, fixtureIcarusWallet] $ \fixtureByronWallet -> do
        -- Restore a Byron wallet with funds, to act as a source wallet:
        sourceWallet <- fixtureByronWallet ctx

        -- Perform a migration from the source wallet to a target wallet:
        targetWallet <- emptyWallet ctx
        r0 <- request @[ApiTransaction n] ctx
            (Link.migrateWallet sourceWallet targetWallet )
            Default
            (Json [json|{"passphrase": "not-the-right-passphrase"}|])
        verify r0
            [ expectResponseCode @IO HTTP.status403
            , expectErrorMessage errMsg403WrongPass
            ]

    describe "BYRON_MIGRATE_05 -\
        \ migrating from/to inappropriate wallet types" $ do

        it "Byron -> Byron" $ \ctx -> do
            sWallet <- fixtureRandomWallet ctx
            tWallet <- emptyRandomWallet ctx

            r <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sWallet tWallet )
                Default
                (Json [json|{ "passphrase": #{fixturePassphrase} }|])
            verify r
                [ expectResponseCode @IO HTTP.status404
                , expectErrorMessage (errMsg404NoWallet $ tWallet ^. walletId)
                ]

        it "Icarus -> Icarus" $ \ctx -> do
            sWallet <- fixtureIcarusWallet ctx
            tWallet <- emptyIcarusWallet ctx

            r <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sWallet tWallet )
                Default
                (Json [json|{ "passphrase": #{fixturePassphrase} }|])
            verify r
                [ expectResponseCode @IO HTTP.status404
                , expectErrorMessage (errMsg404NoWallet $ tWallet ^. walletId)
                ]

        it "Icarus -> Byron" $ \ctx -> do
            sWallet <- fixtureIcarusWallet ctx
            tWallet <- emptyRandomWallet ctx

            r <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sWallet tWallet )
                Default
                (Json [json|{ "passphrase": #{fixturePassphrase} }|])
            verify r
                [ expectResponseCode @IO HTTP.status404
                , expectErrorMessage (errMsg404NoWallet $ tWallet ^. walletId)
                ]

        it "Byron -> Icarus" $ \ctx -> do
            sWallet <- fixtureRandomWallet ctx
            tWallet <- emptyIcarusWallet ctx

            r <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sWallet tWallet )
                Default
                (Json [json|{ "passphrase": #{fixturePassphrase} }|])
            verify r
                [ expectResponseCode @IO HTTP.status404
                , expectErrorMessage (errMsg404NoWallet $ tWallet ^. walletId)
                ]

        it "Shelley -> Byron" $ \ctx -> do
            sWallet <- fixtureWallet ctx
            tWallet <- emptyRandomWallet ctx

            r <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sWallet tWallet )
                Default
                (Json [json|{ "passphrase": #{fixturePassphrase} }|])
            verify r
                [ expectResponseCode @IO HTTP.status404
                , expectErrorMessage (errMsg404NoWallet $ sWallet ^. walletId)
                ]

        it "Shelley -> Icarus" $ \ctx -> do
            sWallet <- fixtureWallet ctx
            tWallet <- emptyIcarusWallet ctx

            r <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sWallet tWallet )
                Default
                (Json [json|{ "passphrase": #{fixturePassphrase} }|])
            verify r
                [ expectResponseCode @IO HTTP.status404
                , expectErrorMessage (errMsg404NoWallet $ sWallet ^. walletId)
                ]

        it "Shelley -> Shelley" $ \ctx -> do
            sWallet <- fixtureWallet ctx
            tWallet <- emptyWallet ctx

            r <- request @[ApiTransaction n] ctx
                (Link.migrateWallet sWallet tWallet )
                Default
                (Json [json|{ "passphrase": #{fixturePassphrase} }|])
            verify r
                [ expectResponseCode @IO HTTP.status404
                , expectErrorMessage (errMsg404NoWallet $ sWallet ^. walletId)
                ]

    it "BYRON_MIGRATE_07 - invalid payload, parser error" $ \ctx -> do
        sourceWallet <- emptyRandomWallet ctx
        targetWallet <- emptyWallet ctx

        r <- request @[ApiTransaction n] ctx
            (Link.migrateWallet sourceWallet targetWallet )
            Default
            (NonJson "{passphrase:,}")
        expectResponseCode @IO HTTP.status400 r
        expectErrorMessage errMsg400ParseError r

    it "BYRON_GET_02 - Byron ep does not show Shelley wallet" $ \ctx -> do
        w <- emptyWallet ctx
        r <- request @ApiByronWallet ctx
            (Link.getWallet @'Byron w) Default Empty
        expectResponseCode @IO HTTP.status404 r
        expectErrorMessage (errMsg404NoWallet $ w ^. walletId) r

    it "BYRON_GET_03 - Shelley ep does not show Byron wallet" $ \ctx -> do
        w <- emptyRandomWallet ctx
        r <- request @ApiWallet ctx
            (Link.getWallet @'Shelley w) Default Empty
        expectResponseCode @IO HTTP.status404 r
        expectErrorMessage (errMsg404NoWallet $ w ^. walletId) r

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

    it "BYRON_LIST_02,03 -\
        \ Byron wallets listed only via Byron endpoints \\\
        \ Shelley wallets listed only via new endpoints" $ \ctx -> do
        m1 <- genMnemonics @12
        m2 <- genMnemonics @12
        m3 <- genMnemonics @12
        _ <- emptyByronWalletWith ctx "random" ("byron1", m1, "Secure Passphrase")
        _ <- emptyByronWalletWith ctx "random" ("byron2", m2, "Secure Passphrase")
        _ <- emptyByronWalletWith ctx "random" ("byron3", m3, "Secure Passphrase")

        _ <- emptyWalletWith ctx ("shelley1", "Secure Passphrase", 20)
        _ <- emptyWalletWith ctx ("shelley2", "Secure Passphrase", 20)
        _ <- emptyWalletWith ctx ("shelley3", "Secure Passphrase", 20)

        --list only byron
        rl <- request @[ApiByronWallet] ctx (Link.listWallets @'Byron) Default Empty
        verify rl
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 3
            , expectListField 0
                    (#name . #getApiT . #getWalletName) (`shouldBe` "byron1")
            , expectListField 1
                    (#name . #getApiT . #getWalletName) (`shouldBe` "byron2")
            , expectListField 2
                    (#name . #getApiT . #getWalletName) (`shouldBe` "byron3")
            ]
        --list only shelley
        rl2 <- request @[ApiWallet] ctx (Link.listWallets @'Shelley) Default Empty
        verify rl2
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 3
            , expectListField 0
                    (#name . #getApiT . #getWalletName) (`shouldBe` "shelley1")
            , expectListField 1
                    (#name . #getApiT . #getWalletName) (`shouldBe` "shelley2")
            , expectListField 2
                    (#name . #getApiT . #getWalletName) (`shouldBe` "shelley3")
            ]

    it "BYRON_LIST_04, DELETE_01 -\
        \ Deleted wallets cannot be listed" $ \ctx -> do
        m1 <- genMnemonics @12
        m2 <- genMnemonics @12
        m3 <- genMnemonics @12
        _   <- emptyByronWalletWith ctx "random" ("byron1", m1, "Secure Passphrase")
        wb2 <- emptyByronWalletWith ctx "random" ("byron2", m2, "Secure Passphrase")
        _   <- emptyByronWalletWith ctx "random" ("byron3", m3, "Secure Passphrase")

        _ <- emptyWalletWith ctx ("shelley1", "Secure Passphrase", 20)
        _ <- emptyWalletWith ctx ("shelley2", "Secure Passphrase", 20)
        ws3 <- emptyWalletWith ctx ("shelley3", "Secure Passphrase", 20)

        -- delete
        _ <- request @ApiByronWallet ctx (Link.deleteWallet @'Byron wb2) Default Empty
        _ <- request @ApiWallet ctx (Link.deleteWallet @'Shelley ws3) Default Empty

        --list only byron
        rdl <- request @[ApiByronWallet] ctx (Link.listWallets @'Byron) Default Empty
        verify rdl
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 2
            , expectListField 0
                    (#name . #getApiT . #getWalletName) (`shouldBe` "byron1")
            , expectListField 1
                    (#name . #getApiT . #getWalletName) (`shouldBe` "byron3")
            ]
        --list only shelley
        rdl2 <- request @[ApiWallet] ctx (Link.listWallets @'Shelley) Default Empty
        verify rdl2
            [ expectResponseCode @IO HTTP.status200
            , expectListSize 2
            , expectListField 0
                    (#name . #getApiT . #getWalletName) (`shouldBe` "shelley1")
            , expectListField 1
                    (#name . #getApiT . #getWalletName) (`shouldBe` "shelley2")
            ]

    it "BYRON_DELETE_02 - Byron ep does not delete Shelley wallet" $ \ctx -> do
        w <- emptyWallet ctx
        r <- request @ApiByronWallet ctx (Link.deleteWallet @'Byron w) Default Empty
        expectResponseCode @IO HTTP.status404 r
        expectErrorMessage (errMsg404NoWallet $ w ^. walletId) r

    it "BYRON_DELETE_03 - Shelley ep does not delete Byron wallet" $ \ctx -> do
        w <- emptyRandomWallet ctx
        r <- request @ApiByronWallet ctx (Link.deleteWallet @'Shelley w) Default Empty
        expectResponseCode @IO HTTP.status404 r
        expectErrorMessage (errMsg404NoWallet $ w ^. walletId) r

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
