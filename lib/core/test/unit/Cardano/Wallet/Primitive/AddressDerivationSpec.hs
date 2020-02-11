{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Cardano.Wallet.Primitive.AddressDerivationSpec
    ( spec

    -- * Generators
    , genAddress
    , genLegacyAddress
    ) where

import Prelude

import Cardano.Crypto.Wallet
    ( XPub, unXPrv )
import Cardano.Wallet.Primitive.AddressDerivation
    ( Depth (..)
    , DerivationType (..)
    , ErrWrongPassphrase (..)
    , FromMnemonic (..)
    , FromMnemonicError (..)
    , Index
    , NetworkDiscriminant (..)
    , NetworkDiscriminant (..)
    , Passphrase (..)
    , PassphraseMaxLength (..)
    , PassphraseMinLength (..)
    , PersistPrivateKey (..)
    , PersistPublicKey (..)
    , WalletKey (..)
    , XPrv
    , checkPassphrase
    , encryptPassphrase
    , getIndex
    , hex
    , unXPrvStripPub
    )
import Cardano.Wallet.Primitive.AddressDerivation.Byron
    ( ByronKey (..) )
import Cardano.Wallet.Primitive.AddressDerivation.Icarus
    ( IcarusKey (..) )
import Cardano.Wallet.Primitive.AddressDerivation.Shelley
    ( KnownNetwork (..), ShelleyKey (..) )
import Cardano.Wallet.Primitive.Types
    ( Address (..), Hash (..) )
import Control.Monad
    ( replicateM )
import Control.Monad.IO.Class
    ( liftIO )
import Data.Either
    ( isRight )
import Data.Proxy
    ( Proxy (..) )
import System.Process
    ( readProcessWithExitCode )
import Test.Hspec
    ( Spec, describe, it, shouldBe, shouldSatisfy )
import Test.QuickCheck
    ( Arbitrary (..)
    , Gen
    , InfiniteList (..)
    , Property
    , arbitraryBoundedEnum
    , arbitraryPrintableChar
    , choose
    , counterexample
    , expectFailure
    , genericShrink
    , oneof
    , property
    , vectorOf
    , (.&&.)
    , (===)
    , (==>)
    )
import Test.QuickCheck.Monadic
    ( assert, monadicIO, monitor, run )
import Test.Text.Roundtrip
    ( textRoundtrip )

import qualified Cardano.Wallet.Primitive.AddressDerivation.Byron as Rnd
import qualified Cardano.Wallet.Primitive.AddressDerivation.Icarus as Ica
import qualified Cardano.Wallet.Primitive.AddressDerivation.Shelley as Seq
import qualified Data.ByteArray as BA
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.Text as T
import qualified Data.Text.Encoding as T

spec :: Spec
spec = do
    describe "Bounded / Enum relationship" $ do
        it "The calls Index.succ maxBound should result in a runtime err (hard)"
            prop_succMaxBoundHardIx
        it "The calls Index.pred minBound should result in a runtime err (hard)"
            prop_predMinBoundHardIx
        it "The calls Index.succ maxBound should result in a runtime err (soft)"
            prop_succMaxBoundSoftIx
        it "The calls Index.pred minBound should result in a runtime err (soft)"
            prop_predMinBoundSoftIx

    describe "Text Roundtrip" $ do
        textRoundtrip $ Proxy @(Passphrase "encryption")
        textRoundtrip $ Proxy @NetworkDiscriminant

    describe "Enum Roundtrip" $ do
        it "Index @'Hardened _" (property prop_roundtripEnumIndexHard)
        it "Index @'Soft _" (property prop_roundtripEnumIndexSoft)

    describe "Passphrases" $ do
        it "checkPassphrase p h(p) == Right ()" $
            property prop_passphraseRoundtrip

        it "p /= p' => checkPassphrase p' h(p) == Left ErrWrongPassphrase" $
            property prop_passphraseRoundtripFail

        it "checkPassphrase fails when hash is malformed" $
            property prop_passphraseHashMalformed

    describe "FromMnemonic" $ do
        let noInDictErr word =
                "Found an unknown word not present in the pre-defined dictionary\
                \: \"" <> word <> "\". The full dictionary is available \
                \here: https://github.com/input-output-hk/cardano-wallet/tree/m\
                \aster/specifications/mnemonic/english.txt"

        it "early error reported first (Invalid Entropy)" $ do
            let res = fromMnemonic @'[15,18,21] @"testing"
                        [ "glimpse", "paper", "toward", "fine", "alert"
                        , "baby", "pyramid", "alone", "shaft", "force"
                        , "circle", "fancy", "squeeze", "cannon", "toilet"
                        ]
            res `shouldBe` Left (FromMnemonicError "Invalid entropy checksum: \
                \please double-check the last word of your mnemonic sentence.")

        it "early error reported first (Non-English Word)" $ do
            let res = fromMnemonic @'[15,18,21] @"testing"
                        [ "baguette", "paper", "toward", "fine", "alert"
                        , "baby", "pyramid", "alone", "shaft", "force"
                        , "circle", "fancy", "squeeze", "cannon", "toilet"
                        ]
            res `shouldBe` Left (FromMnemonicError (noInDictErr "baguette"))

        it "early error reported first (Wrong number of words - 1)" $ do
            let res = fromMnemonic @'[15,18,21] @"testing"
                        ["mom", "unveil", "slim", "abandon"
                        , "nut", "cash", "laugh", "impact"
                        , "system", "split", "depth", "sun"
                        ]
            res `shouldBe` Left (FromMnemonicError "Invalid number of words: \
                \15, 18 or 21 words are expected.")

        it "early error reported first (Wrong number of words - 2)" $ do
            let res = fromMnemonic @'[15] @"testing"
                        ["mom", "unveil", "slim", "abandon"
                        , "nut", "cash", "laugh", "impact"
                        , "system", "split", "depth", "sun"
                        ]
            res `shouldBe` Left (FromMnemonicError "Invalid number of words: \
                \15 words are expected.")

        it "early error reported first (Error not in first constructor)" $ do
            let res = fromMnemonic @'[15,18,21,24] @"testing"
                        ["盗", "精", "序", "郎", "赋", "姿", "委", "善", "酵"
                        ,"祥", "赛", "矩", "蜡", "注", "韦", "效", "义", "冻"
                        ]
            res `shouldBe` Left (FromMnemonicError (noInDictErr "盗"))

        it "early error reported first (Error not in first constructor)" $ do
            let res = fromMnemonic @'[12,15,18] @"testing"
                        ["盗", "精", "序", "郎", "赋", "姿", "委", "善", "酵"
                        ,"祥", "赛", "矩", "蜡", "注", "韦", "效", "义", "冻"
                        ]
            res `shouldBe` Left (FromMnemonicError (noInDictErr "盗"))

        it "successfully parse 15 words in [15,18,21]" $ do
            let res = fromMnemonic @'[15,18,21] @"testing"
                        ["cushion", "anxiety", "oval", "village", "choose"
                        , "shoot", "over", "behave", "category", "cruise"
                        , "track", "either", "maid", "organ", "sock"
                        ]
            res `shouldSatisfy` isRight

        it "successfully parse 15 words in [12,15,18]" $ do
            let res = fromMnemonic @'[12,15,18] @"testing"
                        ["cushion", "anxiety", "oval", "village", "choose"
                        , "shoot", "over", "behave", "category", "cruise"
                        , "track", "either", "maid", "organ", "sock"
                        ]
            res `shouldSatisfy` isRight

        it "successfully parse 15 words in [9,12,15]" $ do
            let res = fromMnemonic @'[9,12,15] @"testing"
                        ["cushion", "anxiety", "oval", "village", "choose"
                        , "shoot", "over", "behave", "category", "cruise"
                        , "track", "either", "maid", "organ", "sock"
                        ]
            res `shouldSatisfy` isRight

    describe "Keys storing and retrieving roundtrips" $ do
        it "XPrv ShelleyKey"
            (property $ prop_roundtripXPrv @ShelleyKey)
        it "XPrv IcarusKey"
            (property $ prop_roundtripXPrv @IcarusKey)
        it "XPrv ByronKey"
            (property $ prop_roundtripXPrv @ByronKey)
        it "XPub ShelleyKey"
            (property $ prop_roundtripXPub @ShelleyKey)
        it "XPub IcarusKey"
            (property $ prop_roundtripXPub @IcarusKey)

    describe "keyToHexText" $ do
        it "is compatible with jcli (Shelley)" $
            property $ prop_keyToHexTextJcliCompatible @ShelleyKey
        it "is compatible with jcli (Icarus)" $
            property $ prop_keyToHexTextJcliCompatible @IcarusKey
        it "is compatible with jcli (Byron)" $
            property $ prop_keyToHexTextJcliCompatible @ByronKey

{-------------------------------------------------------------------------------
                               Properties
-------------------------------------------------------------------------------}

prop_succMaxBoundHardIx :: Property
prop_succMaxBoundHardIx = expectFailure $
    property $ succ (maxBound @(Index 'Hardened _)) `seq` ()

prop_predMinBoundHardIx :: Property
prop_predMinBoundHardIx = expectFailure $
    property $ pred (minBound @(Index 'Hardened _)) `seq` ()

prop_succMaxBoundSoftIx :: Property
prop_succMaxBoundSoftIx = expectFailure $
    property $ succ (maxBound @(Index 'Soft _)) `seq` ()

prop_predMinBoundSoftIx :: Property
prop_predMinBoundSoftIx = expectFailure $
    property $ pred (minBound @(Index 'Soft _)) `seq` ()

prop_roundtripEnumIndexHard :: Index 'WholeDomain 'AccountK -> Property
prop_roundtripEnumIndexHard ix =
    (toEnum . fromEnum) ix === ix .&&. (toEnum . fromEnum . getIndex) ix === ix

prop_roundtripEnumIndexSoft :: Index 'Soft 'AddressK -> Property
prop_roundtripEnumIndexSoft ix =
    (toEnum . fromEnum) ix === ix .&&. (toEnum . fromEnum . getIndex) ix === ix

prop_roundtripXPrv
    :: (PersistPrivateKey (k 'RootK), Eq (k 'RootK XPrv), Show (k 'RootK XPrv))
    => (k 'RootK XPrv, Hash "encryption")
    -> Property
prop_roundtripXPrv xpriv = do
    let xpriv' = (unsafeDeserializeXPrv . serializeXPrv) xpriv
    xpriv' === xpriv

prop_roundtripXPub
    ::  ( PersistPublicKey (k 'AccountK)
        , Eq (k 'AccountK XPub)
        , Show (k 'AccountK XPub)
        )
    => k 'AccountK XPub
    -> Property
prop_roundtripXPub xpub = do
    let xpub' = (unsafeDeserializeXPub . serializeXPub) xpub
    xpub' === xpub

prop_passphraseRoundtrip
    :: Passphrase "encryption"
    -> Property
prop_passphraseRoundtrip pwd = monadicIO $ liftIO $ do
    hpwd <- encryptPassphrase pwd
    checkPassphrase pwd hpwd `shouldBe` Right ()

prop_passphraseRoundtripFail
    :: (Passphrase "encryption", Passphrase "encryption")
    -> Property
prop_passphraseRoundtripFail (p, p') =
    p /= p' ==> monadicIO $ liftIO $ do
        hp <- encryptPassphrase p
        checkPassphrase p' hp `shouldBe` Left ErrWrongPassphrase

prop_passphraseHashMalformed
    :: Passphrase "encryption"
    -> Property
prop_passphraseHashMalformed pwd = monadicIO $ liftIO $ do
    checkPassphrase pwd (Hash mempty) `shouldBe` Left ErrWrongPassphrase

prop_keyToHexTextJcliCompatible
    :: WalletKey k
    => Unencrypted (k 'RootK XPrv)
    -> Property
prop_keyToHexTextJcliCompatible (Unencrypted k) = monadicIO $ do
    let hexXPrv = B8.unpack . hex . unXPrvStripPub . getRawKey $ k
    monitor (counterexample $ "\nkey bytes = " ++ hexXPrv)
    (code, stdout, stderr) <- run $ jcliKeyFromHex hexXPrv
    monitor (counterexample $ "\n" ++ show code)
    monitor (counterexample $ "Stdout: " ++ show stdout)
    monitor (counterexample $ "Stderr: " ++ show stderr)
    assert (stderr == "")
  where
    jcliKeyFromHex = readProcessWithExitCode
        "jcli"
        ["key", "from-bytes", "--type", "ed25519bip32"]

{-------------------------------------------------------------------------------
                             Arbitrary Instances
-------------------------------------------------------------------------------}

instance Arbitrary (Index 'Soft 'AddressK) where
    shrink _ = []
    arbitrary = arbitraryBoundedEnum

instance Arbitrary (Index 'Hardened 'AccountK) where
    shrink _ = []
    arbitrary = arbitraryBoundedEnum

instance Arbitrary (Index 'WholeDomain 'AddressK) where
    shrink _ = []
    arbitrary = arbitraryBoundedEnum

instance Arbitrary (Index 'WholeDomain 'AccountK) where
    shrink _ = []
    arbitrary = arbitraryBoundedEnum

instance (PassphraseMaxLength purpose, PassphraseMinLength purpose) =>
    Arbitrary (Passphrase purpose) where
    arbitrary = do
        n <- choose (passphraseMinLength p, passphraseMaxLength p)
        bytes <- T.encodeUtf8 . T.pack <$> replicateM n arbitraryPrintableChar
        return $ Passphrase $ BA.convert bytes
      where p = Proxy :: Proxy purpose
    shrink (Passphrase bytes)
        | BA.length bytes <= passphraseMinLength p = []
        | otherwise =
            [ Passphrase
            $ BA.convert
            $ B8.take (passphraseMinLength p)
            $ BA.convert bytes
            ]
      where p = Proxy :: Proxy purpose

instance {-# OVERLAPS #-} Arbitrary (Passphrase "generation") where
    shrink (Passphrase "") = []
    shrink (Passphrase _ ) = [Passphrase ""]
    arbitrary = do
        n <- choose (0, 32)
        InfiniteList bytes _ <- arbitrary
        return $ Passphrase $ BA.convert $ BS.pack $ take n bytes

instance Arbitrary (Hash "encryption") where
    shrink _ = []
    arbitrary = do
        InfiniteList bytes _ <- arbitrary
        return $ Hash $ BS.pack $ take 32 bytes

-- Necessary unsound Show instance for QuickCheck failure reporting
instance Show XPrv where
    show = show . unXPrv

-- Necessary unsound Eq instance for QuickCheck properties
instance Eq XPrv where
    a == b = unXPrv a == unXPrv b

instance Arbitrary (ShelleyKey 'RootK XPrv) where
    shrink _ = []
    arbitrary = genRootKeysSeqWithPass $ genPassphrase (0, 16)

instance Arbitrary (ShelleyKey 'AccountK XPub) where
    shrink _ = []
    arbitrary = publicKey <$> genRootKeysSeqWithPass (genPassphrase (0, 16))

instance Arbitrary (ShelleyKey 'RootK XPub) where
    shrink _ = []
    arbitrary = publicKey <$> arbitrary

instance Arbitrary (ByronKey 'RootK XPrv) where
    shrink _ = []
    arbitrary = genRootKeysRndWithPass $ genPassphrase (0, 16)

instance Arbitrary (IcarusKey 'RootK XPrv) where
    shrink _ = []
    arbitrary = genRootKeysIcaWithPass $ genPassphrase (0, 16)

instance Arbitrary (IcarusKey 'AccountK XPub) where
    shrink _ = []
    arbitrary = publicKey <$> genRootKeysIcaWithPass (genPassphrase (0, 16))


instance Arbitrary NetworkDiscriminant where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

newtype Unencrypted a = Unencrypted a
    deriving (Eq, Show)

instance Arbitrary (Unencrypted (ShelleyKey 'RootK XPrv)) where
    shrink _ = []
    arbitrary = Unencrypted <$> genRootKeysSeqWithPass (pure mempty)

instance Arbitrary (Unencrypted (ByronKey 'RootK XPrv)) where
    shrink _ = []
    arbitrary = Unencrypted <$> genRootKeysRndWithPass (pure mempty)

instance Arbitrary (Unencrypted (IcarusKey 'RootK XPrv)) where
    shrink _ = []
    arbitrary = Unencrypted <$> genRootKeysIcaWithPass (pure mempty)

genRootKeysSeqWithPass
    :: Gen (Passphrase "encryption")
    -> Gen (ShelleyKey depth XPrv)
genRootKeysSeqWithPass encryptionPass = do
    (s, g, e) <- (,,)
        <$> genPassphrase @"seed" (16, 32)
        <*> genPassphrase @"generation" (0, 16)
        <*> encryptionPass
    return $ Seq.unsafeGenerateKeyFromSeed (s, g) e

genRootKeysRndWithPass :: Gen (Passphrase "encryption") -> Gen (ByronKey 'RootK XPrv)
genRootKeysRndWithPass encryptionPass = Rnd.generateKeyFromSeed
    <$> genPassphrase @"seed" (16, 32)
    <*> encryptionPass

genRootKeysIcaWithPass
    :: Gen (Passphrase "encryption")
    -> Gen (IcarusKey depth XPrv)
genRootKeysIcaWithPass encryptionPass = Ica.unsafeGenerateKeyFromSeed
    <$> genPassphrase @"seed" (16, 32)
    <*> encryptionPass

genPassphrase :: (Int, Int) -> Gen (Passphrase purpose)
genPassphrase range = do
    n <- choose range
    InfiniteList bytes _ <- arbitrary
    return $ Passphrase $ BA.convert $ BS.pack $ take n bytes

genAddress
    :: forall (network :: NetworkDiscriminant). (KnownNetwork network)
    => Gen Address
genAddress = oneof
    [ (\bytes -> Address (BS.pack (addrSingle @network:bytes)))
        <$> vectorOf Seq.publicKeySize arbitrary
    , (\bytes -> Address (BS.pack (addrGrouped @network:bytes)))
        <$> vectorOf (2*Seq.publicKeySize) arbitrary
    , (\bytes -> Address (BS.pack (addrAccount @network:bytes)))
        <$> vectorOf Seq.publicKeySize arbitrary
    ]

genLegacyAddress :: (Int, Int) -> Gen Address
genLegacyAddress range = do
    n <- choose range
    let prefix = BS.pack
            [ 130       -- Array(2)
            , 216, 24   -- Tag 24
            , 88, fromIntegral n -- Bytes(n), n > 23 && n < 256
            ]
    addrPayload <- BS.pack <$> vectorOf n arbitrary
    let crc = BS.pack [26,1,2,3,4]
    return $ Address (prefix <> addrPayload <> crc)
