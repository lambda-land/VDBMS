module VDB.Schema.Test where 

-- import Databases.Schemas.Test1

-- import VDBMS.VDB.Variational.Schema
-- import VDB.Variant 
-- import VDB.Config 

-- import Test.Tasty
-- -- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
-- import Test.Tasty.HUnit

-- import Debug.Trace (trace)

-- import Data.Bifunctor (bimap)

-- import Data.List
-- import Data.Ord

-- main = defaultMain tests

-- tests :: TestTree
-- tests = testGroup "Tests" [properties, unitTests]

-- properties :: TestTree
-- properties = testGroup "Properties" [qcProps]


-- qcProps = testGroup "(checked by QuickCheck)"
--   [ QC.testProperty "sort == sort . reverse" $
--       \list -> sort (list :: [Int]) == sort (reverse list)
--   , QC.testProperty "Fermat's little theorem" $
--       \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
--   -- the following property does not hold
--   , QC.testProperty "Fermat's last theorem" $
--       \x y z n ->
--         (n :: Integer) >= 3 QC.==> x^n + y^n /= (z^n :: Integer)
--   ]

-- ?=? means is equivalent to.
-- unitTests = testGroup "Schema: Unit tests"
--   [schEqTest]

-- schEqTest = testCase "configed test1 database schema ?=? variants schemas" $
--   assertBool "WhAt!!!" $ 
--   compareSchs test1confs test1sch [test1v1sch, test1v2sch]

-- | compares a list of variant schemas with the list of variant
--   schemas generated by configuring the varitional schema.
-- compareSchs :: [Config Bool] -> Schema -> [VariantSchema] -> Bool
-- compareSchs cs vs ss = trace ("\n" ++ show x ++ "\n" ++ show y ++ "\n") $ x == y
--     where
--       confedss = [mkVariant (appConfSchema' c vs) c | c <- cs]
--       comp = fmap (bimap id (\x -> fmap x test1features))
--       x = comp confedss
--       y = comp ss

