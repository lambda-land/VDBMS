module TestTwoOptionExample where 

import Test.Tasty
import Test.Tasty.HUnit

import VDB.Translations.VSqlToAlgebra
import VDB.SQL
import VDB.Algebra
import VDB.Name 
import qualified VDB.FeatureExpr as F
import VDB.Condition 
import VDB.Variational
-- import qualified VDB.Value as V
import VDB.Variational
import VDB.Schema
import VDB.Config
-- import VDB.Value 
import VDB.Type



import VDB.Example.TwoOption
import VDB.TypeSystem.Semantics
import qualified Data.Map as Map 



-- | test the schema output from different configuration of A and B. 
--   Where A and B is the feature expression, 
--   and the underlying schema is the one from the Example.TwoOption
-- testTwoOptionExample  :: TestTree
-- testTwoOptionExample  = testGroup "Test the schema outputfrom different configuration of A and B "
--   [  
--     testGroup "1) enable all first."
--     [  testCase "enable All" $
--        do output   <- return $ semVsch twoOptionSchema (enableAll)
--           expectVal <- return $ Map.fromList [(Relation "t1", 
--                                       [ (Attribute "a2", TInt)
--                                       , (Attribute "a4", TInt)
--                                       , (Attribute "a6", TInt)
--                                       , (Attribute "a8", TInt)
--                                       , (Attribute "a10", TInt)
--                                       , (Attribute "a12", TInt)
--                                       , (Attribute "a14", TInt)
--                                       , (Attribute "a16", TInt)
--                                       ])]
--           expectVal @=? output

--     ]
--   ,  
--     testGroup "2) disable all first, then:"
--     [ testCase "enable A" $
--        do output   <- return $ semVsch twoOptionSchema (enable (Feature "A") disableAll )
--           expectVal <- return $ Map.fromList [(Relation "t1", 
--                                       [ (Attribute "a3", TInt)
--                                       , (Attribute "a4", TInt)
--                                       , (Attribute "a7", TInt)
--                                       , (Attribute "a8", TInt)
--                                       , (Attribute "a11", TInt)
--                                       , (Attribute "a12", TInt)
--                                       , (Attribute "a15", TInt)
--                                       , (Attribute "a16", TInt)
--                                       ])]
--           expectVal @=? output
--     , testCase "enable B" $
--        do output   <- return $ semVsch twoOptionSchema (enable (Feature "B") disableAll )
--           expectVal <- return $ Map.fromList [(Relation "t1", 
--                                       [ (Attribute "a5", TInt)
--                                       , (Attribute "a6", TInt)
--                                       , (Attribute "a7", TInt)
--                                       , (Attribute "a8", TInt)
--                                       , (Attribute "a13", TInt)
--                                       , (Attribute "a14", TInt)
--                                       , (Attribute "a15", TInt)
--                                       , (Attribute "a16", TInt)
--                                       ])]
--           expectVal @=? output

--     ]
    
--   ]