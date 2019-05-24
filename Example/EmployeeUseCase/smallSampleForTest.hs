module Example.EmployeeUseCase.SmallSampleForTest where

import Database.HDBC 

import VDB.Translations.VSqlToAlgebra
import VDB.SQL
import VDB.Algebra
import VDB.Name 
import VDB.FeatureExpr 
-- import VDB.Condition 
import VDB.Variational
-- import qualified VDB.Value as V
import VDB.Variational
import VDB.Schema
import VDB.Config
import qualified VDB.Condition as C
import VDB.Type


-- import VDB.Example.EmployeeUseCase.EmployeeSchema
-- import VDB.Example.EmployeeUseCase.EmployeeVSchema
import Example.EmployeeUseCase.EmployeeQuery
import Example.EmployeeUseCase.EmployeeVQuery
import Example.EmployeeUseCase.EmployeeVSchema
import Example.EmployeeUseCase.EmployeeSchema
import Example.SmartConstructor

import VDB.TypeSystem.Semantics
import qualified Data.Map as M 
import Data.SBV

import Prelude hiding (Ordering(..))
-- featureExpr rom VDB.Example.EmployeeUseCase.EmployeeVSchema
v1,v2,v3,v4,v5 :: FeatureExpr
v1 = Ref (Feature "v1")
v2 = Ref (Feature "v2")
v3 = Ref (Feature "v3")
v4 = Ref (Feature "v4")
v5 = Ref (Feature "v5")

qualifedOptAttribute :: FeatureExpr -> String -> String -> Opt Attribute
qualifedOptAttribute f relName attrName = (f, Attribute (Just (Relation relName)) attrName)

qualifedAttribute :: String -> String -> Attribute
qualifedAttribute relName attrName = Attribute (Just (Relation relName)) attrName

unQualifedAttribute :: String -> Attribute 
unQualifedAttribute attrName = Attribute Nothing attrName
-- | simple Schema 
tests1 :: Schema 
tests1 = ( v1, s1RelMap)

s1RelMap :: M.Map Relation (Opt RowType)
s1RelMap = constructRelMap [ ("T1",  [ ("A1",  TInt32), ("A2", TString)])]
-- s2^v2 = {T1(A1,A3,A4), T2(A4)}
tests2 :: Schema 
tests2 = ( v2, s2RelMap)


s2RelMap :: M.Map Relation (Opt RowType)
s2RelMap = constructRelMap [ ("T1",  [ ("A1",  TInt32), ( "A3",  TString)])
                           , ( "T2", [ ("A4", TInt32)])]


-- | simple query
testq1,testq2, testq3, testq4, testq5 :: Algebra

-- SELECT A1 FROM T1
testq1 = Proj [plainAttr "A1" ] $ TRef (Relation "T1")

-- SELECT A2 FROM T2 Where A2 > 5
testq2 =  Proj [plainAttr "A2"] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))

-- SELECT A1, A2 FROM T2 Where A2 > 5
testq2' = Proj [plainAttr "A1",plainAttr "A2" ] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))


-- SELECT A3 FROM T3
testq3 = Proj [plainAttr "A3" ] $ TRef (Relation "T3")

-- (SELECT A1 FROM T2) Union (SELECT A1 FROM T3)
testq4 = SetOp Prod l r 
        where l = Proj [plainAttr "A1" ] $ TRef (Relation "T2")
              r = Proj [plainAttr "A1" ] $ TRef (Relation "T3")

-- SELECT * FROM D,E
testq5 = SetOp Prod (TRef (Relation "D")) (TRef (Relation "E"))

testq6 = SetOp Prod testq2 testq2

-- SELECT A1, A2 FROM T2 Where A2 > 5
testqOneCond = Proj [plainAttr "A1",plainAttr "A2" ] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))



testqAndCond = Proj [plainAttr "A1",plainAttr "A2" ] $ Sel (C.And cond1 cond2) $ TRef (Relation "T2")
         where cond1 = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))
               cond2 = C.Comp LT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 100))
