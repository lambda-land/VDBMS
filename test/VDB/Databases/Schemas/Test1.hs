-- | a small test database.
module VDB.Databases.Schemas.Test1 where

-- goal:
-- 1) test the translations (both our approach and brute force)
-- 2) test the optimization rules
-- 3) test config query
-- 4) test config db
-- 5) test type system
-- 6) test the commutativity diagram
-- 7) test hypothesis/properties

-- import VDBMS.Features.FeatureExpr.FeatureExpr
-- -- import VDB.Algebra
-- import VDBMS.VDB.Schema.Variational.Schema
-- import VDBMS.VDB.Name
-- import VDBMS.DBMS.Value.Value
-- import VDBMS.Features.Config
-- import VDB.Variant

-- import Data.Map.Strict (Map)
-- import qualified Data.Map.Strict as M


-- test1f1, test1f2 :: FeatureExpr
-- test1f1 = Ref $ Feature "f1"
-- test1f2 = Ref $ Feature "f2"

-- test1featureModel :: FeatureExpr
-- test1featureModel = xor test1f1 test1f2

-- r, s :: Relation
-- r = Relation "R"
-- s = Relation "S"

-- a, b, c, d :: Attribute
-- a = genAtt "A"
-- b = Attribute (Just r) "B"
-- c = genAtt "C"
-- d = Attribute (Just r) "D"
-- p = genAtt "presCond"

-- rSch, sSch :: TableSchema
-- rSch = (Or test1f1 test1f2, 
--   M.fromList [(addRelToAtt a r,(Lit True, TInt32)),
--               (b,(andNot test1f1 test1f2, TInt32)),
--               (addRelToAtt c r,(andNot test1f2 test1f1,TInt32)),
--               (d,(Lit True, TInt32)),
--               (addRelToAtt p r,(Lit True, TByteString))])
-- sSch = (test1f1,
--   M.fromList [(addRelToAtt a s,(Lit True, TInt32)),
--               (addRelToAtt c s,(Lit True,TInt32)),
--               (addRelToAtt p s,(Lit True, TByteString))])

-- test1sch :: Schema
-- test1sch = (test1featureModel,
--   M.fromList [(r,rSch), (s,sSch)])

-- test1v1sch,test1v2sch :: VariantSchema
-- test1v1sch = ((Lit True, 
--   M.fromList [(r,(Lit True, M.fromList [(addRelToAtt a r,(Lit True, TInt32)),
--                                         (b,(Lit True, TInt32)),
--                                         (d,(Lit True, TInt32))])),
--               (s,(Lit True, M.fromList [(addRelToAtt a s,(Lit True, TInt32)),
--                                         (addRelToAtt c s,(Lit True,TInt32))]))]),
--   enable (Feature "f1") test1initConf)
-- test1v2sch = ((Lit True, 
--   M.fromList [(r,(Lit True, M.fromList [(addRelToAtt a r,(Lit True, TInt32)),
--                                         (b,(Lit True, TInt32)),
--                                         (addRelToAtt c r,(Lit True,TInt32)),
--                                         (d,(Lit True, TInt32))]))]),
--   enable (Feature "f2") test1initConf)

-- test1initConf :: Config Bool
-- test1initConf = disableAll

-- test1confs :: [Config Bool]
-- test1confs = [enable (Feature "f1") test1initConf, 
--               enable (Feature "f2") test1initConf]

-- test1features :: [Feature]
-- test1features = [Feature "f1", Feature "f2"]