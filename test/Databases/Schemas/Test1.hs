-- | a small test database.
module VDB.test.Databases.Schemas.Test1 where

-- goal:
-- 1) test the translations (both our approach and brute force)
-- 2) test the optimization rules
-- 3) test config query
-- 4) test config db
-- 5) test type system
-- 6) test the commutativity diagram
-- 7) test hypothesis/properties

import VDB.FeatureExpr 
-- import VDB.Algebra
import VDB.Schema 
import VDB.Name

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M


test1f1, test1f2 :: FeatureExpr
test1f1 = Ref $ Feature "f1"
test1f2 = Ref $ Feature "f2"

test1featureModel :: FeatureExpr
test1featureModel = xor test1f1 test1f2

r, s :: Relation
r = Relation "R"
s = Relation "S"

a, b, c, d :: Attribute
a = genAtt "A"
b = Attribute r "B"
c = genAtt "C"
d = Attribute r "D"

rSch, sSch :: TableSchema
rSch = (Or test1f1 test1f2, 
  M.fromList [(addRelToAtt a r,(Lit True, TSqlInt32)),
              (b,(andNot test1f1 test1f2, TSqlInt32)),
              (addRelToAtt c r,(andNot test1f2 test1f1,TSqlInt32)),
              (d,(Lit True, TSqlInt32))])
sSch = (test1f1,
  M.fromList [(addRelToAtt a s,(Lit True, TSqlInt32)),
              (addRelToAtt c s,(Lit True,TSqlInt32))])

test1sch :: Schema
test1sch = (test1featureModel,
  M.fromList [(r,rSch), (s,sSch)])

