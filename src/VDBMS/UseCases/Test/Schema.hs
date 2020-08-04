 -- | An example schema 
module VDBMS.UseCases.Test.Schema where

import VDBMS.Features.FeatureExpr.FeatureExpr
import qualified VDBMS.VDB.Name as N 
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Value.Value
import VDBMS.QueryLang.RelAlg.Variational.SmartConstructor
import VDBMS.VDB.Schema.Relational.Types
import VDBMS.Features.Config (Config)
import VDBMS.Variational.Opt

import Data.Map.Strict

-- 
--  * Features
-- 
fone, ftwo, fthree, ffour, ffive :: Feature
fone = Feature "f1"
ftwo = Feature "f2"
fthree = Feature "f3"
ffour = Feature "f4"
ffive = Feature "f5"

fs :: [Feature]
fs = [fone, ftwo, fthree, ffour, ffive]

feone, fetwo, fethree, fefour, fefive :: FeatureExpr
feone = Ref fone 
fetwo = Ref ftwo
fethree = Ref fthree
fefour = Ref ffour
fefive = Ref ffive

-- 
-- * configurations of variants
-- 
ctwo, ctwofour, ctwofive, cthree, cthreefour, cthreefive :: Config Bool
ctwo (Feature "f1") = False
ctwo (Feature "f2") = True
ctwo (Feature "f3") = False
ctwo (Feature "f4") = False
ctwo (Feature "f5") = False
ctwo _ = False

-- 
ctwofour (Feature "f1") = True
ctwofour (Feature "f2") = True
ctwofour (Feature "f3") = False
ctwofour (Feature "f4") = True
ctwofour (Feature "f5") = False
ctwofour _ = False

-- 
ctwofive (Feature "f1") = True
ctwofive (Feature "f2") = True
ctwofive (Feature "f3") = False
ctwofive (Feature "f4") = False
ctwofive (Feature "f5") = True
ctwofive _ = False

-- 
cthree (Feature "f1") = False
cthree (Feature "f2") = False
cthree (Feature "f3") = True
cthree (Feature "f4") = False
cthree (Feature "f5") = False
cthree _ = False

-- 
cthreefour (Feature "f1") = True
cthreefour (Feature "f2") = False
cthreefour (Feature "f3") = True
cthreefour (Feature "f4") = True
cthreefour (Feature "f5") = False
cthreefour _ = False

-- 
cthreefive (Feature "f1") = True
cthreefive (Feature "f2") = False
cthreefive (Feature "f3") = True
cthreefive (Feature "f4") = False
cthreefive (Feature "f5") = True
cthreefive _ = False

cs :: [Config Bool]
cs = [ctwo, ctwofour, ctwofive, cthree, cthreefour, cthreefive]

-- 
-- * Feature models
-- 
fmone, fmtwo, fmthree :: FeatureExpr
fmone = Lit True
-- fm2 = (¬f1 ∧ (f2 ⊕ f3)) ∨ (f1 ∧ (f2 ⊕ f3) ∧ (f4 ⊕ f5))
fmtwo = Or 
  (And (Not feone) 
       ((fetwo `And` Not fethree) `Or` (Not fetwo `And` fethree)))
  (And feone (And ((fetwo `And` Not fethree) `Or` (Not fetwo `And` fethree))
                  ((fefour `And` Not fefive) `Or` (Not fefour `And` fefive))))
-- fm3 = f1 ∨ ... ∨ f5
fmthree = disjFexp [feone, fetwo, fethree, fefour, fefive]

-- 
-- * Attributes
-- 
aone_, atwo_, athree_, afour_, afive_ :: N.Attribute
asix_, aseven_, aeight_, anine_, aten_ :: N.Attribute
aone_ = N.Attribute "a1"
atwo_ = N.Attribute "a2"
athree_ = N.Attribute "a3"
afour_ = N.Attribute "a4"
afive_ = N.Attribute "a5"
asix_ = N.Attribute "a6"
aseven_ = N.Attribute "a7"
aeight_ = N.Attribute "a8"
anine_ = N.Attribute "a9"
aten_ = N.Attribute "a10"

aone, atwo, athree, afour, afive :: N.Attr
-- asix, aseven, aeight, anine, aten :: N.Attr
aone = att2attr aone_
atwo = att2attr atwo_
athree = att2attr athree_
afour = att2attr afour_
afive = att2attr afive_
asix = att2attr asix_
aseven = att2attr aseven_
aeight = att2attr aeight_
anine = att2attr anine_
aten = att2attr aten_

-- 
-- * Relations
-- 
rone, rtwo, rthree, rfour, rfive, rsix :: N.Relation
rone = N.Relation "r1"
rtwo = N.Relation "r2"
rthree = N.Relation "r3"
rfour = N.Relation "r4"
rfive = N.Relation "r5"
rsix = N.Relation "r6"

rsone, rstwo, rsthree, rsfour, rsfive, rssix :: TableSchema
-- r1(a1, a2)
rsone = mkOpt (Lit True)
  $ constructRowType [(aone_, TInt32), (atwo_, TInt32)]
-- r2(a1, a3^(¬f2), a4^(f2 ∧ f3), a5^f2)^(¬f1 ∧ (f2 ∨ f3))
rstwo = mkOpt (Not feone `And` (Or fetwo fethree))
  $ constructOptRowType [(Lit True, aone_, TInt32)
    , (Not fetwo, athree_, TInt32)
    , (And fetwo fethree, afour_, TInt32)
    , (fetwo, afive_, TInt32)]
-- r3(a1, a7^f4, a8^f5)^(f1 ∧ (f4 ∨ f5))
rsthree = mkOpt (And feone (Or fefour fefive))
  $ constructOptRowType [(Lit True, aone_, TInt32)
    , (fefour, aseven_, TInt32)
    , (fefive, aeight_, TInt32)]
-- r4(a1^f1, a6)
rsfour = mkOpt (Lit True)
  $ constructOptRowType [(feone, aone_, TInt32)
    , (Lit True, asix_, TInt32)]
-- r5(a1, a9)^f1
rsfive = mkOpt feone
  $ constructRowType [(aone_, TInt32), (anine_, TInt32)]
-- r6(a1, a10)^(¬f1)
rssix = mkOpt (Not feone)
  $ constructRowType [(aone_,TInt32), (aten_, TInt32)]

-- 
-- * schemas
-- 
schemaMap :: (Map N.Relation TableSchema)
schemaMap = fromList [(rone, rsone), (rtwo, rstwo), (rthree, rsthree)
                     ,(rfour, rsfour), (rfive, rsfive), (rsix, rssix)]

sone, stwo, sthree, sone', stwo', sthree' :: Schema
sone = ((fs, cs), mkOpt fmone schemaMap)
stwo = ((fs, cs), mkOpt fmtwo schemaMap)
sthree = ((fs, cs), mkOpt fmthree schemaMap)
sone' = ((fs, tail cs), mkOpt fmone schemaMap)
stwo' = ((fs, tail cs), mkOpt fmtwo schemaMap)
sthree' = ((fs, tail cs), mkOpt fmthree schemaMap)

