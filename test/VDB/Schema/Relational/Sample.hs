module VDB.Schema.Relational.Sample where 

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Type

import Data.Map.Strict

-- | sample relational schema. 
sampleRSch :: RSchema 
sampleRSch = fromList [rs,ss,ys,zs,ts]

r,s,y,t,z,miss :: Relation
a,b,c,d,e,f :: Attribute
rs,ss,ys,zs,ts :: (Relation, Map Attribute SqlType)

-- | missing relation
miss = Relation "Miss"

-- | relation R(A: int32).
r = Relation "R"
a = Attribute "A"
rs = (r, fromList [(a, TInt64)])

-- | relation S(A: int32,B: string).
s = Relation "S"
b = Attribute "B"
ss = (s, fromList [ (a, TInt64)
                  , (b, TString)])

-- | relation Y(B: byte string,F: bool).
y = Relation "Y"
f = Attribute "F"
ys = (y, fromList [ (b, TByteString)
                  , (f, TBool)])

-- | relation Z(C: int32, A: int32)
z = Relation "Z"
zs = (z, fromList [ (c, TInt64)
                  , (a, TInt64)])

-- | relation T(C: int32, D: int32, E: int32)
t = Relation "T"
c = Attribute "C"
d = Attribute "D"
e = Attribute "E"
ts = (t, fromList [ (c, TInt64)
                  , (d, TInt64)
                  , (e, TInt64)])

