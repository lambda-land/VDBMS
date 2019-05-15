 -- | Example Queries upon Enron Email Database
module VDB.Example.EnronUseCase.EnronQuery where

import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import Database.HDBC
import VDB.Type
import Prelude hiding (Ordering(..))
import Data.Time

import VDB.Example.SmartConstructor

-- | the message id value we choose for entire use case
midValue :: C.Atom
midValue = (C.Val (SqlInt32 9138))

-- | All Feautres
encrypt, autoresponder :: F.FeatureExpr
encrypt = F.Ref $ Feature "encrypt"
autoresponder = F.Ref $ Feature "autoresponder"


-- | Table reference 
v_employee, v_message, v_recipientinfo, v_auto_msg :: Algebra
v_employee = TRef (Relation "v_employee")
v_message = TRef (Relation "v_message")
v_recipientinfo = TRef (Relation "v_recipientinfo")
v_auto_msg = TRef (Relation "v_auto_msg")

-- 
-- 1. interaction between autoresponder with encrypt
-- 
-- * Situdation: Bob send an encrypted message to Jack who successfully decrypt it,
--   and who has his autoreponder provisioned (but Jack has no encrypt key for Bob provisioned).
-- * Fix with VDB: use presence condition to prevent such situation happen.
--   - encrypt AND autoresponder => Q1: reply with autorespond subject and body, 
--                                      but doesn't contain any decrypted content
--   - encrypt AND (NOT autoresponder) => Nothing 
--   - (NOT encrypt) AND autoresponder => Q3: reply with autorespond subject and body 
--                                            and the original subject (Re:XXX)
--   - (NOT encrypt) AND (NOT autoresponder) => Nothing
-- * V-Query: autoresponder <encrypt <Q1,Q3>, Empty>


enronVQ1 :: Algebra
enronVQ1 = AChc autoresponder (AChc encrypt u1_Q1 u1_Q3) (Empty)

u1_Q1 :: Algebra
u1_Q1 = Proj (map trueAtt $ genQAtts [("v_auto_msg", "subject"), ("v_auto_msg", "body")]) 
        $ Sel cond 
        $ joinRecEmpAuto
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_recipientinfo","mid"))) midValue
                          cond = C.And joinRecEmpAutoCond cond1

u1_Q3 :: Algebra
u1_Q3 = Proj (map trueAtt $ genQAtts [("v_message", "subject"), ("v_auto_msg", "subject"), ("v_auto_msg", "body")]) 
        $ Sel cond 
        $ SetOp Prod (TRef (Relation "v_message")) $ joinRecEmpAuto
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_recipientinfo","mid"))) midValue
                          cond2 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue
                          cond = C.And joinRecEmpAutoCond $ C.And cond1 cond2

joinRecEmpAuto :: Algebra
joinRecEmpAuto = SetOp Prod (TRef (Relation "v_recipientinfo")) $ SetOp Prod v_employee v_auto_msg

joinRecEmpAutoCond :: C.Condition
joinRecEmpAutoCond = C.And cond1 cond2                 
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_recipientinfo","rvalue"))) (C.Attr (genQAtt ("v_employee","email_id")))
                          cond2 = C.Comp EQ (C.Attr (genQAtt ("v_employee","eid"))) (C.Attr (genQAtt ("v_auto_msg","eid")))




