module VDB.Example.EnronUseCase.EnronQuery.AutoresponderEncrypt where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 8. interaction between autoresponder with encrypt
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


enronVQ8 :: Algebra
enronVQ8 = AChc autoresponder (AChc encrypt u8_Q1 u8_Q3) (Empty)

u8_Q1 :: Algebra
u8_Q1 = Proj (map trueAtt $ genQAtts [("v_auto_msg", "subject"), ("v_auto_msg", "body")]) 
        $ Sel cond 
        $ joinRecEmpAuto
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_recipientinfo","mid"))) midValue
                          cond = C.And joinRecEmpAutoCond cond1

u8_Q3 :: Algebra
u8_Q3 = Proj (map trueAtt $ genQAtts [("v_message", "subject"), ("v_auto_msg", "subject"), ("v_auto_msg", "body")]) 
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

-- | translated Query for interaction between encrypt and autoresponder

-- (SELECT NULL as originalSubject, auto.subject as autoSubject, auto.body as autoBody, concat("encrypt", " AND ", "autoresponder") as presCond
-- FROM (v_recipientinfo rec
-- inner join v_employee emp on rec.rvalue = emp.email_id)
-- inner join v_auto_msg auto on auto.eid = emp.eid
-- Where  rec.mid = 9138)

-- union all 

-- (SELECT msg.subject as originalSubject, auto.subject as autoSubject, auto.body as autoBody, concat("(NOT encrypt)", " AND ", "autoresponder") as presCond
-- FROM (v_recipientinfo rec
-- inner join v_employee emp on rec.rvalue = emp.email_id)
-- inner join v_auto_msg auto on auto.eid = emp.eid, v_message msg
-- Where  rec.mid = 9138 and msg.mid = 9138)



