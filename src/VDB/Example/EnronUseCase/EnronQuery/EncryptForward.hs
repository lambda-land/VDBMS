module VDB.Example.EnronUseCase.EnronQuery.EncryptForward where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 9. interaction between encrypt with forwardmsg
-- 
-- * Situdation: Bob sent a encrypted message to Jack's old email address which will encrypt the message 
--               and automatically forward the decrpted message to new email address (hall@research). 
--               The original encrypted message travels in the clear open network during the transition from old to new. 
--  
-- * Fix with VDB: use presence condition to prevent such situation happen.
--   Recognizes a decrypted msg and then send a notification to the following link 
--   - encrypt AND forwardmsg => Q1: get the public_key, and send the notification to forward address
--   - encrypt AND (NOT forwardmsg) => Q2:get public key to decrypt message
--   - (NOT encrypt) AND forwardmsg => Q3: get forward address 
--   - (NOT encrypt) AND (NOT forwardmsg) => Empty
--
-- * V-Query: encrypt <forwardmsg <Q1,Q2>, forwardmsg<Q3,Empty>>


enronVQ9 :: Algebra
enronVQ9 = AChc encrypt (AChc forwardmsg u9_Q1 u9_Q2) (AChc forwardmsg u9_Q3 Empty)

u9_Q1 :: Algebra
u9_Q1 = Proj (map trueAtt $ genQAtts [("v_recipientinfo", "rvalue"), ("v_employee", "public_key"),("v_forward_msg", "forwardAddr") ]) 
        $ Sel ( C.And (C.And cond1 cond2) joinForwardRecMsgEmpCond )
        $ joinForwardEmpRecMsg
        where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue
              cond2 = C.Comp NEQ (C.Attr (genQAtt ("v_employee","public_key"))) nullValue
                          

u9_Q2 :: Algebra
u9_Q2 = Proj (map trueAtt $ genQAtts [("v_recipientinfo", "rvalue"), ("v_employee", "public_key") ]) 
        $ Sel (C.And cond joinMsgEmpRecCond) 
        $ joinMsgEmpRec
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue

u9_Q3 :: Algebra
u9_Q3 = Proj (map trueAtt $ genQAtts [("v_recipientinfo", "rvalue"),("v_forward_msg", "forwardAddr")]) 
        $ Sel (C.And cond joinForwardRecMsgEmpCond) 
        $ joinForwardEmpRecMsg
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue


joinMsgEmpRec :: Algebra
joinMsgEmpRec = SetOp Prod v_message $ SetOp Prod v_employee  v_recipientinfo 

joinMsgEmpRecCond :: C.Condition
joinMsgEmpRecCond = C.And cond1 cond2
    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) (C.Attr (genQAtt ("v_recipientinfo","mid")))
          cond2 = C.Comp EQ (C.Attr (genQAtt ("v_recipientinfo","rvalue"))) (C.Attr (genQAtt ("v_employee","email_id")))

-- | same in the signatureForward 
joinForwardEmpRecMsg :: Algebra
joinForwardEmpRecMsg = SetOp Prod v_forward_msg $ SetOp Prod v_employee $ SetOp Prod v_recipientinfo v_message 

joinForwardRecMsgEmpCond :: C.Condition
joinForwardRecMsgEmpCond  = C.And cond1 $ C.And cond2 cond3
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_forward_msg","eid"))) (C.Attr (genQAtt ("v_employee","eid")))
                          cond2 = C.Comp EQ (C.Attr (genQAtt ("v_recipientinfo","rvalue"))) (C.Attr (genQAtt ("v_employee","email_id")))
                          cond3 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) (C.Attr (genQAtt ("v_recipientinfo","mid")))

-- | translted query of interaction between encrypt and forwardmsg

-- (SELECT  rec.rvalue as recipientAddr, public_key, forwardAddr, concat("encrypt", " AND", "forwardmsg") as presCond
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138 and public_key is not NULL) 

-- union all 

-- (SELECT rec.rvalue as recipientAddr, public_key, NULL as forwardAddr, concat("encrypt", " AND", "(NOT forwardmsg)") as presCond
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- where msg.mid = 9138)

-- union all 

-- (SELECT  rec.rvalue as recipientAddr, NULL as public_key, forwardAddr, concat("(NOT encrypt)", " AND", "forwardmsg") as presCond
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138)


