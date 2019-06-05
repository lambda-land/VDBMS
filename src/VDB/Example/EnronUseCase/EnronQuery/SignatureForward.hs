module VDB.Example.EnronUseCase.EnronQuery.SignatureForward where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 27. interaction between signature(virify) with forwardmessage
-- 
-- * Situdation: Bob sent a signed message to Jack's old email address which automatically forward 
--               message to new email address (hall@research). The signed message may be altered 
--               during the transition from old to new. 
--
-- * Fix with VDB: use presence condition to prevent such situation happen.
--   - signautre AND forwardmsg => Q1: query the sender, subject, body, date
--                                 (have a header for time and identity whose signature was verified)
--   - signautre AND (NOT forwardmsg) => Q2: Q1 + query on signature  
--   - (NOT signautre) AND forwardmsg => Q3: Q1 + query on forwardaddrs
--   - (NOT signautre) AND (NOT forwardmsg) => Empty
--
-- * V-Query: signature <forwardmsg <Q1,Q2>, forwardmsg <Q3,Q4>>


enronVQ27 :: Algebra
enronVQ27 = AChc signature (AChc forwardmsg u27_Q1 u27_Q2) (AChc forwardmsg u27_Q3 u27_Q4)

u27_Q1 :: Algebra
u27_Q1 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_message", "subject"),("v_message", "body"), ("v_message", "date") ]) 
        $ Sel cond 
        $ v_message
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue
                          

u27_Q2 :: Algebra
u27_Q2 =  Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_message", "subject"),("v_message", "body"), ("v_employee", "sign") ]) 
        $ Sel (C.And cond joinMsgEmpCond) 
        $ joinMsgEmp
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue

u27_Q3 :: Algebra
u27_Q3 =  Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_message", "subject"),("v_message", "body"), ("v_forward_msg", "forwardAddr") ]) 
        $ Sel (C.And cond joinForwardRecMsgEmpCond) 
        $ joinForwardEmpRecMsg
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue

u27_Q4 :: Algebra
u27_Q4 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_message", "subject"),("v_message", "body") ]) 
        $ Sel cond 
        $ v_message
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue


-- | translted query of interaction between signature and forwardmsg
-- (SELECT sender, subject, body, date, NULL as forwardAddr, concat("signature", " AND", "forwardmsg")
-- FROM v_message 
-- where mid = 9138)

-- union all 

-- (SELECT sender, subject, body, NULL as date, sign, NULL as forwardAddr, concat("signature", " AND ", "(NOT forwardmsg)")
-- FROM v_message msg
-- inner join v_employee emp on msg.sender = emp.email_id
-- where msg.mid = 9138)

-- union all 

-- (SELECT sender, subject, body, NULL as date, NULL as sign, forwardAddr, concat("(NOT signature)", " AND ", " forwardmsg")
-- FROM v_forward_msg  fmsg 
-- inner join v_employee emp on fmsg.eid = emp.eid
-- inner join v_recipientinfo rec on rec.rvalue = emp.email_id 
-- inner join v_message msg on msg.mid = rec.mid
-- where msg.mid = 9138)

-- union all 


-- (SELECT sender, subject, body, NULL as date, NULL as sign, NULL as forwardAddr, concat("(NOT signature)", " AND", "(NOT forwardmsg)")
-- FROM v_message 
-- where mid = 9138)



