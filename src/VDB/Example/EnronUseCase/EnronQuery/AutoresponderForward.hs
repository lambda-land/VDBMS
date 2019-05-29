module VDB.Example.EnronUseCase.EnronQuery.AutoresponderForward where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 13. interaction between autoresponder with forwardmsg 
-- 
-- * Situdation: Bob sets up forwarding to rjh. Rjh has autoresponse enbaled.
--   A third party sends a message to Bob, which s forward to rjh/
--   autoresponse is sent back to Bob and then forwarded to rjh. Thus, msg arriving at rjh via
--   Bob are no effectively autoresponded. 
-- 
-- * Fix with VDB: manipulate header line, that is, leave the Sender line intact, make the autoresponder 
--   reply to the originator of the message instead of the forwarder.
--   All queries happends when we call forward function 
-- 
--   - forwardmsg AND autoresponder => Q1: forward with intact sender info and auto reply to original sender 
--   - forwardmsg AND (NOT autoresponder) => Q2: normal query with forward  
--   - (NOT forwardmsg) AND autoresponder => Nothing
--   - (NOT forwardmsg) AND (NOT autoresponder) => Nothing
-- * V-Query: forwardmsg <autoresponder <Q1,Q2>, Nothing>


enronVQ13 :: Algebra
enronVQ13 = AChc forwardmsg (AChc autoresponder u13_Q1 u13_Q2) Empty

u13_Q1 :: Algebra
u13_Q1 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_message", "subject"), ("v_forward_msg", "forwardAddr")]) 
        $ Sel cond 
        $ joinForwardEmpRecMsg
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue
                          cond = C.And joinForwardEmpRecMsgCond cond1

u13_Q2 :: Algebra
u13_Q2 = Proj (map trueAtt $ genQAtts [("v_recipientinfo", "rvalue"), ("v_message", "subject"), ("v_forward_msg", "forwardAddr")]) 
        $ Sel cond 
        $ joinForwardEmpRecMsg
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue
                          cond = C.And joinForwardEmpRecMsgCond cond1

-- | translated Query for interaction between forwardmsg and autoresponder

-- (SELECT  msg.sender as originator,  rec.rvalue as receipientAddr, msg.subject, forwardAddr, concat ("forwardmsg", " AND ", "autoresponder") as presCond
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138 )

-- union all 

-- (SELECT  NULL as originator, rec.rvalue as receipientAddr, msg.subject, forwardAddr, concat (" forwardmsg", " AND ", "(NOT autoresponder)") as presCond
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138	)

