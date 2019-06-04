module VDB.Example.EnronUseCase.EnronQuery.AutoresponderRemailI where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 14. interaction between autoresponder with remail (1) 
-- 
-- * Situdation: Bob activate an autoresponder in his remailer account when he is on vacation.
--   Rjh can reply a msg to Bob's pseudonym which then remailMessage mails to Bob. Then
--   the autoresponder of Bob will sends a message to Rjh telling him Bob is on vacation.
--   This allows rjh to infer that the pseudonym is for Bob.
-- 
-- * Fix with VDB: the autoresponder should be altered to notice when a message arrived via the remailer
--   and then not respond to them. 
--   => 
--   remailmsg AND autoresponder => Q1: if is_remail is true, then not auto-reply msg; else auto-reply.
--   remailmsg AND (NOT autoresponder) => Nothing   
--   (NOT remailmsg) AND autoresponder => Q3. normal auto-reply
--   (NOT remailmsg) AND (NOT autoresponder) => Nothing 
-- 
-- * V-Query: autoresponder <remailmsg<Q1,Q3>, Empty>


enronVQ14 :: Algebra
enronVQ14 = AChc autoresponder (AChc remailmsg u14_Q1 u13_Q3) Empty


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

