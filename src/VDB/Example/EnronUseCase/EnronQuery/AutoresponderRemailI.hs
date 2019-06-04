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
--   remailmsg AND autoresponder => Q1: if is_remail is False, then auto-reply; else do not auto-reply msg; 
--   remailmsg AND (NOT autoresponder) => Nothing   
--   (NOT remailmsg) AND autoresponder => Q3. normal auto-reply
--   (NOT remailmsg) AND (NOT autoresponder) => Nothing 
-- 
-- * V-Query: autoresponder <remailmsg<Q1,Q3>, Empty>


enronVQ14 :: Algebra
enronVQ14 = AChc autoresponder (AChc remailmsg u14_Q1 u14_Q3) Empty


u14_Q1 :: Algebra
u14_Q1 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_message", "subject"), ("v_auto_msg", "subject"), ("v_auto_msg", "body") ]) 
        $ Sel cond 
        $ joinAutoEmpRecMsg
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValueFromRemailer
                    	  cond2 = C.Comp EQ (C.Attr (genQAtt ("v_message","is_from_remailer"))) falseValue
                          cond =C.And (C.And joinAutoEmpRecMsgCond cond1) cond2

u14_Q3 :: Algebra
u14_Q3 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_message", "subject"), ("v_auto_msg", "subject"), ("v_auto_msg", "body") ]) 
        $ Sel cond 
        $ joinAutoEmpRecMsg
                    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValueFromRemailer
                          cond = C.And joinAutoEmpRecMsgCond cond1

-- | Translated SQL Query of autoresponder <remailmsg<Q1,Q3>, Empty>

-- (SELECT msg.sender as sendTo, msg.subject as re, auto.subject,  auto.body, concat ("remailmsg", " AND ", "autoresponder") as presCond
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id
-- inner join v_auto_msg auto on auto.eid = emp.eid
-- Where  msg.mid =  1082 and msg.is_from_remailer = False  )

-- union all 

-- (SELECT msg.sender as sendTo, msg.subject as re, auto.subject,  auto.body, concat ("NOT remailmsg", " AND ", "autoresponder") as presCond
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id
-- inner join v_auto_msg auto on auto.eid = emp.eid
-- Where  msg.mid =  1082 )
