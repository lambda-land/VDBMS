module VDB.Example.EnronUseCase.EnronQuery.ForwardmsgRemail1 where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 19. interaction between forwardmsg with remail (1) 
-- 
-- * Situdation: Bob establishes a pseudonym on the remailer and 
--   provisions FORWARDMESSAGES to send to that pseudonym. 
--   Messages sent to Bob will be infinitely forwarded from Bob to remailer and back.
-- 
-- * Fix: remailer detect the loop and terminate it. Also, it must remove any header information 
--   that leak the pseudonym prior to the Non-delivery Notification
--   => Queries
--   remailmsg AND forwardmsg => Q1: get forwardAddr and psuedonym for each email_id (remailer detect the loop) 
--   remailmsg AND (NOT forwardmsg) => Nothing    
--   (NOT remailmsg) AND forwardmsg => Nothing 
--   (NOT remailmsg) AND (NOT forwardmsg) => Nothing 
-- 
-- * V-Query: forwardmsg and remailmsg <Q1, Empty>


enronVQ19 :: Algebra
enronVQ19 = AChc (forwardmsg `F.And` remailmsg) u19_Q1 Empty

u19_Q1 :: Algebra
u19_Q1 = Proj (map trueAtt $ genQAtts [("v_employee", "eid"), ("v_employee", "email_id"), ("v_forward_msg", "forwardAddr"), ("v_remail_msg", "pseudonym") ]) 
        $ Sel joinEmpForwardRemailCond 
        $ joinEmpForwardRemail

-- | Translated SQL Query of autoresponder <remailmsg<Q1,Q3>, Empty>
-- SELECT emp.eid, emp.email_id, forward.forwardAddr,remail.pseudonym, concat("forwardmsg", " AND ", " remailmsg") as presCond
-- FROM v_employee emp
-- inner join v_forward_msg forward on forward.eid = emp.eid
-- inner join v_remail_msg remail on remail.eid = emp.eid 