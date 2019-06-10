module VDB.Example.EnronUseCase.EnronQuery.ForwardmsgForwardmsg where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 18. (interaction between fowardmsg with forwardmsg 
-- 
-- * Situdation:  Bob provisions for- warding to rjh; rjh provisions forwarding to Bob. 
--   Any message sent to either of them will loop back and forth infinitely.
-- 
-- * Fix with VDB: detect loop of forwardmsg address when have forwardmsg feature involved 
-- 
--   fowardmsg => Q1: if is_remail is False, then auto-reply; else do not auto-reply msg; 
--   NOT fowardmsg => Nothing 
-- 
-- * V-Query: fowardmsg <Q1, Empty>


enronVQ18 :: Algebra
enronVQ18 = AChc forwardmsg (u18_Q1) Empty

-- | Q1 
-- SELECT *
-- FROM v_employee emp 
-- where emp.email_id in ( 
-- 	SELECT forward.forwardAddr
--     from v_forward_msg forward )

-- | undefined because there is no "in" operation in metalanguages
u18_Q1 :: Algebra
u18_Q1 = undefined 


-- | translated SQL Q for fowardmsg <Q1, Empty>
-- SELECT emp.eid, emp.email_id, forward.forwardAddr, "forwardmsg" as presCond
-- FROM v_employee emp
-- inner join v_forward_msg forward on forward.eid = emp.eid
-- where emp.email_id in ( 
-- 	SELECT forward.forwardAddr
--     from v_forward_msg forward )
