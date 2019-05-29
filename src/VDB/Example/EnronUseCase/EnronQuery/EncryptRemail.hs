module VDB.Example.EnronUseCase.EnronQuery.EncryptRemail where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- * NOTE: implement before is_remail column introduced
-- 
-- 10. interaction between encrypt with remail
-- 
-- * Situdation: If message is encrypted,the sender's address is not visible, 
--               system can't change the address with pseudonym
--  
-- * Fix with VDB: use presence condition to prevent such situation happen.
--   remove sender's address from header line before encryption.
--   - encrypt AND remail => Q1: remove the sender's address from header line before encrypt, and do not give pseudonym
--   - encrypt AND (NOT remail) => Q2: get the public key and send the normal header 
--   - (NOT encrypt) AND remail => Q3: get pseudonym and replace the header with pseudonym
--   - (NOT encrypt) AND (NOT remail) => Q4: Normal header 
--
-- * V-Query: encrypt <remail <Q1,Q2>, remail<Q3,Q4>>


enronVQ10 :: Algebra
enronVQ10 = AChc encrypt (AChc remail u10_Q1 u10_Q2) (AChc remail u10_Q3 u10_Q4)

-- | remove the sender's address from header line before encrypt
u10_Q1 :: Algebra
u10_Q1 = Proj (map trueAtt $ genQAtts [("v_recipientinfo", "rvalue"), ("v_message", "subject"), ("v_employee", "public_key") ]) 
        $ Sel ( C.And cond joinMsgEmpRecCond)
        $ joinMsgEmpRec
        where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue
                          

u10_Q2 :: Algebra
u10_Q2 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_recipientinfo", "rvalue"), ("v_message", "subject"), ("v_employee", "public_key") ]) 
        $ Sel (C.And cond joinMsgEmpRecCond) 
        $ joinMsgEmpRec
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue

u10_Q3 :: Algebra
u10_Q3 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_recipientinfo", "rvalue"), ("v_message", "subject"), ("v_remail_msg", "pseudonym") ]) 
        $ Sel (C.And cond joinRemailEmpRecMsgCond) 
        $ joinRemailEmpRecMsg
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue


u10_Q4 :: Algebra
u10_Q4 = Proj (map trueAtt $ genQAtts [("v_message", "sender"), ("v_recipientinfo", "rvalue"), ("v_message", "subject") ]) 
        $ Sel (C.And cond joinMsgEmpRecCond) 
        $ joinMsgEmpRec
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValue


-- | translted query of interaction between encrypt and remail

-- (SELECT NULL as sender, rec.rvalue as recipientAddr, subject, public_key, NULL as pseudonym, concat("encrypt", " AND", "remailmsg") as presCond
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue 
-- where msg.mid = 9138)

-- union all 

-- (SELECT sender, rec.rvalue as recipientAddr, subject, public_key, NULL as pseudonym, concat("encrypt", " AND", "(NOT remailmsg)") as presCond
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue 
-- where msg.mid = 9138)

-- union all 

-- (SELECT sender, rec.rvalue as recipientAddr, subject, NULL as public_key, pseudonym, concat("( NOT encrypt) ", " AND", " remailmsg") as presCond
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue
-- inner join v_remail_msg rmsg on rmsg.eid = emp.eid 
-- where msg.mid = 9138)

-- union all 

-- (SELECT sender, rec.rvalue as recipientAddr, subject, NULL as public_key, NULL as pseudonym, concat("( NOT encrypt)", " AND", "(NOT remailmsg)") as presCond
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue
-- where msg.mid = 9138)
