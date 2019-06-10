module VDB.Example.EnronUseCase.EnronQuery.AddressbookEncrypt where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))

-- 
-- 1. Interaction between addressbook with encrypt 
-- 
-- * Situdation: Suppose an alias in the address book sends to two correspondents, 
--   for one of whom ENCRYPTMESSAGE is provisioned with an encryption key and 
--   for the other it is not. 
--   Then a message sent to this alias will go encrypted to one but in the clear to the other; 
--   sending the message in the clear on the open network defeats the intent (privacy) of ENCRYPTMESSAGE.
--   (eg. a single message with two addressees)
-- * Fix: use presence condition to prevent such situation happen.
-- 
--   => Queries in different configuration
--   addressbook AND encrypt => Q1: Query that could support UI (detail is in SPL paper p.71)
--   addressbook AND (NOT encrypt) => Nothing
--   (NOT addressbook) AND encrypt => Nothing
--   (NOT addressbook) AND (NOT encrypt) => Nothing 
--
-- * V-Query: addressbook AND encrypt <Q1,Empty>

enronVQ1 :: Algebra
enronVQ1 = AChc encrypt u1_Q1 Empty

-- | remove the sender's address from header line before encrypt
u1_Q1 :: Algebra
u1_Q1 = Proj (map trueAtt $ genQAtts [("v_employee", "eid"), ("v_employee", "email_id"), ("v_employee", "public_key") ]) 
        $ Sel ( C.And cond joinMsgEmpRecCond)
        $ joinMsgEmpRec
        where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) midValueEncrypted
              cond2 = C.Comp EQ (C.Attr (genQAtt ("v_message","is_encrypt"))) trueValue
              cond = C.And cond1 cond2 

-- | translted query of interaction between encrypt and remail
-- SELECT emp.eid, emp.email_id, emp.public_key, concat("addressbook", " AND ", "encrypt") as presCond
-- FROM v_employee emp 
-- inner join v_recipientinfo rec on rec.rvalue = emp.email_id 
-- inner join v_message msg on msg.mid = rec.mid
-- where msg.mid = 2893 and  msg.is_encrypt = 1 