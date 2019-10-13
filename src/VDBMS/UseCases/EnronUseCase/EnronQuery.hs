-- | Example Queries upon Enron Email Database
module VDBMS.UseCases.EnronUseCase.EnronQuery where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.EnronUseCase.EnronSchema
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.UseCases.SmartConstructor
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))
import Database.HDBC 

-- the purpose of the email database is to showcase 
-- the testing step and the use of databases in this
-- step. hence qs are written from the tester perspective
-- in spl. due to interactions among features lots of test
-- is required to ensure that the software system behaves
-- accordinly in these scenarios.

-- | the message id value we choose for entire use case
midValue :: C.Atom
midValue = (C.Val (SqlInt32 9138))

midValueFromRemailer :: C.Atom
midValueFromRemailer = (C.Val (SqlInt32 1082))

midValueEncrypted :: C.Atom 
midValueEncrypted = (C.Val (SqlInt32 2893))

eidValue :: C.Atom
eidValue = (C.Val (SqlInt32 123))

nullValue :: C.Atom 
nullValue = C.Val SqlNull

trueValue :: C.Atom
trueValue = C.Val (SqlBool True)

falseValue :: C.Atom
falseValue = C.Val (SqlBool False)

midCondition :: C.Condition
midCondition = C.Comp EQ (C.Att (qualifiedAttr v_message  "mid")) midValue

join_msg_rec_emp :: Algebra
join_msg_rec_emp = Join (genRenameAlgebra join_msg_rec) (genRenameAlgebra (tRef v_employee)) cond 
                where join_msg_rec = joinTwoRelation v_message v_recipientinfo "mid"
                      cond = C.Comp EQ (C.Att rvalue) (C.Att email_id)

join_msg_rec_emp_foward :: Algebra
join_msg_rec_emp_foward = Join (genRenameAlgebra join_msg_rec_emp) (genRenameAlgebra (tRef v_forward_msg)) cond 
                where cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vforwardmsg_eid)
                      vemployee_eid     = qualifiedAttr v_employee "eid"
                      vforwardmsg_eid = qualifiedAttr v_forward_msg "eid"


-- FNE: The paper name: Fundamental Nonmodularity in Electronic Mail
-- 
-- 1. Interaction: Addressbook vs EncryptMessage 
-- 
-- * Feature: addressbook vs encrypt
-- * Situdation: Suppose an alias in the address book sends to two correspondents, 
--   for one of whom ENCRYPTMESSAGE is provisioned with an encryption key and 
--   for the other it is not. 
--   Then a message sent to this alias will go encrypted to one but in the clear to the other; 
--   sending the message in the clear on the open network defeats the intent (privacy) of ENCRYPTMESSAGE.
--   (eg. a single message with two addressees)
-- * Fix by FNE: by customized UI, 
--   Fix by VDB: This interation has no query involed. 

--
-- 2. Interaction: Addressbook vs RemailMessage 
-- 
-- * Feature: addressbook vs remail
-- * Situation: Suppose an alias in the address book sneds to the remailer as well as to some other correspondent. 
--   Then sending a meesage to that alias in remailer format will send the message both through the remailer
--   to the third party and to the other correspondent. However, the correspondent can see who the thrid party is 
--   and then leak the identity of the sender. 
-- * Fix by FNE: by customized UI, 
--   Fix by VDB: This interation has no query involed. 

-- 
-- 3. Interaction: SignMessage vs VerifyMessage 
-- 
-- * We do not consider this interaction in our experiment, since for signMessage and VerifyMessage will 
--   be represent as signature feature in our variational databases.

--
-- 4. Interaction: SignMessage vs ForwardMessages 
-- 
-- * Feature: signature vs forward
-- * Situation: Suppose Bob sends a signed message to rjh, who has no signkey provisioned, yet who forwards
--   the message to a third party, THe message will arrive there signed, but not by the sender(rjh), 
--   but by the originator(Bob), since the verification is defined to determine whether the message 
--   was signed by the sender of the message. 
-- * Fix by FNE: change the ForwardMessages so that it doens't alter the "Sender: " header of the message.
--   Fix in VDB: Check if the receiver of msg is in forwardlist and the sender's is_signed is true, 
--               if so, the forwardmsg will not alter the sender in the header. 
--   - signautre AND forwardmsg => Q1: query the forward address for receiver of msg and the sender's is_signed
--   - signautre AND (NOT forwardmsg) => Q2. the sender's is_signed
--   - (NOT signautre) AND forwardmsg => Q3. the forward address for receiver of msg
--   - (NOT signautre) AND (NOT forwardmsg) => Empty
-- * V-Query: signature <forwardmsg<Q1, Q2>, forwardmsg <Q3, empty>>

enronVQ4 :: Algebra
enronVQ4 = AChc signature (AChc forwardmsg i4_Q1 i4_Q2) (AChc forwardmsg i4_Q3 Empty)


-- Proj_ forwardaddr, is_signed
--  Sel_ mid = midValue and rtype == "To" 
--  (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)  
i4_Q1 :: Algebra 
i4_Q1 = Proj [trueAttr forwardaddr, trueAttr is_signed] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_foward 

-- Proj_ is_signed Sel_ mid = midValue (v_message)
i4_Q2 :: Algebra
i4_Q2 = Proj [trueAttr is_signed] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            tRef v_message


-- Proj_ forwardaddr 
--  Sel_ mid = midValue and rtype == "To" 
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)
i4_Q3 :: Algebra
i4_Q3 = Proj [trueAttr forwardaddr] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_foward


--
-- 5. Interaction: SignMessage vs RemailMessage 
-- 
-- * Feature: signature vs remailmsg
-- * Situdation: Bob sign a message that is then sent though the remail(use pseudonyms), 
--               the recipient receive the signed message, defeating the anonymity.
-- * Fix by FNE: UI --> Either disallow this or warn the user.
--   Fix by VDB: Check if the sender's is_sign is true and receiver of the msg is remail@rmhost
--   - signautre AND remailmsg => Q1: query the sender's is_sign and receiver of the msg
--   - signautre AND (NOT remailmsg) => Empty
--   - (NOT signautre) AND remailmsg => Empty
--   - (NOT signautre) AND (NOT remailmsg) => Empty
-- * V-Query: signature AND remailmsg <Q1, Empty>
enronVQ5 :: Algebra
enronVQ5 = undefined 

-- Proj_ is_signed, rvalue Sel_ mid = midValue (v_message join_[mid = mid] v_recipientinfo)
i5_Q1 :: Algebra
i5_Q1 = Proj [trueAttr is_signed, trueAttr rvalue] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
           joinTwoRelation v_message v_recipientinfo "mid"


