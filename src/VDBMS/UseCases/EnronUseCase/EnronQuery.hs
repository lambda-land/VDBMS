-- | Example Queries upon Enron Email Database
module VDBMS.UseCases.EnronUseCase.EnronQuery where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.EnronUseCase.EnronSchema
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
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

join_msg_rec_emp_auto :: Algebra
join_msg_rec_emp_auto = Join (genRenameAlgebra join_msg_rec_emp) (genRenameAlgebra (tRef v_auto_msg)) cond 
                where cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vautomsg_eid)
                      vemployee_eid     = qualifiedAttr v_employee "eid"
                      vautomsg_eid = qualifiedAttr v_auto_msg "eid"

join_msg_rec_emp_remail :: Algebra
join_msg_rec_emp_remail = Join (genRenameAlgebra join_msg_rec_emp) (genRenameAlgebra (tRef v_remail_msg)) cond 
                where cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vremailmsg_eid)
                      vemployee_eid     = qualifiedAttr v_employee "eid"
                      vremailmsg_eid = qualifiedAttr v_remail_msg "eid"

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
-- * Fix by VDB: This interation has no query involed. 

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
-- * Fix in VDB: Check if the receiver of msg is in forwardlist and the sender's is_signed is true, 
--               if so, the forwardmsg will not alter the sender in the header. 
--   - signature AND forwardmsg => Q1: query the forward address for receiver of msg and the sender's is_signed
--   - signature AND (NOT forwardmsg) => Q2. the sender's is_signed
--   - (NOT signature) AND forwardmsg => Q3. the forward address for receiver of msg
--   - (NOT signature) AND (NOT forwardmsg) => Empty
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
-- * Situation: Bob sign a message that is then sent though the remail(use pseudonyms), 
--               the recipient receive the signed message, defeating the anonymity.
-- * Fix by FNE: UI --> Either disallow this or warn the user.
-- * Fix by VDB: Check if the sender's is_sign is true and receiver of the msg is remail@rmhost
--   - signature AND remailmsg => Q1: query the sender's is_sign and receiver of the msg
--   - signature AND (NOT remailmsg) => Empty
--   - (NOT signature) AND remailmsg => Empty
--   - (NOT signature) AND (NOT remailmsg) => Empty
-- * V-Query: signature AND remailmsg <Q1, Empty>
enronVQ5 :: Algebra
enronVQ5 = AChc (signature `F.And` remailmsg) i5_Q1 Empty 

-- Proj_ is_signed, rvalue Sel_ mid = midValue (v_message join_[mid = mid] v_recipientinfo)
i5_Q1 :: Algebra
i5_Q1 = Proj [trueAttr is_signed, trueAttr rvalue] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
           joinTwoRelation v_message v_recipientinfo "mid"


--
-- 6. Interaction: EncryptMessage vs. DecryptMessage
-- 
-- * We do not consider this interaction in our experiment, since for EncryptMessage and DecryptMessage will 
--   be represent as a single encrpyt feature in our variational databases. 
-- 

--
-- 7. Interaction: EncryptMeesage vs. VerifySignature
-- 
-- * Feature: encrypt vs signature
-- * Situation: Bob's encrypted message interferes with rjh's verifySignature if rjh's DecryptMessage is unable 
--   to successfully decrypt the message, since in the configuration of Client the signing is perfromed prior to encryption.          
--
-- * Fix by FNE: DNI (Do Not Inform) => the inability to verify the signature is of minor importance compared to 
--   the decryption failure, so there is little point in bringing this interaction to the attention. 
-- * Fix by VDB: DNI

--
-- 8. Interaction: EncryptMessage vs. AutoResponder
-- 
-- * Feature: encrypt vs. autoresponder
-- * Situation: Bob send an encrypted message to rjh who successfully decrypt it,
--   and who has his autoreponder provisioned (but rjh has no encrypt key for Bob provisioned).
--   The autoresponse message includes the (now decrypted) subject line of the original message, so
--   the information leaked because the autoresponse travels in the clear over the network.
-- * Fix by FNE: This can be fixed by altering AutoResponder so that it recognizes decrpyted message, which have
--   header indications inserted by decryption, and then exludes content from those message when generating the response.
-- * Fix by VDB: generate the response which exludes decrypted contects if encrypttion is provisioned and autoresponder is enabled.
--   - encrypt AND autoresponder => Q1: query the is_encrypted and the receiver's autoresponder's subject and body
--                                      (reply with autorespond subject and body, 
--                                      but doesn't contain any decrypted content)
--   - encrypt AND (NOT autoresponder) => Q2: query the sender's is_encrypted 
--   - (NOT encrypt) AND autoresponder => Q3: query the receiver's autoresponder's subject and body
--                                            (reply with autorespond subject and body 
--                                            and the original subject (Re:XXX))
--   - (NOT encrypt) AND (NOT autoresponder) => Nothing
-- * V-Query:  encrypt <autoresponder<Q1, Q2>, autoresponder <Q3, empty>>
enronVQ8 :: Algebra
enronVQ8 = AChc encrypt (AChc autoresponder i8_Q1 i8_Q2) (AChc autoresponder i8_Q3 Empty)

-- Proj_ is_encrypted, v_auto_msg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)
i8_Q1 :: Algebra
i8_Q1  = Proj (map trueAttr [is_encrypted, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_auto
        where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
              vautomsg_body    = qualifiedAttr v_auto_msg "body" 

-- Proj_ is_encrypted Sel_ mid = midValue (v_message)
i8_Q2 :: Algebra 
i8_Q2 = Proj [trueAttr is_encrypted] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            tRef v_message

-- Proj_ v_auto_msg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)
i8_Q3 :: Algebra 
i8_Q3 = Proj [ trueAttr vautomsg_subject, trueAttr vautomsg_body] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_auto
        where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
              vautomsg_body    = qualifiedAttr v_auto_msg "body"

--
-- 9. Interaction: EncryptMessage vs. ForwardMessages
-- 
-- * Feature: encrypt vs. forwardmsg
-- * Situdation: Bob sent a encrypted message to rjh's old email address which will decrypt the message 
--               and automatically forward the message to new email address (hall@research).  
--               The original encrypted message travels in the clear open network during the transition from old to new. 
-- * Fix by FNE: alter ForwardMessage so that it recognizes a decrypted message and then, instead of forwarding the message, 
--               stores it, optinally also sending a notification of its arrival along the forwarding link.
-- * Fix by VDB:  Check if the message is encrypted and forwardaddr provisoned, then send a notification.
--   - encrypt AND forwardmsg => Q1: query is_encrypted of message and the receiver's forwardaddr
--   - encrypt AND (NOT forwardmsg) => Q2: query is_encrypted 
--   - (NOT encrypt) AND forwardmsg => Q3: get forward address 
--   - (NOT encrypt) AND (NOT forwardmsg) => Empty
--
-- * V-Query: encrypt <forwardmsg<Q1, Q2>, forwardmsg <Q3, empty>>
enronVQ9 :: Algebra
enronVQ9 = AChc encrypt (AChc forwardmsg i9_Q1 i9_Q2) (AChc forwardmsg i9_Q3 Empty)


-- Proj_ is_encrypted, forwardaddr, 
--  Sel_ mid = midValue and rtype == "To" 
--  (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)  
i9_Q1 :: Algebra 
i9_Q1 = Proj [trueAttr is_encrypted, trueAttr forwardaddr] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_foward 

-- Proj_ is_encrypted Sel_ mid = midValue (v_message)
i9_Q2 :: Algebra
i9_Q2 = Proj [trueAttr is_encrypted] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            tRef v_message


-- Proj_ forwardaddr 
--  Sel_ mid = midValue and rtype == "To" 
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)
i9_Q3 :: Algebra
i9_Q3 = Proj [trueAttr forwardaddr] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_foward

--
-- 10. Interaction: EncryptMessage vs. RemailMessage  
-- 
-- * Feature: encrypt vs. remailmsg
-- * Situation: The remailer's normal function rewrites the sender's address in the message headers, replaceing 
--              such occurrences with the pseudonym. If the message is encrypted, these are not visible, so will 
--              not be rewritten. Thus, the aninymity goal of the remailer is defeated. 
-- 
-- * Fix by FNE: This can be fixed by altering the encrypt/decrypt feature to notice when the message is addressed 
--               to the remailer and take apporopriate action. For examle encrypt/decrypt could remove the sender
--               address from the header lines itself prior to encryption.
-- * Fix by VDB: 
--   - encrypt AND remailmsg => Q1: query the is_encrypted and pseudonym for the sender.
--                              (remove the sender's address from header line before encrypt, and do not give pseudonym)
--   - encrypt AND (NOT remailmsg) => Nothing 
--   - (NOT encrypt) AND remailmsg => Nothing 
--   - (NOT encrypt) AND (NOT remailmsg) => Nothing 
--
-- * V-Query: encrypt <remail <Q1,Q2>, remailmsg<Q3,Q4>>
enronVQ10 :: Algebra
enronVQ10 = AChc encrypt i10_Q1 Empty


-- Proj_ is_encrypted, pseudonym
--  Sel_ mid = midValue 
--  (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_remail_msg)  
i10_Q1 :: Algebra 
i10_Q1 = Proj [trueAttr is_encrypted, trueAttr pseudonym] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_remail 

--
-- 11. Interaction: DecryptMessage vs. AutoResponder
-- 
-- * Feature: encrypt vs. autoresponder
-- * Situation: Bob sends a message to rjh encrypted, but rjh's decrypt has the wrong key for Bob.
--              AutoResponder attempts to extract the subject from the message to include in the 
--              reponse text, but fails because it's encapsulated in the encryption. 
-- 
-- * Fix by FNE: DNI. The garbling of the subject line is of minor importance compared to the 
--               failure to decrypt. 
-- * Fix by VDB: DNI

--
-- 12. Interaction: VerifySignature vs. RemailMessage 
--                  (second half of interaction 5 "SignMessage vs RemailMessage" which is controled by own side UI)
--  
-- * Feature:  signature vs. remailmsg 
-- * Situation: A signed message sent through the remailer will be signed by the actual originator, but the RemailMessage
--              has altered the header fields by changing the originator to the pseudonym. Thus, the verifyMessage will fail
--              when applied to the message, notifying the recipient of the failure. But the clever recipient being informed
--              the failure, could search known signature ekys and try each on. Thus, the sender's identity could be leaked.  
-- 
-- * Fix by FNE: the remailer notice the signature block and purposely deleting it. 
-- * Fix by VDB: Query will be same with that of interaction 5.
enronVQ12:: Algebra
enronVQ12 = enronVQ5

--
-- 13. Interaction: AutoResponder vs. ForwardMessages
-- 
-- * Feature:  autoresponder vs. forwardmsg
-- * Situation: Bob sets up forwarding to rjh. Rjh has autoresponse enbaled.
--              A third party sends a message to Bob, which is forwarded to rjh.
--              The autoresponse is sent back to Bob and then forwarded to rjh. Thus, msg arriving at rjh via
--              Bob are no effectively autoresponded. 
-- 
-- * Fix by FNE: fix ForwardMessages so that it manipulates header lines better: leave the "sender: " line intact.
--               The autoresponder will then reply to the originator of the message instead of to the forwarder.    
-- 
-- * Fix by VDB: 
--   - autoresponder AND forwardmsg  => Q1: Query the original sender, forwardAddr, auto_response's body and subject of forwardaddr
--                                          (forward with intact sender info and auto reply to original sender)
--   - autoresponder AND (NOT forwardmsg) => Q2: normal query with autoresponse. (body and forward)  
--   - (NOT autoresponder) AND forwardmsg => Q3. normal query with forwardmsg (forwardAddr)
--   - (NOT autoresponder) AND (NOT forwardmsg) => Nothing
--   
-- * V-Query: autoresponder <forwardmsg <Q1,Q2>, forwardmsg<Q3, Empty>>
enronVQ13 :: Algebra
enronVQ13 =  AChc autoresponder (AChc forwardmsg i13_Q1 i13_Q2) (AChc forwardmsg i13_Q3 Empty) 

-- Proj_ sender, forwardaddr, v_auto_msg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg [eid = eid] v_forward_msg)
i13_Q1 :: Algebra
i13_Q1 = Proj (map trueAttr [sender, forwardaddr, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            Join (genRenameAlgebra join_msg_rec_emp_auto) (genRenameAlgebra (tRef v_forward_msg)) cond    
        where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
              vautomsg_body    = qualifiedAttr v_auto_msg "body"
              vforwardmsg_eid  = qualifiedAttr v_forward_msg "eid"
              vemployee_eid    = qualifiedAttr v_employee "eid"
              cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vforwardmsg_eid)

-- Proj_ v_auto_msg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)
i13_Q2 :: Algebra
i13_Q2 = Proj [ trueAttr vautomsg_subject, trueAttr vautomsg_body] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_auto
        where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
              vautomsg_body    = qualifiedAttr v_auto_msg "body"
-- Proj_ forwardaddr 
--  Sel_ mid = midValue and rtype == "To" 
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)
i13_Q3 :: Algebra
i13_Q3 = Proj [trueAttr forwardaddr] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_foward

--
-- . Interaction: 
-- 
-- * Feature: 
-- * Situation: 
-- 
-- * Fix by FNE: 
-- 
-- * Fix by VDB:
-- * V-Query: 







