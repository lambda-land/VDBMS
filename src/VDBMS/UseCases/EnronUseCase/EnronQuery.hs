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

join_msg_rec_emp_reference :: Algebra
join_msg_rec_emp_reference = Join  (genRenameAlgebra join_msg_rec_emp) (genRenameAlgebra (tRef v_referenceinfo)) cond 
                        where cond = C.Comp EQ (C.Att vrecipientinfo_mid) (C.Att vreferenceinfo_mid)
                              vrecipientinfo_mid = qualifiedAttr v_recipientinfo "eid"
                              vreferenceinfo_mid = qualifiedAttr v_referenceinfo "eid"
-- | v_message Join_[sender = email_id] v_employee
join_msg_emp :: Algebra
join_msg_emp = Join (genRenameAlgebra (tRef v_message)) (genRenameAlgebra (tRef v_employee)) join_cond
                where join_cond = C.Comp EQ (C.Att sender) (C.Att email_id)

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

-- | Join 4 tables based on recipient suffix 
--  v_message Join_[mid = mid] v_recipient Join _[rvalue = email_id] v_employee [eid = eid]v_filrter_msg
join_msg_rec_emp_filter :: Algebra
join_msg_rec_emp_filter = Join (genRenameAlgebra join_msg_rec_emp) (genRenameAlgebra (tRef v_filter_msg)) cond 
                where cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vfiltermsg_eid)
                      vemployee_eid     = qualifiedAttr v_employee "eid"
                      vfiltermsg_eid = qualifiedAttr v_filter_msg "eid"

-- | v_message Join_[sender = email_id] v_employee Join _[eid = eid] v_filrter_msg
join_msg_emp_filter :: Algebra
join_msg_emp_filter = Join (genRenameAlgebra join_msg_emp) (genRenameAlgebra (tRef v_filter_msg)) cond 
                where cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vfiltermsg_eid)
                      vemployee_eid     = qualifiedAttr v_employee "eid"
                      vfiltermsg_eid = qualifiedAttr v_filter_msg "eid"

join_msg_emp_forward :: Algebra
join_msg_emp_forward = Join (genRenameAlgebra join_msg_emp) (genRenameAlgebra (tRef v_forward_msg)) cond 
                where cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vforwardmsg_eid)
                      vemployee_eid     = qualifiedAttr v_employee "eid"
                      vforwardmsg_eid = qualifiedAttr v_forward_msg "eid"


join_emp_forward_remail :: Algebra
join_emp_forward_remail = joinThreeRelation v_employee v_forward_msg v_remail_msg "eid"

-- | Query recipient's pseudonym from remailer for a certain message id.
--  Proj_ pseudonym
--   Sel_ mid = midValue 
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_remail_msg)  
query_pseudonym_from_remailer :: Algebra
query_pseudonym_from_remailer  = Proj [trueAttr pseudonym] $ genRenameAlgebra $ 
                                  Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                                    join_msg_rec_emp_remail

-- | Query autorespondse subject and body of recipient for a certain message id.
-- Proj_ v_auto_mg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)
query_autoresponder_subject_body :: Algebra
query_autoresponder_subject_body = 
            Proj [ trueAttr vautomsg_subject, trueAttr vautomsg_body] $ genRenameAlgebra $ 
            Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_auto
        where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
              vautomsg_body    = qualifiedAttr v_auto_msg "body"

-- | Normal query abot reicipient's filter suffix 
-- Proj_ suffix 
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_filter_msg)
query_recipient_filter_suffix :: Algebra
query_recipient_filter_suffix = 
            Proj [ trueAttr suffix] $ genRenameAlgebra $ 
            Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_filter 

-- | Normal query about sender's filter suffix 
-- Proj_ suffix 
--  Sel_ mid = midValue
--   (v_message join_[sender = email_id] v_employee [eid = eid] v_filter_msg)
query_sender_filter_suffix :: Algebra
query_sender_filter_suffix = 
            Proj [ trueAttr suffix] $ genRenameAlgebra $ 
            Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_filter 

-- | Normal query about recipient's forwardaddr 
-- Proj_ forwardaddr 
--  Sel_ mid = midValue 
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)
query_recipient_forwardaddr :: Algebra
query_recipient_forwardaddr = Proj [trueAttr forwardaddr] $ genRenameAlgebra $ 
                                Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                                  join_msg_rec_emp_foward

-- | Normal query for is_signed
query_is_signed :: Algebra
query_is_signed = Proj [trueAttr is_signed] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      tRef v_message

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
-- * Feature: signature vs. forwardmsg
-- * Situation: Suppose Bob sends a signed message to rjh, who has no signkey provisioned, yet who forwards
--   the message to a third party, THe message will arrive there signed, but not by the sender(rjh), 
--   but by the originator(Bob), since the verification is defined to determine whether the message 
--   was signed by the sender of the message. 
--
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
i4_Q2 = query_is_signed


-- Proj_ forwardaddr 
--  Sel_ mid = midValue and rtype == "To" 
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)
i4_Q3 :: Algebra
i4_Q3 = query_recipient_forwardaddr

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
-- * Fix by VDB: Check if the sender is removed when email is encrypted and is sending to a remailer.
--   - encrypt AND remailmsg => Q1: query the is_encrypted and recipient address .
--                              (remove the sender's address from header line before encrypt, and do not give pseudonym)
--   - encrypt AND (NOT remailmsg) => Nothing 
--   - (NOT encrypt) AND remailmsg => Nothing 
--   - (NOT encrypt) AND (NOT remailmsg) => Nothing 
--
-- * V-Query: encrypt <remail <Q1,Q2>, remailmsg<Q3,Empty>>
enronVQ10 :: Algebra
enronVQ10 = AChc encrypt i10_Q1 Empty

-- Proj_ is_encrypted, rvalue
--  Sel_ mid = midValue 
--  (v_message join_[mid == mid] v_recipientinfo)  
i10_Q1 :: Algebra 
i10_Q1 = Proj [trueAttr is_encrypted, trueAttr rvalue] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            joinTwoRelation v_message v_recipientinfo "mid"

-- -- Proj_ is_encrypted, pseudonym
-- --  Sel_ mid = midValue 
-- --  (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_remail_msg)  
-- i10_Q1 :: Algebra 
-- i10_Q1 = Proj [trueAttr is_encrypted, trueAttr pseudonym] $ genRenameAlgebra $ 
--           Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--             join_msg_rec_emp_remail 

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
-- 14. Interaction: AutoResponder vs. RemailMessage (1)
-- 
-- * Feature: autoresponder vs. remailmsg
-- * Situdation: Bob activate an autoresponder in his remailer account when he is on vacation.
--   Rjh can reply a msg to Bob's pseudonym which then remailMessage mails to Bob. Then
--   the autoresponder of Bob will sends a message directly to Rjh telling him Bob is on vacation.
--   This allows rjh to infer that the pseudonym is for Bob.
--   (The problem is the content of the autoreply message giving Bob's identity, header manipulation will not avoid that)
-- 
-- * Fix by FNE: The autoresponder should be altered to notice when a message has arrived via the remailer(it can tell 
--               this by examining message headers) and not respond to them. 
-- 
-- * Fix by VDB: 
--   autoresponder AND remailmsg  => Q1: query the is_from_remailer, and autoresponse's body and subject
--                                      (if is_from_remailer is False, then auto-reply; else do not auto-reply msg)
--   autoresponder AND (NOT remailmsg) => Q2. normal query about autoresponse's body and subject
--   (NOT autoresponder AND remailmsg => Q3. normal query abot pseudonym form remailer    
--   (NOT autoresponder) AND (NOT remailmsg) => Nothing 
-- * V-Query: autoresponder <remailmsg <Q1,Q2>, remailmsg<Q3, Empty>> 
enronVQ14 :: Algebra
enronVQ14 = AChc autoresponder (AChc remailmsg i14_Q1 i14_Q2) (AChc remailmsg i14_Q3 Empty) 

-- Proj_ is_from_remailer, v_auto_msg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)i14_Q1 :: Algebra
i14_Q1 :: Algebra
i14_Q1 = Proj (map trueAttr [ is_from_remailer, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_auto
        where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
              vautomsg_body    = qualifiedAttr v_auto_msg "body"

-- Proj_ v_auto_msg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)
i14_Q2 :: Algebra
i14_Q2 = query_autoresponder_subject_body

-- Proj_ pseudonym
--  Sel_ mid = midValue 
--  (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_remail_msg)  
i14_Q3 :: Algebra
i14_Q3 = query_pseudonym_from_remailer

--
-- 15. Interaction: AutoResponder vs. RemailMessage (2)
-- 
-- * Feature: autoresponder vs. remailmsg
-- * Situation: Suppose Bob has a remailer acocount, so he can send anonymously to rjh. 
--              Suppose Bob goes on vacation and activates his autoresponder. 
--              Now suppose rjh, having no reason to think Bob and the pseudonym address the same account,
--              sends a "Happy New Year" message to both Bob and this pseudonym account. 
--              Autoreponder of Bob, seeing both as from rjh, generates a totla of one response, 
--              since it is designed not to send more than one copy of the response to any single correspondent.
--              Thus, rjh is informed that Bob is on vacation, but thinks the pseudonym is just being rude in not replying.
--              The autoresponder's function is defeated. 
--   
-- * Fix by FNE: Fix the remailer so that instead of needing to format the message body specilly in the anonymize direction, 
--               the user encodes the address of the recipient in the remailer address.
--               (make ) 
-- 
-- * Fix by VDB: Check if the message is both from remailer and also receipient's autoresponse is provisioned. 
--               If so, then the recipient address should be in a new format (rjh%rjhhost@remailer.org).
-- 
--   autoresponder AND remailmsg  => Q1: query the is_from_remailer, receipitent's address, autoresponse's body and subject
--   autoresponder AND (NOT remailmsg) => Q2. normal query about autoresponse's body and subject
--   (NOT autoresponder AND remailmsg => Q3. normal query abot pseudonym form remailer    
--   (NOT autoresponder) AND (NOT remailmsg) => Nothing 
-- 
-- * V-Query: autoresponder <remailmsg <Q1,Q2>, remailmsg<Q3, Empty>> 
enronVQ15 :: Algebra
enronVQ15 = AChc autoresponder (AChc remailmsg i15_Q1 i15_Q2) (AChc remailmsg i15_Q3 Empty) 

-- | Query the is_from_remailer, receipitent's address, autoresponse's body and subject
-- Proj_ is_from_remailer, v_auto_msg.subject, v_auto_msg.body  
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)i14_Q1 :: Algebra
i15_Q1 :: Algebra
i15_Q1 = Proj (map trueAttr [ is_from_remailer, rvalue, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_auto
        where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
              vautomsg_body    = qualifiedAttr v_auto_msg "body"

-- | Normal query about autoresponse's body and subject
i15_Q2 :: Algebra 
i15_Q2 =  query_autoresponder_subject_body

-- | Normal query abot pseudonym form remailer  
i15_Q3 :: Algebra
i15_Q3 = query_pseudonym_from_remailer

--
-- 16. Interaction: Autoresponder vs. FilterMessages
-- 
-- * Feature:  autoresponder vs. filtermsg
-- * Situation: The system adminitrator provisions FilterMessages to discard message from "research" domain.
--              Bob, a user, sends a message to "hall@research" asking him to meet him tomorrow. hall@research's 
--              autoresponse informing Bob that he is OOO is discard by filter. Thus, the filter ahs defeated
--              the purpose of autoresponder. 
-- 
-- * Fix by FNE: Making the filter recognize autoresponder-generated message and admitting them even when they
--               would otherwise be filtered. 
-- 
-- * Fix by VDB: Test if the message is from autoresponder and the sender of autoresponse msg is in the receipient's
--               filter suffix, the message deliver or not 
--   autoresponder AND filtermsg  => Q1: query sender's email address, is_autoresponse, recipient's filter suffix.
--   autoresponder AND (NOT filtermsg) => Q2. normal query about autoresponse's subject and body
--   (NOT autoresponder AND filtermsg => Q3. normal query about filter suffix.
--   (NOT autoresponder) AND (NOT filtermsg) => Nothing 
-- * V-Query:  autoresponder <filtermsg <Q1, Q2>, filterMsg <Q3, Empty>>
enronVQ16 :: Algebra
enronVQ16 = AChc autoresponder (AChc filtermsg i16_Q1 i16_Q2) (AChc filtermsg i16_Q3 Empty) 

-- -- |Query sender's email address, is_autoresponse, recipient's filter suffix.
-- -- Proj_ sender, is_autoresponse, suffix
-- --  Sel_ mid = midValue
-- --   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg [eid = eid] v_filter_msg)
-- i16_Q1 :: Algebra
-- i16_Q1 = Proj (map trueAttr [sender, is_autoresponse, suffix]) $ genRenameAlgebra $ 
--           Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--             join_msg_rec_emp_filter

-- |Query message's subject, autoresponse's subject sender's email address, recipient's filter suffix.
-- Proj_ sender, is_autoresponse, suffix
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg [eid = eid] v_filter_msg)
i16_Q1 :: Algebra
i16_Q1 = Proj (map trueAttr [sender, is_autoresponse, suffix]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
             Join ( genRenameAlgebra join_msg_emp_filter) (genRenameAlgebra (tRef v_auto_msg)) cond 
              where  cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vautomsg_eid)
                     vemployee_eid = qualifiedAttr v_employee "eid"
                     vautomsg_eid = qualifiedAttr v_auto_msg "eid"
-- | Normal query about autoresponse's body and subject
i16_Q2 :: Algebra 
i16_Q2 =  query_autoresponder_subject_body

-- | Normal query abot filter suffix
i16_Q3 :: Algebra
i16_Q3 = query_recipient_filter_suffix


--
-- 17. Interaction: AutoResponder vs. MailHost
-- 
-- * Feature: autoresponder vs. mailhost
-- * Situation: Bob provisions an autoresponse. Then Bob sends a message to an unknow user. This generates
--              a response from postmaster informing Bob of the problem. But this postmaster response is, in turn,
--              autorespond and yet another message is sent from Bob to Postmaster containing Bob's autorespond.
--              The latter one is extraneous.
-- 
-- * Fix by FNE: Autoreponder should not reply to Non-Delivery Notification generated ny MailHost feature.
-- 
-- * Fix by VDB: Test if the autoresponder generate a response when there is a Non-Delivery Message from MailhHost, 
--                 
-- * V-Query: 
--   autoresponder AND mailhost  => Q1: Query is_system_notification, recipient's autoresponder subject and body
--   autoresponder AND (NOT mailhost) =>  Nothing 
--   (NOT autoresponder AND mailhost => Nothing 
--   (NOT autoresponder) AND (NOT mailhost) => Nothing 
enronVQ17 :: Algebra
enronVQ17 = AChc (autoresponder `F.And` mailhost) i17_Q1 Empty

i17_Q1 :: Algebra
i17_Q1 = Proj (map trueAttr [is_system_notification]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            (tRef v_message)
-- | Query is_system_notification, recipient's autoresponder subject and body
-- Proj_ is_system_notification, v_auto_msg.subject, v_auto_msg.body
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_auto_msg)
-- i17_Q1 :: Algebra
-- i17_Q1 = Proj (map trueAttr [is_system_notification, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
--           Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--             join_msg_rec_emp_auto
        -- where vautomsg_subject = qualifiedAttr v_auto_msg "subject"
        --       vautomsg_body    = qualifiedAttr v_auto_msg "body"

--
-- 18. Interaction: ForwardMessages vs. ForwardMessages 
-- 
-- * Feature: forwardmsg vs. forwardmsg 
-- * Situation: Bob provisions forwarding to rjh, rjh provisions forwarding to Bob. Loop exists in this case.
-- 
-- * Fix by FNE: fix ForwardMessages so that it adds "Received-by:" headers appropriately and terminates loop
--               when it detectes that the message has been processed by it before.
-- 
-- * Fix by VDB: 
--   fowardmsg => Q1: check if there is cycle of eid and forwardaddr in v_forward_msg 
--   NOT fowardmsg => Nothing 
-- 
-- * V-Query: fowardmsg <Q1, Empty>
enronVQ18 :: Algebra
enronVQ18 = AChc forwardmsg i18_Q1 Empty

-- | Check if there is cycle of eid and forwardaddr in v_forward_msg 
-- Proj_ email_id, forwardaddr
--  (v_employee Join_[eid = eid] v_forward_msg) 
i18_Q1 :: Algebra
i18_Q1 = Proj (map trueAttr [ subject, email_id, forwardaddr]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            joinTwoRelation v_employee v_forward_msg "eid"

--
-- 19. Interaction: ForwardMessage vs. RemailMessage (1)
-- 
-- * Feature: forwardmsg vs. remailmsg
-- * Situdation: Bob establishes a pseudonym on the remailer and 
--   provisions FORWARDMESSAGES to send to that pseudonym. 
--   Messages sent to Bob will be infinitely forwarded from Bob to remailer and back.
-- 
-- * Fix by FNE: This must be fixed at remailer, even if a ForwardMessage fix is done first.
--               if the ForwardMessages feature is allowed to terminate the loop and send back a Non-Delivery
--               Notification, then the headers will show that Bob and the pseudonym are connected, leaking
--               identity. Thus, the fix must be for the remailer to detect the loop adn terminate it. It must
--               also remove any header information that might leak the pseudonym prior tp generating the NDN.
-- 
-- * Fix by VDB: Detect the loop
--   forwardmsg AND remailmsg => Q1: Query forwardAddr and psuedonym for each email_id (remailer detect the loop) 
--   forwardmsg AND (NOT remailmsg) => Nothing    
--   (NOT forwardmsg) AND remailmsg => Nothing 
--   (NOT forwardmsg) AND (NOT remailmsg) => Nothing 
-- 
-- * V-Query: remailmsg AND forwardmsg <Q1, Empty>
enronVQ19 :: Algebra
enronVQ19 = AChc (remailmsg `F.And` forwardmsg) i19_Q1 Empty  

-- | Query forwardAddr and psuedonym for each email_id (remailer detect the loop) 
i19_Q1 :: Algebra
i19_Q1 = Proj (map trueAttr [email_id, forwardaddr, pseudonym]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_emp_forward_remail

--
-- 20. Interaction: ForwardMessage vs. RemailMessage (2)
-- 
-- * Feature: forwardmsg vs. remailmsg
-- * Situation: Bob doesn't establish a pseudonym on the remailer; 
--              Bob provisions ForwardMessages to send to "remail-mail@remailer".
--              Any message sent to Bob will result in an error message from remailer to Bob which will
--              be again forward back to the remailer, resulting in another error message. 
-- 
-- * Fix by FNE: DNI.
-- 
-- * Fix by VDB: DNI
-- * V-Query: 

--
-- 21. Interaction: ForwardMessages vs. FilterMessages
-- 
-- * Feature: forwardmsg vs. filtermsg
-- * Situation: Bob sets forwarding to rjh@host. Unbeknownst to Bob, host's admin runs a filter that discards all 
--              mail from Bob's domain. All of Bob's mail silently disappears from then on.
-- 
-- * Fix by FNE: When ForwardMessages is first provisioned by Bob, ForwardMessages can send a simple test message,
--               to the forward address, notifying Bob that he should observe whether it gets there. 
--               The fix is to observe whehter it gets there. 
-- 
-- * Fix by VDB: Test the notification works or not. Query sender's domain and sender forwardaddr's filter suffix.
--   forwardmsg AND filtermsg =>  Q1: Query sender's domain and forwardaddr's filter suffix.
--   forwardmsg AND (NOT filtermsg) =>  Nothing 
--   (NOT forwardmsg) AND filtermsg =>  Nothing 
--   (NOT forwardmsg) AND (NOT filtermsg) =>  Nothing 
--   
-- * V-Query: forwardmsg AND filtermsg <Q1, Empty>
enronVQ21 :: Algebra
enronVQ21 = AChc (forwardmsg `F.And` filtermsg) i21_Q1 Empty


-- Proj_ sender, forwardaddr, suffix
--   Sel_ mid = midValue
--    (v_message Join_[sender = email_id] v_employee Join_[eid = eid] v_filter_msg Join_[eid = eid] v_forward_msg)
i21_Q1 :: Algebra
i21_Q1 = Proj (map trueAttr [sender, forwardaddr, suffix]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
             Join ( genRenameAlgebra join_msg_emp_filter) (genRenameAlgebra (tRef v_forward_msg)) cond 
              where  cond = C.Comp EQ (C.Att vemployee_eid) (C.Att vforwardmsg_eid)
                     vemployee_eid = qualifiedAttr v_employee "eid"
                     vforwardmsg_eid = qualifiedAttr v_forward_msg "eid"
--
-- 22. Interaction: ForwardMessages vs. MailHost
-- 
-- * Feature: fowardmsg vs. mailhost
-- * Situation: Bob accidentally sets forwarding to a nonexistent user at his host.
--              Any subsequent message to Bob results in an infinite sequence of progreesively 
--              longer error message as MailHost attempts to inform Bob that the user is unknown and 
--              keep receiving its error messages forward back to the same non-existent user.
-- 
-- * Fix by FNE:  MailHost detect the loop and terminate it. 
-- 
-- * Fix by VDB: Check in MailHost that if the sender of this forward msg has set a non-user as forwardaddr. 
--               If so, then check the original message in message body to see if the address in "FROM:" is the 
--               mailhost it self. 
--   forwardmsg AND mailhost =>  Q1: Query about is_forward_msg, sender, sender's forwardaddr, recipient address, reference 
--   forwardmsg AND (NOT mailhost) =>  Nothing 
--   (NOT forwardmsg) AND mailhost =>  Nothing 
--   (NOT forwardmsg) AND (NOT mailhost) =>  Nothing 
-- * V-Query: forwardmsg AND mailhost <Q1, Empty>
enronVQ22 :: Algebra
enronVQ22 = AChc (forwardmsg `F.And` mailhost) i22_Q1 Empty

-- Proj_ is_forward_msg, sender, forwardaddr, rvalue, reference
--   Sel_ mid = midValue
--    (v_message Join_[mid = mid] v_recipientinfo Join_[mid = mid ] v_referenceinfo Join_[rvalue = email_id] v_employee) 
--    Union_
--    (v_message Join_[sender = email_id] v_employee Join_[eid = eid] v_forward_msg) 
i22_Q1 :: Algebra
i22_Q1 = Proj (map trueAttr [sender, forwardaddr, rvalue, reference]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
             SetOp Union join_msg_rec_emp_reference join_msg_emp_forward 

--
-- 23. Interaction: RemailMessages vs. FilterMessages
-- 
-- * Feature: remailmsg vs. filtermsg
-- * Situation: We provision FilterMessages to discard all message from the domain "research".
--              However, the third party from within "research" obtains a RemailMessage pseudonym 
--              and sends a message to Bob. Because RemailMessage sets the sender of the message 
--              to <pseudonym>@remailer, it is not filter and is instead deliver to Bob
-- 
-- * Fix by FNE: NO FIX.

--
-- 24. Interaction: RemailMessage vs. VerifySignature
-- 
-- * Feature: remailmsg vs. signature
-- * Situation: 
-- 
-- * Fix by FNE: same fix with interaction 15.
-- 
-- * Fix by VDB: Check if receipient's signature is provisioned in PostOffice . 
--               If so, then the recipient address should be in a new format (rjh%rjhhost@remailer.org).
-- 
--   remailmsg AND signature =>  Q1: query is_signed, recipient's address 
--   remailmsg AND (NOT signature) =>  Nothing 
--   (NOT remailmsg) AND signature =>  Nothing 
--   (NOT remailmsg) AND (NOT signature) =>  Nothing 
-- * V-Query: remailmsg AND signature <Q1, Empty>
enronVQ24 :: Algebra
enronVQ24 = AChc (remailmsg `F.And` signature) i24_Q1 Empty

-- | Query the is_signed, recipient's address
-- Proj_ is_signed, rvalue 
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo)
i24_Q1 :: Algebra
i24_Q1 = Proj (map trueAttr [is_signed, rvalue]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            joinTwoRelation v_message v_recipientinfo "mid"

--
-- 25. Interaction: RemailMessage vs. MailHost
-- 
-- * Feature: remailmsg vs. mailhost
-- * Situation: Bob at host sets up and uses a remailer pseudonym to send embarrasing mail to rjh.
--              Bob then abandon his host account forgeeting to deactivate the remailer pseudonym.
--              Rjh then replies to the pseudonym and gets a bound message from the host the reveals
--              Bob's identity to rjh.
-- 
-- * Fix by FNE: Alter MailHost so that it detects remailed messages and generates Non-Delivery notification
--               that are devoid of information that might leak the identity of the user. 
-- 
-- * Fix by VDB: Check in MailHost that if the message is from remailer. 
-- * V-Query: 
--   remailmsg AND mailhost =>  Q1: query is_from_remailer
--   remailmsg AND (NOT mailhost) =>  Nothing 
--   (NOT remailmsg) AND mailhost =>  Nothing 
--   (NOT remailmsg) AND (NOT mailhost) =>  Nothing 
-- * V-Query: remailmsg AND mailhost <Q1, Empty>
enronVQ25 :: Algebra
enronVQ25 = AChc (remailmsg `F.And` mailhost) i25_Q1 Empty

-- | Proj_ is_from_remailer,
--    Sel mid = midValue
--     (v_message)
i25_Q1 :: Algebra
i25_Q1 = Proj [trueAttr is_from_remailer] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            tRef v_message

--
-- 26. Interaction: FilterMessages vs. MailHost
-- 
-- * Feature: filtermsg vs. mailhost
-- * Situation: We provision FilterMessage to discard all messages from "research" domain. Bob then sends a message
--              to "non-user@research" which is not a valid user name in that domain. The MailHost instance
--              in "research" generate a message from "postmaster@research" to Bob to notify him no such user.
--              FilterMessages discard the postmaster message. This defeats the goal of MailHost feature which
--              is to either deliver a message or notify the sender of its inability to do so.
-- 
-- * Fix by FNE: Alter FilterMessages so that it recognizes Non-Delivery Notification and passes them through when
--               they are in response to a known prior ourbound message.
-- 
-- * Fix by VDB: Check if the message is a Non-Delivery Notification and the sender's address is in the suffix of recipient.
--   filtermsg AND mailhost =>  Q1: query is_system_notification, sender, sender's filter suffix, recipient's address
--   filtermsg AND (NOT mailhost) =>  Nothing 
--   (NOT filtermsg) AND mailhost =>  Nothing 
--   (NOT filtermsg) AND (NOT mailhost) =>  Nothing 
-- * V-Query: filtermsg AND mailhost <Q1, Empty>
enronVQ26 :: Algebra
enronVQ26 = AChc (filtermsg `F.And` mailhost) i26_Q1 Empty

-- | query is_system_notification, sender, receipient's filter suffix and address
-- Proj_ is_system_notification, sender, rvalue, suffix
--  Sel_ mid = midValue
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_filter_msg)
i26_Q1 :: Algebra
i26_Q1 = Proj (map trueAttr [is_system_notification, sender, rvalue, suffix]) $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_filter

--
-- 27. Interaction: VerifySignature vs. ForwardMessages
-- 
-- * Feature: signature vs. forwardmsg
-- * Situdation: Bob sent a signed message to Jack's old email address which automatically forward 
--               message to new email address (hall@research). The signed message may be altered 
--               during the transition from old to new. 
-- 
-- * Fix by FNE: Alter the sign/verify feature to add a "Verify-At:" header giving the host where the 
--               verification was done, the time, and the identity whose signature whose signature was 
--               verified. 
-- 
-- * Fix by VDB:
--   - signature AND forwardmsg => Q1: query the forward address for receiver of msg and the sender's is_signed
--   - signature AND (NOT forwardmsg) => Q2. the sender's is_signed
--   - (NOT signature) AND forwardmsg => Q3. the forward address for receiver of msg
--   - (NOT signature) AND (NOT forwardmsg) => Empty
-- * V-Query:  (Same query with interaciton 4 SignMessage vs ForwardMessages ),
--   signature <forwardmsg<Q1, Q2>, forwardmsg <Q3, empty>>

enronVQ27 :: Algebra
enronVQ27 = AChc signature (AChc forwardmsg i4_Q1 i4_Q2) (AChc forwardmsg i4_Q3 Empty)

-- | same with i4_Q1
-- Proj_ forwardaddr, is_signed
--  Sel_ mid = midValue and rtype == "To" 
--  (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)  
i27_Q1 :: Algebra 
i27_Q1 = Proj [trueAttr forwardaddr, trueAttr is_signed, trueAttr subject] $ genRenameAlgebra $ 
          Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
            join_msg_rec_emp_foward 

-- | same with i4_Q2
-- Proj_ is_signed Sel_ mid = midValue (v_message)
i27_Q2 :: Algebra
i27_Q2 = query_is_signed

-- | same with i4_Q3
-- Proj_ forwardaddr 
--  Sel_ mid = midValue and rtype == "To" 
--   (v_message join_[mid == mid] v_recipientinfo [rvalue = email_id] v_employee [eid = eid] v_forward_msg)
i27_Q3 :: Algebra
i27_Q3 = query_recipient_forwardaddr





