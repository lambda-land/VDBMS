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
import VDBMS.VDB.Name

-- the purpose of the email database is to showcase 
-- the testing step and the use of databases in this
-- step. hence qs are written from the tester perspective
-- in spl. due to interactions among features lots of test
-- is required to ensure that the software system behaves
-- accordinly in these scenarios.

-- | the message id value we choose for entire use case
midValue :: C.Atom
midValue = (C.Val (SqlInt32 9138))

nullValue :: C.Atom 
nullValue = C.Val SqlNull

trueValue :: C.Atom
trueValue = C.Val (SqlBool True)

falseValue :: C.Atom
falseValue = C.Val (SqlBool False)

midCondition :: C.Condition
midCondition = C.Comp EQ (C.Att (qualifiedAttr messages  "mid")) midValue

--
-- V-Queires for Features
--

-- 1. Intent: Given a message X, return the recipient's nickname in feature ADDRESSBOOK.
--
-- Queries in LaTex:
-- \begin{align*} 
-- \receid = & \pi_{(\eid, \rvalue, \midatt)} ((\sigma_{\midatt=\midvalue} \vrecipientinfo) \\
-- & \bowtie_{\rvalue = \emailid} \vemployees) \\
-- \pQ_{\addressbookf} =& \pi_{(\rvalue, \nickname)} (\receid \\
-- & \bowtie_{\receid.\eid = \valias.\eid} \valias ) \\
-- \vQ_{\addressbookf} = & \chc[\addressbookf]{\pQ_{\addressbookf}, \empRel } 
-- \end{align*} 
q_rec_eid :: Rename Algebra
q_rec_eid = genSubquery "q_rec_eid" $ Proj (map trueAttr [eid, rvalue, mid]) $ genRenameAlgebra $ 
                    Join (genRenameAlgebra (Sel (VsqlCond midCondition)  $ genRenameAlgebra $ 
                            tRef recipientinfo )) 
                         (genRenameAlgebra (tRef employeelist)) cond 
          where cond = C.Comp EQ (C.Att rvalue) (C.Att email_id)

q_addressbook :: Algebra
q_addressbook = Proj [trueAttr rvalue, trueAttr nickname] $ genRenameAlgebra $ 
                  Join q_rec_eid (genRenameAlgebra (tRef alias)) join_cond
                where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_rec_eid" "eid")) (C.Att (qualifiedAttr alias "eid"))

vq_addressbook :: Algebra
vq_addressbook = AChc addressbook q_addressbook Empty

-- 2. Intent: Check if the message X is signed in feature SIGNATURE.
-- 
-- Queries in LaTex:
-- \begin{align*}  
-- \pQ_{\signaturef}=  &\pi_{\issigned} (\sigma_{\midatt=\midvalue} \vmessages) \\
-- \vQ_{\signaturef} = & \chc[\signaturef]{\pQ_{\signaturef}, \empRel } 
-- \end{align*} 
q_signature :: Algebra
q_signature = Proj [trueAttr is_signed] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      tRef messages

vq_signature :: Algebra
vq_signature = AChc signature q_signature Empty             

-- 3. Intent: Check if the message X is encrypted in feature ENCRYPTION.
--
-- Queries in LaTex:
-- \begin{align*}  
-- \pQ_{\encryptionf}=  &\pi_{\isencrypted} (\sigma_{\midatt=\midvalue} \vmessages) \\
-- \vQ_{\encryptionf} = & \chc[\encryptionf]{\pQ_{\encryptionf}, \empRel }
-- \end{align*} 
q_encryption :: Algebra
q_encryption = Proj [trueAttr is_encrypted] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      tRef messages
vq_encryption :: Algebra
vq_encryption = AChc encryption q_encryption Empty     

-- 4. Intent: Given a message X, return the recipient's autoresponder email in the feature AUTORESPONDER.        
--
-- Queries in LaTex:
-- \begin{align*}  
-- \pQ_{\autoresponderf}= & \pi_{(\vautomsg.\subject, \vautomsg.\body)} (\receid \\
-- & \bowtie_{\receid.\eid = \vautomsg.\eid} \vautomsg ) \\
-- \vQ_{\autoresponderf} = & \chc[\autoresponderf]{\pQ_{\autoresponderf}, \empRel } 
-- \end{align*} 
q_autoresponder :: Algebra
q_autoresponder = 
            Proj [ trueAttr vautomsg_subject, trueAttr vautomsg_body] $ genRenameAlgebra $ 
            Join q_rec_eid (genRenameAlgebra (tRef auto_msg)) join_cond
        where vautomsg_subject = qualifiedAttr auto_msg "subject"
              vautomsg_body    = qualifiedAttr auto_msg "body"
              join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_rec_eid" "eid")) (C.Att (qualifiedAttr auto_msg "eid"))

vq_autoresponder :: Algebra
vq_autoresponder = AChc autoresponder q_autoresponder Empty    

-- 5. Intent: Given a message X, return the recipient's forward address in the feature FORWARDMESSAGES.
-- 
-- Queries in LaTex:
-- \begin{align*} 
-- \pQ_{\forwardmsgf}= & \pi_{\forwardaddr} (\receid \\
-- & \bowtie_{\receid.\eid = \vforwardmsg.\eid} \vforwardmsg ) \\ 
-- \vQ_{\forwardmsgf} = & \chc[\forwardmsgf]{\pQ_{\forwardmsgf}, \empRel } 
-- \end{align*}  
q_forwardmessages :: Algebra
q_forwardmessages =             
            Proj [ trueAttr forwardaddr] $ genRenameAlgebra $ 
            Join q_rec_eid (genRenameAlgebra (tRef forward_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_rec_eid" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

vq_forwardmessages :: Algebra
vq_forwardmessages = AChc forwardmessages q_forwardmessages Empty    

-- 6. Intent: Given a message X, return the sender's pseudonym in the feature REMAILMESSAGE.
-- 
-- Queries in LaTex:
-- \begin{align*} 
-- \sendereid = & \pi_{(\eid, \sender, \midatt)} ((\sigma_{\midatt=\midvalue} \vmessages) \\
-- & \bowtie_{\sender = \emailid} \vemployees) \\
-- \pQ_{\remailmsgf}= & \pi_{(\sender, \pseudonym)} (\sendereid \\
-- & \bowtie_{\sendereid.\eid = \vremailmsg.\eid} \vremailmsg ) \\
-- \vQ_{\remailmsgf}= & \chc[\remailmsgf]{\pQ_{\remailmsgf}, \empRel } 
-- \end{align*} 
q_sender_eid :: Rename Algebra
q_sender_eid = genSubquery "q_sender_eid" $ Proj (map trueAttr [eid, sender, mid]) $ genRenameAlgebra $ 
                    Join (genRenameAlgebra (Sel (VsqlCond midCondition)  $ genRenameAlgebra $ 
                            tRef messages )) 
                         (genRenameAlgebra (tRef employeelist)) cond 
          where cond = C.Comp EQ (C.Att sender) (C.Att email_id)

q_remailmessage :: Algebra
q_remailmessage = 
            Proj [ trueAttr sender, trueAttr pseudonym] $ genRenameAlgebra $ 
            Join q_sender_eid (genRenameAlgebra (tRef remail_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_sender_eid" "eid")) (C.Att (qualifiedAttr remail_msg "eid"))

vq_remailmessage :: Algebra
vq_remailmessage = AChc remailmessage q_remailmessage Empty  

-- 7. Intent: Given the email message X, return the recipient's filter suffix in the feature FILTERMESSAGES.
-- 
-- Queries in LaTex:
-- \begin{align*}
-- \pQ_{\filtermsgf}=  & \pi_{\sender, \suffix} (\receid \\
-- &\bowtie_{\receid.\eid = \vfiltermsg.\eid} \vfiltermsg )\\
-- \vQ_{\filtermsgf} = & \chc[\filtermsgf]{\pQ_{\filtermsgf}, \empRel }  
-- \end{align*} 
q_filtermessages :: Algebra 
q_filtermessages = 
            Proj [ trueAttr sender, trueAttr suffix] $ genRenameAlgebra $ 
            Join q_rec_eid (genRenameAlgebra (tRef filter_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_rec_eid" "eid")) (C.Att (qualifiedAttr filter_msg "eid"))

vq_filtermessages :: Algebra
vq_filtermessages = AChc filtermessages q_filtermessages Empty  

-- 8. Intent: Given the email message X, return the user-name of the recipient in the feature MAILHOST.
-- 
-- Queries in LaTex:
-- \begin{align*} 
-- \pQ_{\mailhostf}= & \pi_{(\rvalue, \username, \mailhost)} (\receid \\
-- & \bowtie_{\receid.\eid = \vmailhost.\eid} \vmailhost ) \\ 
-- \vQ_{\mailhostf} = & \chc[\mailhostf]{\pQ_{\mailhostf}, \empRel } 
-- \end{align*}  
q_mailhost :: Algebra
q_mailhost = 
            Proj (map trueAttr [rvalue, username, mailhost_attr]) $ genRenameAlgebra $ 
            Join q_rec_eid (genRenameAlgebra (tRef mail_host)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_rec_eid" "eid")) (C.Att (qualifiedAttr mail_host "eid"))

vq_mailhost :: Algebra
vq_mailhost = AChc mailhost q_mailhost Empty  

--
-- ** V-Queries for Feature Interactions
--

-- 1. Intent: Fix interaction SIGNATURE vs. FORWARDMESSAGES (1).
q_join_rec_emp_msg :: Rename Algebra
q_join_rec_emp_msg = genSubquery "q_join_rec_emp_msg" $ Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                    Join (genRenameAlgebra (joinTwoRelation messages recipientinfo "mid"))
                         (genRenameAlgebra (tRef employeelist)) join_cond
          where join_cond = C.Comp EQ (C.Att sender) (C.Att email_id)

enronQ1 :: Algebra
enronQ1 = Proj (map trueAttr [sender, rvalue, forwardaddr, is_signed]) $ genRenameAlgebra $ 
            Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

enronVQ1 :: Algebra
enronVQ1 = AChc signature (AChc forwardmessages enronQ1 q_signature) q_forwardmessages

-- 2. Intent: Fix interaction SIGNATURE vs. REMAILMESSAGE.
enronQ2 :: Algebra
enronQ2 = Proj [trueAttr is_signed, trueAttr rvalue] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      joinTwoRelation messages recipientinfo "mid"

enronVQ2 :: Algebra
enronVQ2 = AChc (signature `F.Or` remailmessage) enronQ2 Empty

-- 3. Intent: Fix interaction ENCRYPTION vs. AUTORESPONDER
enronQ3 :: Algebra
enronQ3 = Proj (map trueAttr [is_encrypted, rvalue, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
            Join q_join_rec_emp_msg (genRenameAlgebra (tRef auto_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr auto_msg "eid"))
              vautomsg_subject = qualifiedAttr auto_msg "subject"
              vautomsg_body    = qualifiedAttr auto_msg "body"

enronVQ3 :: Algebra
enronVQ3 = AChc encryption (AChc autoresponder enronQ4 q_encryption) q_autoresponder

-- 4. Intent: Fix interaction ENCRYPTION vs. FORWARDMESSAGES.
enronQ4 :: Algebra
enronQ4 = Proj (map trueAttr [is_encrypted, rvalue, forwardaddr]) $ genRenameAlgebra $ 
            Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

enronVQ4 :: Algebra
enronVQ4 = AChc encryption (AChc forwardmessages enronQ4 q_encryption) q_forwardmessages

-- 5. Intent: Fix interaction ENCRYPTION vs. REMAILMESSAGE.
enronQ5 :: Algebra
enronQ5 = Proj (map trueAttr [is_encrypted, sender, rvalue]) $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      joinTwoRelation messages recipientinfo "mid"

enronVQ5 :: Algebra
enronVQ5 = AChc encryption (AChc remailmessage enronQ5 q_encryption) q_remailmessage

-- 6. Intent: Fix interaction AUTORESPONDER vs. FORWARDMESSAGES.
enronQ6 :: Algebra
enronQ6 = Proj (map trueAttr [sender, rvalue, forwardaddr, vautomsg_eid, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
            Join (genRenameAlgebra (Join q_join_rec_emp_msg (genRenameAlgebra (tRef auto_msg)) join_cond1))
                 (genRenameAlgebra (tRef forward_msg)) join_cond2
        where join_cond1 = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr auto_msg "eid"))
              join_cond2 = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))
              vautomsg_subject = qualifiedAttr auto_msg "subject"
              vautomsg_body    = qualifiedAttr auto_msg "body"
              vautomsg_eid     = qualifiedAttr auto_msg "eid"
enronVQ6 :: Algebra
enronVQ6 = AChc autoresponder (AChc forwardmessages enronQ6 q_autoresponder) q_forwardmessages

-- 7. Intent: Fix interaction AUTORESPONDER vs. REMAILMESSAGE (1).
enronQ7 :: Algebra
enronQ7 = Proj (map trueAttr [sender, rvalue, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
            Join q_join_rec_emp_msg (genRenameAlgebra (tRef auto_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr auto_msg "eid"))
              vautomsg_subject = qualifiedAttr auto_msg "subject"
              vautomsg_body    = qualifiedAttr auto_msg "body"

enronVQ7 :: Algebra
enronVQ7 = AChc autoresponder (AChc remailmessage enronQ7 q_autoresponder) q_remailmessage

-- 8. Intent: Fix interaction AUTORESPONDER vs. FILTERMESSAGES.
enronQ8 :: Algebra
enronQ8 = Proj [trueAttr is_autoresponse] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      tRef messages
enronVQ8 :: Algebra
enronVQ8 = AChc autoresponder (AChc filtermessages enronQ8 q_autoresponder) q_filtermessages
    
-- 9. Intent: Fix interaction AUTORESPONDER vs. MAILHOST.   
enronQ9 :: Algebra
enronQ9 = Proj [trueAttr is_system_notification] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      tRef messages
enronVQ9 :: Algebra
enronVQ9 = AChc (autoresponder `F.And` mailhost) enronQ9 Empty
         
-- 10. Intent: Fix interaction FORWARDMESSAGES vs. FORWARDMESSAGES.
enronQ10 :: Algebra
enronQ10 = Proj (map trueAttr [sender, rvalue, forwardaddr]) $ genRenameAlgebra $ 
            Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

enronVQ10 :: Algebra
enronVQ10 = AChc forwardmessages enronQ10 Empty
     
-- 11. Intent: Fix interaction FORWARDMESSAGES vs. REMAILMESSAGE (1).
temp :: Rename Algebra
temp = genSubquery "temp" $ joinTwoRelation employeelist forward_msg "eid"

enronQ11 :: Algebra
enronQ11 = Proj (map trueAttr [email_id, forwardaddr, pseudonym]) $ genRenameAlgebra $ 
            Join temp (genRenameAlgebra (tRef remail_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "temp" "eid")) (C.Att (qualifiedAttr remail_msg "eid"))

enronVQ11 :: Algebra
enronVQ11 = AChc (remailmessage `F.Or` forwardmessages) enronQ11 Empty

-- 12. Intent: Fix interaction FORWARDMESSAGES vs. FILTERMESSAGES.
enronQ12 :: Algebra
enronQ12 = Proj [trueAttr forwardaddr] $ genRenameAlgebra $ 
            Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
              joinTwoRelation employeelist forward_msg "eid"

enronVQ12 :: Algebra
enronVQ12 = AChc (forwardmessages `F.Or` filtermessages ) enronQ12 Empty

-- 13. Intent:Fix interaction FORWARDMESSAGES vs. MAILHOST.
enronQ13 :: Algebra
enronQ13 = Proj (map trueAttr [rvalue, username, is_forward_msg]) $ genRenameAlgebra $ 
            Join q_join_rec_emp_msg (genRenameAlgebra (tRef mail_host)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr mail_host "eid"))

enronVQ13 :: Algebra
enronVQ13 = AChc (forwardmessages `F.Or` mailhost ) enronQ13 Empty

-- 14. Intent:Fix interaction REMAILMESSAGE vs. MAILHOST
enronQ14 :: Algebra
enronQ14 = Proj [trueAttr sender] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      tRef messages
enronVQ14 :: Algebra
enronVQ14 = AChc (remailmessage `F.Or` mailhost ) enronQ14 Empty

-- 15. Intent: Fix interaction FILTERMESSAGES vs. MAILHOST.
enronQ15 :: Algebra
enronQ15 = Proj [trueAttr is_system_notification, trueAttr sender] $ genRenameAlgebra $ 
                    Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
                      tRef messages

enronVQ15 :: Algebra
enronVQ15 = AChc (filtermessages `F.Or` mailhost ) enronQ14 Empty

-- 16. Intent: Fix interaction SIGNATURE vs. FORWARDMESSAGES (2).
enronQ16 :: Algebra
enronQ16 =  Proj (map trueAttr [is_signed, rvalue, forwardaddr]) $ genRenameAlgebra $ 
            Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
        where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

enronVQ16 :: Algebra
enronVQ16 =  AChc signature (AChc forwardmessages enronQ16 q_signature) q_forwardmessages

