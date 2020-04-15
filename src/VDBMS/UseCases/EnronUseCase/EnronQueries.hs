-- | Example Queries upon Enron Email Database
module VDBMS.UseCases.EnronUseCase.EnronQueries where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.EnronUseCase.EnronSchema
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.QueryLang.RelAlg.Variational.SmartConstructor
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))
import Database.HDBC 
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value

-- the purpose of the email database is to showcase 
-- the testing step and the use of databases in this
-- step. hence qs are written from the tester perspective
-- in spl. due to interactions among features lots of test
-- is required to ensure that the software system behaves
-- accordinly in these scenarios.

-- | the message id value we choose for entire use case
midVal :: SqlValue
midVal = SqlInt32 9138

midValue :: C.Atom
midValue = C.Val midVal

nullValue :: C.Atom 
nullValue = C.Val SqlNull

trueValue :: C.Atom
trueValue = C.Val (SqlBool True)

falseValue :: C.Atom
falseValue = C.Val (SqlBool False)

midCondition :: C.Condition
midCondition = C.Comp EQ (C.Att (qualifiedAttr messages  "mid")) midValue

midXcond :: VsqlCond
midXcond = eqAttValSqlCond mid_ midVal

temp :: Name
temp = "temp"

--
-- V-Queires for Features
--

-- 1. OLD Intent: Given a message X, return the recipient's nickname in feature ADDRESSBOOK.
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (sender, nickname, subject, body)
--   ((ρ (temp1) ((ρ (temp0) (σ (mid=X) messages)) ⋈_{temp.mid=recipientinfo.mid} recepientinfo))
--              ⋈_{temp1.eid=alias.eid} alias)
-- 
q_addressbook, q_addressbook_alt :: Algebra
q_addressbook = undefined

-- 
-- π (mid, sender, nickname, subject, body)
--   ((ρ (temp) (messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo))
--   ⋈_{temp.eid=alias.eid})
q_addressbook_alt = undefined

-- π (rvalue, nickname) (enronTemp ⋈_{temp.eid=alias.eid} alias)
-- 
q_addressbook_old, q_addressbook_alt_old :: Algebra
q_addressbook_old = 
  project ([trueAttr rvalue_
          , trueAttr nickname_ ])
          (join enronTemp
                (tRef alias)
                (joinEqCond (att2attrQual eid_ temp)
                            (att2attrQualRel eid_ alias)))

-- enronTem <-- ρ (temp) 
--                (π (eid, rvalue, mid) 
--                   ((σ (mid=X) recipientinfo) ⋈_{rvalue=email_id} employeelist)
enronTemp :: Algebra
enronTemp = renameQ temp $
  project ([trueAttr eid_
          , trueAttr rvalue_
          , trueAttr mid_])
          (join (select midXcond
                       (tRef recipientinfo))
                (tRef employeelist)
                (joinEqCond (att2attr rvalue_)
                            (att2attr email_id_)))


q_addressbook_alt_old = 
  choice addressbook q_addressbook Empty

-- 2. OLD Intent: Check if the message X is signed in feature SIGNATURE.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- 
-- 
q_signature, q_signature_alt :: Algebra
q_signature = undefined

-- 
-- 
q_signature_alt = undefined

-- π (is_signed) (σ (mid=X) messages)
-- 
q_signature_old :: Algebra
q_signature_old = 
  project (pure $ trueAttr is_signed_)
          (select midXcond (tRef messages))

-- 3. OLD Intent: Check if the message X is encrypted in feature ENCRYPTION.
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- 
-- 
q_encryption, q_encryption_alt :: Algebra
q_encryption = undefined

-- 
-- 
q_encryption_alt = undefined

-- π (is_encrypted) (σ (mid=X) messages)
-- 
q_encryption_old :: Algebra
q_encryption_old = 
  project (pure $ trueAttr is_encrypted_)
          (select midXcond (tRef messages))

-- 4. OLD Intent: Given a message X, return the recipient's autoresponder email in the feature AUTORESPONDER.        
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- 
-- 
q_autoresponder, q_autoresponder_alt :: Algebra
q_autoresponder = undefined

-- 
-- 
q_autoresponder_alt = undefined

-- π (subject, body) (enronTemp ⋈_{temp.eid=auto_msg.eid} auto_msg)
-- 
q_autoresponder_old :: Algebra
q_autoresponder_old = 
  project ([trueAttr subject_
          , trueAttr body_])
          (join enronTemp (tRef auto_msg)
                (joinEqCond (att2attrQual eid_ temp) 
                            (att2attrQualRel eid_ auto_msg)))

-- 5. OLD Intent: Given a message X, return the recipient's forward address in the feature FORWARDMESSAGES.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- 
-- 
q_forwardmessages, q_forwardmessages_alt :: Algebra
q_forwardmessages = undefined

-- 
-- 
q_forwardmessages_alt = undefined

-- π (forwardaddr) (enronTemp ⋈_{temp.eid=forward_msg.eid} forward_msg)
-- 
q_forwardmessages_old :: Algebra
q_forwardmessages_old =
  project (pure $ trueAttr forwardaddr_)
          (join enronTemp (tRef forward_msg)
                (joinEqCond (att2attrQual eid_ temp)
                            (att2attrQualRel eid_ forward_msg)))

-- 6. OLD Intent: Given a message X, return the sender's pseudonym in the feature REMAILMESSAGE.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- 
-- 
q_remailmessage, q_remailmessage_alt :: Algebra
q_remailmessage = undefined

-- 
-- 
q_remailmessage_alt = undefined

-- π (sender, pseudonym)
--   ((ρ (temp) (π (eid, sender, mid) ((σ (mid=X) messages) ⋈_{sender=email_id} employeelist))) 
--       ⋈_{temp.eid=remail_msg.eid} remail_msg)
-- 
q_remailmessage_old :: Algebra
q_remailmessage_old = 
  project ([trueAttr sender_
          , trueAttr pseudonym_])
          (join (renameQ temp
                         (project ([trueAttr eid_
                                  , trueAttr sender_
                                  , trueAttr mid_])
                                  (join (select midXcond
                                                (tRef messages))
                                        (tRef employeelist)
                                        (joinEqCond (att2attr sender_)
                                                    (att2attr email_id_)))))
                (tRef remail_msg)
                (joinEqCond (att2attrQual eid_ temp)
                            (att2attrQualRel eid_ remail_msg)))

-- 7. OLD Intent: Given the email message X, return the recipient's filter suffix in the feature FILTERMESSAGES.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- 
-- 
q_filtermessages, q_filtermessages_alt :: Algebra
q_filtermessages = undefined

-- 
-- 
q_filtermessages_alt = undefined

-- π (sender, suffix) (enronTemp ⋈_{temp.eid=filter_msg.eid} filter_msg)
-- 
q_filtermessages_old :: Algebra 
q_filtermessages_old = 
  project ([trueAttr sender_
          , trueAttr suffix_])
          (join enronTemp (tRef filter_msg)
                (joinEqCond (att2attrQual eid_ temp)
                            (att2attrQualRel eid_ filter_msg)))

-- 8. OLD Intent: Given the email message X, return the user-name of the recipient in the feature MAILHOST.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- 
-- 
q_mailhost, q_mailhost_alt :: Algebra
q_mailhost = undefined

-- 
-- 
q_mailhost_alt = undefined

-- π (rvalue, username, mailhost)
--   (enronTemp ⋈_{temp.eid=mailhost.eid} mailhost)
-- 
q_mailhost_old :: Algebra
q_mailhost_old = 
  project ([trueAttr rvalue_
          , trueAttr username_
          , trueAttr mailhost_attr_])
          (join enronTemp (tRef mail_host)
                (joinEqCond (att2attrQual eid_ temp)
                            (att2attrQualRel eid_ mail_host)))

-- --
-- -- ** V-Queries for Feature Interactions
-- --

-- 1. Purpose: Fix interaction SIGNATURE vs. FORWARDMESSAGES (1).
-- q_join_rec_emp_msg :: Rename Algebra
-- q_join_rec_emp_msg = genSubquery "q_join_rec_emp_msg" $ Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                     Join (genRenameAlgebra (joinTwoRelation messages recipientinfo "mid"))
--                          (genRenameAlgebra (tRef employeelist)) join_cond
--           where join_cond = C.Comp EQ (C.Att sender) (C.Att email_id)

-- enronQ1 :: Algebra
-- enronQ1 = Proj (map trueAttr [sender, rvalue, forwardaddr, is_signed]) $ genRenameAlgebra $ 
--             Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

-- enronVQ1 :: Algebra
-- enronVQ1 = AChc signature (AChc forwardmessages enronQ1 q_signature) q_forwardmessages

-- -- 2. Intent: Fix interaction SIGNATURE vs. REMAILMESSAGE.
-- enronQ2 :: Algebra
-- enronQ2 = Proj [trueAttr is_signed, trueAttr rvalue] $ genRenameAlgebra $ 
--                     Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                       joinTwoRelation messages recipientinfo "mid"

-- enronVQ2 :: Algebra
-- enronVQ2 = AChc (signature `F.Or` remailmessage) enronQ2 Empty

-- -- 3. Intent: Fix interaction ENCRYPTION vs. AUTORESPONDER
-- enronQ3 :: Algebra
-- enronQ3 = Proj (map trueAttr [is_encrypted, rvalue, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
--             Join q_join_rec_emp_msg (genRenameAlgebra (tRef auto_msg)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr auto_msg "eid"))
--               vautomsg_subject = qualifiedAttr auto_msg "subject"
--               vautomsg_body    = qualifiedAttr auto_msg "body"

-- enronVQ3 :: Algebra
-- enronVQ3 = AChc encryption (AChc autoresponder enronQ4 q_encryption) q_autoresponder

-- -- 4. Intent: Fix interaction ENCRYPTION vs. FORWARDMESSAGES.
-- enronQ4 :: Algebra
-- enronQ4 = Proj (map trueAttr [is_encrypted, rvalue, forwardaddr]) $ genRenameAlgebra $ 
--             Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

-- enronVQ4 :: Algebra
-- enronVQ4 = AChc encryption (AChc forwardmessages enronQ4 q_encryption) q_forwardmessages

-- -- 5. Intent: Fix interaction ENCRYPTION vs. REMAILMESSAGE.
-- enronQ5 :: Algebra
-- enronQ5 = Proj (map trueAttr [is_encrypted, sender, rvalue]) $ genRenameAlgebra $ 
--                     Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                       joinTwoRelation messages recipientinfo "mid"

-- enronVQ5 :: Algebra
-- enronVQ5 = AChc encryption (AChc remailmessage enronQ5 q_encryption) q_remailmessage

-- -- 6. Intent: Fix interaction AUTORESPONDER vs. FORWARDMESSAGES.
-- enronQ6 :: Algebra
-- enronQ6 = Proj (map trueAttr [sender, rvalue, forwardaddr, vautomsg_eid, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
--             Join (genRenameAlgebra (Join q_join_rec_emp_msg (genRenameAlgebra (tRef auto_msg)) join_cond1))
--                  (genRenameAlgebra (tRef forward_msg)) join_cond2
--         where join_cond1 = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr auto_msg "eid"))
--               join_cond2 = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))
--               vautomsg_subject = qualifiedAttr auto_msg "subject"
--               vautomsg_body    = qualifiedAttr auto_msg "body"
--               vautomsg_eid     = qualifiedAttr auto_msg "eid"
-- enronVQ6 :: Algebra
-- enronVQ6 = AChc autoresponder (AChc forwardmessages enronQ6 q_autoresponder) q_forwardmessages

-- -- 7. Intent: Fix interaction AUTORESPONDER vs. REMAILMESSAGE (1).
-- enronQ7 :: Algebra
-- enronQ7 = Proj (map trueAttr [sender, rvalue, vautomsg_subject, vautomsg_body]) $ genRenameAlgebra $ 
--             Join q_join_rec_emp_msg (genRenameAlgebra (tRef auto_msg)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr auto_msg "eid"))
--               vautomsg_subject = qualifiedAttr auto_msg "subject"
--               vautomsg_body    = qualifiedAttr auto_msg "body"

-- enronVQ7 :: Algebra
-- enronVQ7 = AChc autoresponder (AChc remailmessage enronQ7 q_autoresponder) q_remailmessage

-- -- 8. Intent: Fix interaction AUTORESPONDER vs. FILTERMESSAGES.
-- enronQ8 :: Algebra
-- enronQ8 = Proj [trueAttr is_autoresponse] $ genRenameAlgebra $ 
--                     Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                       tRef messages
-- enronVQ8 :: Algebra
-- enronVQ8 = AChc autoresponder (AChc filtermessages enronQ8 q_autoresponder) q_filtermessages
    
-- -- 9. Intent: Fix interaction AUTORESPONDER vs. MAILHOST.   
-- enronQ9 :: Algebra
-- enronQ9 = Proj [trueAttr is_system_notification] $ genRenameAlgebra $ 
--                     Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                       tRef messages
-- enronVQ9 :: Algebra
-- enronVQ9 = AChc (autoresponder `F.And` mailhost) enronQ9 Empty
         
-- -- 10. Intent: Fix interaction FORWARDMESSAGES vs. FORWARDMESSAGES.
-- enronQ10 :: Algebra
-- enronQ10 = Proj (map trueAttr [sender, rvalue, forwardaddr]) $ genRenameAlgebra $ 
--             Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

-- enronVQ10 :: Algebra
-- enronVQ10 = AChc forwardmessages enronQ10 Empty
     
-- -- 11. Intent: Fix interaction FORWARDMESSAGES vs. REMAILMESSAGE (1).
-- temp :: Rename Algebra
-- temp = genSubquery "temp" $ joinTwoRelation employeelist forward_msg "eid"

-- enronQ11 :: Algebra
-- enronQ11 = Proj (map trueAttr [email_id, forwardaddr, pseudonym]) $ genRenameAlgebra $ 
--             Join temp (genRenameAlgebra (tRef remail_msg)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "temp" "eid")) (C.Att (qualifiedAttr remail_msg "eid"))

-- enronVQ11 :: Algebra
-- enronVQ11 = AChc (remailmessage `F.Or` forwardmessages) enronQ11 Empty

-- -- 12. Intent: Fix interaction FORWARDMESSAGES vs. FILTERMESSAGES.
-- enronQ12 :: Algebra
-- enronQ12 = Proj [trueAttr forwardaddr] $ genRenameAlgebra $ 
--             Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--               joinTwoRelation employeelist forward_msg "eid"

-- enronVQ12 :: Algebra
-- enronVQ12 = AChc (forwardmessages `F.Or` filtermessages ) enronQ12 Empty

-- -- 13. Intent:Fix interaction FORWARDMESSAGES vs. MAILHOST.
-- enronQ13 :: Algebra
-- enronQ13 = Proj (map trueAttr [rvalue, username, is_forward_msg]) $ genRenameAlgebra $ 
--             Join q_join_rec_emp_msg (genRenameAlgebra (tRef mail_host)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr mail_host "eid"))

-- enronVQ13 :: Algebra
-- enronVQ13 = AChc (forwardmessages `F.Or` mailhost ) enronQ13 Empty

-- -- 14. Intent:Fix interaction REMAILMESSAGE vs. MAILHOST
-- enronQ14 :: Algebra
-- enronQ14 = Proj [trueAttr sender] $ genRenameAlgebra $ 
--                     Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                       tRef messages
-- enronVQ14 :: Algebra
-- enronVQ14 = AChc (remailmessage `F.Or` mailhost ) enronQ14 Empty

-- -- 15. Intent: Fix interaction FILTERMESSAGES vs. MAILHOST.
-- enronQ15 :: Algebra
-- enronQ15 = Proj [trueAttr is_system_notification, trueAttr sender] $ genRenameAlgebra $ 
--                     Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                       tRef messages

-- enronVQ15 :: Algebra
-- enronVQ15 = AChc (filtermessages `F.Or` mailhost ) enronQ14 Empty

-- -- 16. Intent: Fix interaction SIGNATURE vs. FORWARDMESSAGES (2).
-- enronQ16 :: Algebra
-- enronQ16 =  Proj (map trueAttr [is_signed, rvalue, forwardaddr]) $ genRenameAlgebra $ 
--             Join q_join_rec_emp_msg (genRenameAlgebra (tRef forward_msg)) join_cond
--         where join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "q_join_rec_emp_msg" "eid")) (C.Att (qualifiedAttr forward_msg "eid"))

-- enronVQ16 :: Algebra
-- enronVQ16 =  AChc signature (AChc forwardmessages enronQ16 q_signature) q_forwardmessages

