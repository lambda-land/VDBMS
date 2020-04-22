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

trueValue :: SqlValue
trueValue = --C.Val (
  SqlBool True

falseValue :: SqlValue
falseValue = --C.Val (
  SqlBool False
  -- )

midCondition :: C.Condition
midCondition = C.Comp EQ (C.Att (qualifiedAttr messages  "mid")) midValue

midXcond :: VsqlCond
midXcond = eqAttValSqlCond mid_ midVal

temp :: Name
temp = "temp"

--
-- V-Queires considering one feature at a time and what is needed to be extracted
-- from the DB when the feature is enabled.
--

-- 
-- INTENT: the intent for all these queries is constructing the header of an email.
-- For most cases the header is being constructed for email X that has been sent 
-- from sender A to reciever B. However, there are some exceptions:
-- * for autoresponder and forwardmsg features the header being constructed is for 
--   the email that is to respond to email X.
-- * for filtermsg and mailhost features extra information is extracted from the DB
--   to decide whether to accept the recieving email X on the reciver side or not.
-- Note: the order of the projected attribute list is always considered to match 
--       the header (as much of it as it contains), i.e., the first attribute 
--       always denotes the sender.

-- 
-- The header inculdes the following infromation:
-- sender, recieved_by, is_signed, signature, is_encrypted, encryption_key,
-- subject, body, mailhost, should_filter, verification_status, verified_at,
-- signed_by
-- Note: not all fields of the header can be extracted from the DB. Last four
--       fields can be created from the data from the DB and some checks. 
-- Note: one can add more fields to the header as they please.
-- 

-- 
-- Note: the main queries are named as q_featurename which will be used for debugging
--       the behaviour of different parts of VDBMS. These queries can be used in various
--       parts of development code to retrieve information from the DB and process it as
--       desired. The q_featurename_alt are for runtime evaluation of VDBMS.
-- 

-- 0. Basic query when non of the features are enabled.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (sender, rvalue, subject, body) ((σ (mid=X) messages) 
--                                    ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
-- 
q_basic, q_basic_alt :: Algebra
q_basic = 
  project (fmap trueAttr [sender_, rvalue_, subject_, body_])
          (join (select midXcond $ tRef messages)
                (tRef recipientinfo)
                (joinEqCond (att2attrQualRel mid_ messages)
                            (att2attrQualRel mid_ recipientinfo)))

-- π (sender, rvalue, subject, body) 
--   (messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
-- 
q_basic_alt =
  project (fmap trueAttr [sender_, rvalue_, subject_, body_])
          (join (tRef messages)
                (tRef recipientinfo)
                (joinEqCond (att2attrQualRel mid_ messages)
                            (att2attrQualRel mid_ recipientinfo)))

-- 1. OLD Intent: Given a message X, return the recipient's nickname in feature ADDRESSBOOK.
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (sender, nickname, subject, body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recepientinfo)
--     ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--     ⋈_{recipientinfo.eid=alias.eid} alias)
-- 
q_addressbook, q_addressbook_alt :: Algebra
q_addressbook = 
  project ([trueAttr sender_
          , trueAttr nickname_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (select midXcond (tRef messages))
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef alias)
                (joinEqCond (att2attrQualRel eid_ recipientinfo)
                            (att2attrQualRel eid_ alias)))

-- 
-- π (messages.mid, sender, nickname, subject, body)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo) 
--    ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--    ⋈_{recipientinfo.eid=alias.eid} alias)
q_addressbook_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr sender_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (tRef messages)
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef alias)
                (joinEqCond (att2attrQualRel eid_ recipientinfo)
                            (att2attrQualRel eid_ alias)))

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
-- π (sender, rvalue, is_signed, verification_key, subject, body)
--   (((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--    ⋈_{sender=email_id} employeelist)
-- 
q_signature, q_signature_alt :: Algebra
q_signature = 
  project ([trueAttr sender_
          , trueAttr rvalue_
          , trueAttr is_signed_
          , trueAttr verification_key_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (select midXcond (tRef messages))
                      (tRef recipientinfo)
                      (joinEqCond (att2attrQualRel mid_ messages)
                                  (att2attrQualRel mid_ recipientinfo)))
                (tRef employeelist)
                (joinEqCond (att2attrQualRel sender_ messages)
                            (att2attrQualRel email_id_ employeelist)))

-- 
-- π (messages.mid, sender, rvalue, is_signed, verification_key, subject, body)
--   ((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo) 
--    ⋈_{sender=email_id} employeelist)
q_signature_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr is_signed_
          , trueAttr verification_key_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (tRef messages)
                      (tRef recipientinfo)
                      (joinEqCond (att2attrQualRel mid_ messages)
                                  (att2attrQualRel mid_ recipientinfo)))
                (tRef employeelist)
                (joinEqCond (att2attrQualRel sender_ messages)
                            (att2attrQualRel email_id_ employeelist)))


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
-- π (sender, rvalue, is_encrypted, public_key, subject, body)
--   (((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--    ⋈_{sender=email_id} employeelist)
-- 
q_encryption, q_encryption_alt :: Algebra
q_encryption = 
  project ([trueAttr sender_
          , trueAttr rvalue_
          , trueAttr is_encrypted_
          , trueAttr public_key_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (select midXcond (tRef messages))
                      (tRef recipientinfo)
                      (joinEqCond (att2attrQualRel mid_ messages)
                                  (att2attrQualRel mid_ recipientinfo)))
                (tRef employeelist)
                (joinEqCond (att2attrQualRel sender_ messages)
                            (att2attrQualRel email_id_ employeelist)))

-- 
-- π (messages.mid, sender, rvalue, is_encrypted, public_key, subject, body)
--   ((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo) 
--     ⋈_{sender=email_id} employeelist)
q_encryption_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr is_encrypted_
          , trueAttr public_key_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (tRef messages)
                      (tRef recipientinfo)
                      (joinEqCond (att2attrQualRel mid_ messages)
                                  (att2attrQualRel mid_ recipientinfo)))
                (tRef employeelist)
                (joinEqCond (att2attrQualRel sender_ messages)
                            (att2attrQualRel email_id_ employeelist)))

-- π (is_encrypted) (σ (mid=X) messages)
-- 
q_encryption_old :: Algebra
q_encryption_old = 
  project (pure $ trueAttr is_encrypted_)
          (select midXcond (tRef messages))

-- 4. OLD Intent: Given a message X, return the recipient's autoresponder email in the feature AUTORESPONDER.        
--
-- The rvalue is the sender and sender is the reciever.
-- It is constructing the auto respond email to email X.
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (rvalue, sender, is_system_notification, auto_msg.subject, auto_msg.body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=auto_msg.eid} auto_msg)
-- 
q_autoresponder, q_autoresponder_alt :: Algebra
q_autoresponder = 
  project ([trueAttr rvalue_
          , trueAttr sender_
          , trueAttr is_system_notification_
          , trueAttrQualRel subject_ auto_msg
          , trueAttrQualRel body_ auto_msg])
          (join (join (join (select midXcond (tRef messages))
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef auto_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ auto_msg)))

-- 
-- π (messages.mid, rvalue, sender, is_system_notification, auto_msg.subject, auto_msg.body)
--   (((messages ⋈_{messages.mid=temp.mid} recipientinfo) 
--     ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=auto_msg.eid} auto_msg)
q_autoresponder_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr rvalue_
          , trueAttr sender_
          , trueAttr is_system_notification_
          , trueAttrQualRel subject_ auto_msg
          , trueAttrQualRel body_ auto_msg])
          (join (join (join (tRef messages)
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef auto_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ auto_msg)))

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
-- π (rvalue, forwardaddr, subject, body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
-- 
q_forwardmessages, q_forwardmessages_alt :: Algebra
q_forwardmessages = 
  project ([trueAttr rvalue_
          , trueAttr forwardaddr_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (select midXcond (tRef messages))
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef forward_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ forward_msg)))

-- 
-- π (messages.mid, rvalue, forwardaddr, subject, body)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
q_forwardmessages_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr rvalue_
          , trueAttr forwardaddr_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (tRef messages)
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef forward_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ forward_msg)))


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
-- Note that pseudonym is the sender, rvalue is the reciver.
-- It is constructing the header for the message to be forwarded.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (pseudonym, sender, rvalue, subject, body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{messages.sender=employeelist.email_id} employeelist) 
--     ⋈_{employeelist.eid=remailmessage.eid} remail_msg)
-- 
q_remailmessage, q_remailmessage_alt :: Algebra
q_remailmessage = 
  project ([trueAttr pseudonym_
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (select midXcond (tRef messages))
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel sender_ messages)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef remail_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ remail_msg)))

-- 
-- π (messages.mid, pseudonym, sender, rvalue, subject, body)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{messages.sender=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=remailmessage.eid} remail_msg)
q_remailmessage_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr pseudonym_
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (tRef messages)
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel sender_ messages)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef remail_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ remail_msg)))

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
-- It (the email server) checks the suffix of the reciver and if the sender isn't included in it
-- it delivers the email to the reciever, otherwise it rejects it.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (sender, rvalue, suffix, subject, body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=filter_msg.eid} filter_msg)
-- 
q_filtermessages, q_filtermessages_alt :: Algebra
q_filtermessages = 
  project ([trueAttr sender_
          , trueAttr rvalue_
          , trueAttr suffix_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (select midXcond (tRef messages))
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef filter_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ filter_msg)))

-- 
-- π (messages.mid, sender, rvalue, suffix, subject, body)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=filter_msg.eid} filter_msg)
q_filtermessages_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr suffix_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (tRef messages)
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef filter_msg)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ filter_msg)))

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
-- It checks if mailhost of the sender is in the set of mailhost for the reciever,
-- it so it delivers the email to the reciever, otherwise it rejects it.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (sender, rvalue, username, mailhost, subject, body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=mail_host.eid} mail_host)
-- 
q_mailhost, q_mailhost_alt :: Algebra
q_mailhost = 
  project ([trueAttr sender_
          , trueAttr rvalue_
          , trueAttr username_
          , trueAttr mailhost_attr_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (select midXcond (tRef messages))
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef mail_host)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ mail_host)))

-- 
-- π (messages.mid, sender, rvalue, username, mailhost, subject, body)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=mail_host.eid} mail_host)
q_mailhost_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr username_
          ,trueAttr mailhost_attr_
          , trueAttr subject_
          , trueAttr body_])
          (join (join (join (tRef messages)
                            (tRef recipientinfo)
                            (joinEqCond (att2attrQualRel mid_ messages)
                                        (att2attrQualRel mid_ recipientinfo)))
                      (tRef employeelist)
                      (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                  (att2attrQualRel email_id_ employeelist)))
                (tRef mail_host)
                (joinEqCond (att2attrQualRel eid_ employeelist)
                            (att2attrQualRel eid_ mail_host)))

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

-- 1. Purpose: Generate the header for an email when both SIGNATURE and FORWARDMESSAGES
--             have been enabled(1). The header is for the email to be forwarded.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- signature ∧ forwardmessages ⟪ 
-- π (rvalue, forwardaddr, emp1.is_signed, emp1.verification_key)
--   (((((σ (mid = X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--       ⋈_{messages.sender=emp1.email_id} (ρ (emp1) employeelist))
--       ⋈_{recipientinfo.rvalue=emp2.email_id} (ρ (emp2) employeelist))
--       ⋈_{emp2.eid=forward_msg.eid} forward_msg)
-- , signature ⟪ q_signature, forwardmessages ⟪ q_forwardmessages, q_basic ⟫⟫⟫
-- 
enronQ1, enronQ1_alt :: Algebra
enronQ1 = 
  choice (F.And signature forwardmessages)
         (project ([trueAttr rvalue_
                  , trueAttr forwardaddr_
                  , trueAttrQual is_signed_ emp1Name
                  , trueAttrQual verification_key_ emp1Name
                  , trueAttr subject_
                  , trueAttr body_])
                  (subq))
         (choice signature
                 q_signature
                 (choice forwardmessages
                         q_forwardmessages
                         q_basic))
    where
      subq = 
        join (join (join (join (select midXcond $ tRef messages)
                               (tRef recipientinfo)
                               (joinEqCond (att2attrQualRel mid_ messages)
                                           (att2attrQualRel mid_ recipientinfo)))
                         (renameQ emp1Name (tRef employeelist))
                         (joinEqCond (att2attrQualRel sender_ messages)
                                     (att2attrQual email_id_ emp1Name)))
                   (renameQ emp2Name (tRef employeelist))
                   (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                               (att2attrQual email_id_ emp2Name)))
             (tRef forward_msg)
             (joinEqCond (att2attrQual eid_ emp2Name)
                         (att2attrQualRel eid_ forward_msg))
      emp1Name = "emp1"
      emp2Name = "emp2"


-- checks for type system:
-- have the same name for emp1 and emp2 --> type error
-- dont have names for emp1 and emp2
-- dont have qualifier for email_id attribute in join condition
-- dont have qualifier for is_signed attribute in the projected attribute list

-- signature ∧ forwardmessages ⟪ 
-- π (messages.mid, rvalue, forwardaddr, emp1.is_signed, emp1.verification_key)
--   ((((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--       ⋈_{messages.sender=emp1.email_id} (ρ (emp1) employeelist))
--       ⋈_{recipientinfo.rvalue=emp2.email_id} (ρ (emp2) employeelist))
--       ⋈_{emp2.eid=forward_msg.eid} forward_msg)
-- , signature ⟪ q_signature_alt, forwardmessages ⟪ q_forwardmessages_alt, q_basic_alt⟫⟫⟫
-- 
enronQ1_alt = 
  choice (F.And signature forwardmessages)
         (project ([trueAttrQualRel mid_ messages
                  , trueAttr rvalue_
                  , trueAttr forwardaddr_
                  , trueAttrQual is_signed_ emp1Name
                  , trueAttrQual verification_key_ emp1Name
                  , trueAttr subject_
                  , trueAttr body_])
                  (subq))
         (choice signature
                 q_signature_alt
                 (choice forwardmessages
                         q_forwardmessages_alt
                         q_basic_alt))
    where
      subq = 
        join (join (join (join (tRef messages)
                               (tRef recipientinfo)
                               (joinEqCond (att2attrQualRel mid_ messages)
                                           (att2attrQualRel mid_ recipientinfo)))
                         (renameQ emp1Name (tRef employeelist))
                         (joinEqCond (att2attrQualRel sender_ messages)
                                     (att2attrQual email_id_ emp1Name)))
                   (renameQ emp2Name (tRef employeelist))
                   (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                               (att2attrQual email_id_ emp2Name)))
             (tRef forward_msg)
             (joinEqCond (att2attrQual eid_ emp2Name)
                         (att2attrQualRel eid_ forward_msg))
      emp1Name = "emp1"
      emp2Name = "emp2"

-- 2. Purpose: Generate the header for an email when both SIGNATURE and REMAILMESSAGE
--             have been enabled. The header is for the email that may be delivered
--             to the reciever, if is_signed is enabled the sender will get an UI 
--             warning, otherwise the email will be delivered to the reciever where
--             the sender name is their pseudonym.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- signature ∧ remailmessage ⟪π (sender) (σ (mid=X ∧ is_signed=True) messages),
--   signature ⟪q_signature, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- 
enronQ2part1, enronQ2part1_alt :: Algebra
enronQ2part1 = 
  choice (F.And signature remailmessage)
         (project (pure $ trueAttr sender_)
                  (select (VsqlAnd midXcond (eqAttValSqlCond is_signed_ trueValue)) 
                          (tRef messages)))
         (choice signature q_signature (choice remailmessage q_remailmessage q_basic))

-- signature ∧ remailmessage ⟪π (mid, sender) (σ (is_signed=True) messages),
--   signature ⟪q_signature_alt, remailmessage⟪ q_remailmessage_alt, q_basic_alt⟫⟫⟫
-- 
enronQ2part1_alt = 
  choice (F.And signature remailmessage)
         (project (fmap trueAttr [mid_, sender_])
                  (select (eqAttValSqlCond is_signed_ trueValue)
                          (tRef messages)))
         (choice signature 
                 q_signature_alt 
                 (choice remailmessage q_remailmessage_alt q_basic_alt))

-- signature ∧ remailmessage ⟪subq_similar_to_remialmessage_q,
--   signature ⟪q_signature, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- subq_similar_to_remialmessage_q ← π (pseudonym, sender, rvalue, subject, body)
--   ((((σ (mid=X ∧ ¬is_signed) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{messages.sender=employeelist.email_id} employeelist) 
--     ⋈_{employeelist.eid=remailmessage.eid} remail_msg)
-- 
enronQ2part2, enronQ2part2_alt :: Algebra
enronQ2part2 = 
  choice (F.And signature remailmessage)
         subq
         (choice signature q_signature (choice remailmessage q_remailmessage q_basic))
    where
      subq = 
        project ([trueAttr pseudonym_
                , trueAttr sender_
                , trueAttr rvalue_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (select (VsqlAnd midXcond 
                                                   (eqAttValSqlCond is_signed_ falseValue)) 
                                          (tRef messages))
                                  (tRef recipientinfo)
                                  (joinEqCond (att2attrQualRel mid_ messages)
                                              (att2attrQualRel mid_ recipientinfo)))
                            (tRef employeelist)
                            (joinEqCond (att2attrQualRel sender_ messages)
                                        (att2attrQualRel email_id_ employeelist)))
                      (tRef remail_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ remail_msg)))



-- signature ∧ remailmessage ⟪subq_similar_to_remialmessage_q,
--   signature ⟪q_signature_alt, remailmessage⟪ q_remailmessage_alt, q_basic_alt⟫⟫⟫
-- ⟪subq_similar_to_remialmessage_q ← π (messages.mid, pseudonym, sender, rvalue, subject, body, suffix)
--   ((((σ (¬ is_signed) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=filter_msg.eid} filter_msg)
-- 
enronQ2part2_alt = 
  choice (F.And signature remailmessage)
         subq
         (choice signature 
                 q_signature_alt 
                 (choice remailmessage q_remailmessage_alt q_basic_alt))
    where
      subq =
        project ([trueAttrQualRel mid_ messages
                , trueAttr pseudonym_
                , trueAttr sender_
                , trueAttr rvalue_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (select (eqAttValSqlCond is_signed_ falseValue) 
                                          (tRef messages))
                                  (tRef recipientinfo)
                                  (joinEqCond (att2attrQualRel mid_ messages)
                                              (att2attrQualRel mid_ recipientinfo)))
                            (tRef employeelist)
                            (joinEqCond (att2attrQualRel sender_ messages)
                                        (att2attrQualRel email_id_ employeelist)))
                      (tRef remail_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ remail_msg)))

-- 3. Purpose: Generate the header for an email when both ENCRYPTION and AUTORESPONDER
--             have been enabled. The header is for the email to be autoresponded.
--             Note that whether the email is encrypted or not, it doesn't matter
--             because either way the header shouldn't include the security info in 
--             the header of the email is being sent out.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- encryption ∧ autoresponder ⟪ q_autoresponder,
--    encryption ⟪ q_encryption, autoresponded⟪ q_autoresponder, q_basic⟫⟫⟫
-- 
enronQ3, enronQ3_alt :: Algebra
enronQ3 = 
  choice (F.And encryption autoresponder)
         q_autoresponder
         (choice encryption q_encryption (choice autoresponder q_autoresponder q_basic))

-- encryption ∧ autoresponder ⟪ q_autoresponder_alt,
--    encryption ⟪ q_encryption_alt, autoresponded⟪ q_autoresponder_alt, q_basic_alt⟫⟫⟫
-- 
enronQ3_alt = 
  choice (F.And encryption autoresponder)
         q_autoresponder_alt
         (choice encryption 
                 q_encryption_alt 
                 (choice autoresponder q_autoresponder_alt q_basic_alt))

-- 4. Purpose: Generate the header for an email when both ENCRYPTION and FORWARDMESSAGES
--             have been enabled. The header is for the email that may be forwarded.
--             If is_encrypted is enabled the reciever of email X (whose about to 
--             forward the message) will get an UI 
--             warning, otherwise the email will be forwarded.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- encryption ∧ forwardmessages ⟪π (rvalue) (σ (mid=X ∧ is_encrypted) messages),
--    encryption⟪ q_encryption,forwardmessages⟪ q_forwardmessages, q_basic⟫⟫⟫
-- 
enronQ4part1, enronQ4part1_alt :: Algebra
enronQ4part1 = 
  choice (F.And encryption forwardmessages)
         (project (pure $ trueAttr rvalue_)
                  (select (VsqlAnd midXcond 
                                   (eqAttValSqlCond is_encrypted_ trueValue))
                          (tRef messages)))
         (choice encryption 
                 q_encryption
                 (choice forwardmessages
                         q_forwardmessages
                         q_basic))

-- encryption ∧ forwardmessages ⟪π (mid, rvalue) (σ (is_encrypted) messages),
--    encryption⟪ q_encryption_alt,forwardmessages⟪ q_forwardmessages_alt, q_basic_alt⟫⟫⟫
-- 
enronQ4part1_alt = 
  choice (F.And encryption forwardmessages)
         (project (fmap trueAttr [mid_, rvalue_])
                  (select (eqAttValSqlCond is_encrypted_ trueValue)
                          (tRef messages)))
         (choice encryption 
                 q_encryption_alt
                 (choice forwardmessages
                         q_forwardmessages_alt
                         q_basic_alt))

-- 
-- encryption ∧ forwardmessages ⟪subq_similar_to_forwardmsg_q,
-- forwardmessages⟪ q_forwardmessages, q_basic⟫⟫
-- ⟪subq_similar_to_forwardmsg_q ← π (rvalue, forwardaddr, subject, body)
--   ((((σ (mid=X ∧ ¬is_encrypted) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
enronQ4part2, enronQ4part2_alt :: Algebra
enronQ4part2 = 
  choice (F.And encryption forwardmessages)
         subq
         (choice forwardmessages
                 q_forwardmessages
                 q_basic)
    where
      subq = 
        project ([trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (select (VsqlAnd midXcond 
                                                   (eqAttValSqlCond is_encrypted_ falseValue))
                                          (tRef messages))
                                  (tRef recipientinfo)
                                  (joinEqCond (att2attrQualRel mid_ messages)
                                              (att2attrQualRel mid_ recipientinfo)))
                            (tRef employeelist)
                            (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                        (att2attrQualRel email_id_ employeelist)))
                      (tRef forward_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ forward_msg)))


-- 
-- encryption ∧ forwardmessages ⟪subq_similar_to_forwardmsg_q,
-- forwardmessages⟪ q_forwardmessages, q_basic⟫⟫
-- ⟪subq_similar_to_forwardmsg_q ← π (messages.mid, rvalue, forwardaddr, subject, body)
--   ((((σ (¬is_encrypted) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
enronQ4part2_alt = 
  choice (F.And encryption forwardmessages)
         subq
         (choice forwardmessages
                 q_forwardmessages_alt
                 q_basic_alt)
    where
      subq =
        project ([trueAttrQualRel mid_ messages
                , trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (select (eqAttValSqlCond is_encrypted_ falseValue)
                                          (tRef messages))
                                  (tRef recipientinfo)
                                  (joinEqCond (att2attrQualRel mid_ messages)
                                              (att2attrQualRel mid_ recipientinfo)))
                            (tRef employeelist)
                            (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                        (att2attrQualRel email_id_ employeelist)))
                      (tRef forward_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ forward_msg)))

-- 5. Purpose: Generate the header for an email when both ENCRYPTION and REMAILMESSAGE
--             have been enabled. Since enrcyption is enabled the remailer doesn't 
--             include the sender information in the header however it still needs
--             the public key to decode the email. 
-- 
-- #variants = 
-- #unique_variants =
-- 
-- encryption ∧ remailmessage⟪ subq_enc_remail_qs_combined,
--    encryption⟪ q_encryption, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- subq_enc_remail_qs_combined ← 
--   π (pseudonym, rvalue, is_encrypted, public_key, subject, body)
--     ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--       ⋈_{messages.sender=employeelist.email_id} employeelist) 
--       ⋈_{employeelist.eid=remailmessage.eid} remail_msg)
-- 
enronQ5, enronQ5_alt :: Algebra
enronQ5 = 
  choice (F.And encryption remailmessage)
         (project ([trueAttr pseudonym_
                  , trueAttr rvalue_
                  , trueAttr is_encrypted_
                  , trueAttr public_key_
                  , trueAttr subject_
                  , trueAttr body_])
                  (join (join (join (select midXcond (tRef messages))
                                    (tRef recipientinfo)
                                    (joinEqCond (att2attrQualRel mid_ messages)
                                                (att2attrQualRel mid_ recipientinfo)))
                              (tRef employeelist)
                              (joinEqCond (att2attrQualRel sender_ messages)
                                          (att2attrQualRel email_id_ employeelist)))
                        (tRef remail_msg)
                        (joinEqCond (att2attrQualRel eid_ employeelist)
                                    (att2attrQualRel eid_ remail_msg))))
         (choice encryption 
                 q_encryption 
                 (choice remailmessage 
                         q_remailmessage 
                         q_basic))

-- encryption ∧ remailmessage⟪ subq_enc_remail_qs_combined,
--    encryption⟪ q_encryption_alt, remailmessage⟪ q_remailmessage_alt, q_basic_alt⟫⟫⟫
-- subq_enc_remail_qs_combined ← 
--   π (messages.mid, pseudonym, rvalue, is_encrypted, public_key, subject, body)
--     (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--       ⋈_{messages.sender=employeelist.email_id} employeelist) 
--       ⋈_{employeelist.eid=remailmessage.eid} remail_msg)
-- 
enronQ5_alt = 
  choice (F.And encryption remailmessage)
         (project ([trueAttrQualRel mid_ messages
                  , trueAttr pseudonym_
                  , trueAttr rvalue_
                  , trueAttr is_encrypted_
                  , trueAttr public_key_
                  , trueAttr subject_
                  , trueAttr body_])
                 (join (join (join (select midXcond (tRef messages))
                                   (tRef recipientinfo)
                                   (joinEqCond (att2attrQualRel mid_ messages)
                                               (att2attrQualRel mid_ recipientinfo)))
                             (tRef employeelist)
                             (joinEqCond (att2attrQualRel sender_ messages)
                                         (att2attrQualRel email_id_ employeelist)))
                       (tRef remail_msg)
                       (joinEqCond (att2attrQualRel eid_ employeelist)
                                   (att2attrQualRel eid_ remail_msg))))
         (choice encryption 
                 q_encryption_alt
                 (choice remailmessage 
                         q_remailmessage_alt
                         q_basic_alt))

-- 6. Purpose: Generate the header for an email when both AUTORESPONDER and FORWARDMESSAGES
--             have been enabled. This interaction requires us to generate two headers
--             one for the email to be forwarded and another one to be autoresponded
--             to the original first sender and not the one who forwarded the message
--             to avoid a cycle.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- autoresponder ∧ forwardmessages⟪ subq_gen_fwd, 
--   autoresponder⟪ q_autoresponder, forwardmessages⟪ q_forwardmessages, q_basic⟫⟫⟫
-- subq_gen_fwd ← q_forwardmessages
-- 
enronQ6part1, enronQ6part1_alt :: Algebra
enronQ6part1 = 
  choice (F.And autoresponder forwardmessages)
         (subq_gen_fwd)
         (choice autoresponder
                 q_autoresponder
                 (choice forwardmessages
                         q_forwardmessages
                         q_basic))
    where 
      subq_gen_fwd = q_forwardmessages

-- autoresponder ∧ forwardmessages⟪ subq_gen_fwd, 
--   autoresponder⟪ q_autoresponder_alt, forwardmessages⟪ q_forwardmessages_alt, q_basic_alt⟫⟫⟫
-- subq_gen_fwd ← q_forwardmessages_alt
-- 
enronQ6part1_alt = 
  choice (F.And autoresponder forwardmessages)
         (subq_gen_fwd)
         (choice autoresponder
                 q_autoresponder_alt
                 (choice forwardmessages
                         q_forwardmessages_alt
                         q_basic_alt))
    where
      subq_gen_fwd = q_forwardmessages_alt

-- 
-- autoresponder ∧ forwardmessages⟪ subq_gen_auto, 
--   autoresponder⟪ q_autoresponder, forwardmessages⟪ q_forwardmessages, q_basic⟫⟫⟫
-- subq_gen_auto ← π (forwardaddr, sender, auto_msg.subject, auto_msg.body)
--   (((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=auto_msg.eid} auto_msg)
--     ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
-- 
enronQ6part2, enronQ6part2_alt :: Algebra
enronQ6part2 = 
  choice (F.And autoresponder forwardmessages)
         (subq_gen_auto)
         (choice autoresponder
                 q_autoresponder
                 (choice forwardmessages
                         q_forwardmessages
                         q_basic))
    where
      subq_gen_auto = 
        project ([trueAttr forwardaddr_
                , trueAttr sender_
                , trueAttrQualRel subject_ auto_msg
                , trueAttrQualRel body_ auto_msg])
                (join (join (join (join (select midXcond (tRef messages))
                                        (tRef recipientinfo)
                                        (joinEqCond (att2attrQualRel mid_ messages)
                                                    (att2attrQualRel mid_ recipientinfo)))
                                  (tRef employeelist)
                                  (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                              (att2attrQualRel email_id_ employeelist)))
                            (tRef auto_msg)
                            (joinEqCond (att2attrQualRel eid_ employeelist)
                                        (att2attrQualRel eid_ auto_msg)))
                      (tRef forward_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ forward_msg)))


-- autoresponder ∧ forwardmessages⟪ subq_gen_auto, 
--   autoresponder⟪ q_autoresponder_alt, 
--      forwardmessages⟪ q_forwardmessages_alt, q_basic_alt⟫⟫⟫
-- subq_gen_auto ← π (forwardaddr, sender, auto_msg.subject, auto_msg.body)
--   ((((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=auto_msg.eid} auto_msg)
--     ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
-- 
enronQ6part2_alt = 
  choice (F.And autoresponder forwardmessages)
         (subq_gen_auto)
         (choice autoresponder
                 q_autoresponder_alt
                 (choice forwardmessages
                         q_forwardmessages_alt
                         q_basic_alt))
    where
      subq_gen_auto = 
        project ([trueAttrQualRel mid_ messages
                , trueAttr forwardaddr_
                , trueAttr sender_
                , trueAttrQualRel subject_ auto_msg
                , trueAttrQualRel body_ auto_msg])
                (join (join (join (join (tRef messages)
                                        (tRef recipientinfo)
                                        (joinEqCond (att2attrQualRel mid_ messages)
                                                    (att2attrQualRel mid_ recipientinfo)))
                                  (tRef employeelist)
                                  (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                              (att2attrQualRel email_id_ employeelist)))
                            (tRef auto_msg)
                            (joinEqCond (att2attrQualRel eid_ employeelist)
                                        (att2attrQualRel eid_ auto_msg)))
                      (tRef forward_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ forward_msg)))

-- 7. Purpose: Generate the header for an email when both AUTORESPONDER and REMAILMESSAGE
--             have been enabled. If a user sends out an email using remailmessage while
--             having their autoresponder on, the autoresponder shouldn't respond if it
--             recieves an email. So when both these features are enabled the reciever
--             who has their autoresponder on won't send out an email and gets a warning
--             message.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- autoresponder ∧ remailmessage⟪π (rvalue) 
--          ((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo),
--   autoresponder⟪ q_autoresponder, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- 
enronQ7, enronQ7_alt :: Algebra
enronQ7 =
  choice (F.And autoresponder remailmessage)
         (project (pure $ trueAttr rvalue_)
                  (join (select midXcond $ tRef messages)
                        (tRef recipientinfo)
                        (joinEqCond (att2attrQualRel mid_ messages)
                                    (att2attrQualRel mid_ recipientinfo))))
         (choice autoresponder 
                 q_autoresponder
                 (choice remailmessage
                         q_remailmessage
                         q_basic))

-- autoresponder ∧ remailmessage⟪π (mid, rvalue) 
--          (messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo),
--   autoresponder⟪ q_autoresponder_alt, remailmessage⟪ q_remailmessage_alt, q_basic_alt⟫⟫⟫
-- 
enronQ7_alt =
  choice (F.And autoresponder remailmessage)
         (project ([trueAttrQualRel mid_ messages
                  , trueAttr rvalue_])
                  (join (tRef messages)
                        (tRef recipientinfo)
                        (joinEqCond (att2attrQualRel mid_ messages)
                                    (att2attrQualRel mid_ recipientinfo))))
         (choice autoresponder 
                 q_autoresponder_alt
                 (choice remailmessage
                         q_remailmessage_alt
                         q_basic_alt))

-- 8. Purpose: Generate the header for an email when both AUTORESPONDER and FILTERMESSAGES
--             have been enabled. When a user recieves an email that has been sent
--             as an autoresponse and it belongs to the messages to be filtered, it
--             shouldn't. since the autoresponse is responding to an email that said
--             user has sent already and want to get the response. So when both these 
--             features are enabled two headers are generated, one for the case
--             that an incoming message is in fact autoresponse and should be delivered, 
--             and the other where it is not and should be filtered.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- autoresponder ∧ remailmessage⟪π (sender, rvalue, subject, body)
--        ((σ (mid=X ∧ is_autoresponse) messages) 
--         ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--    , autoresponder⟪ q_autoresponder, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- 
enronQ8part1, enronQ8part1_alt :: Algebra
enronQ8part1 = 
  choice (F.And autoresponder remailmessage)
         (project (fmap trueAttr [sender_, rvalue_, subject_, body_])
                  (join (select (VsqlAnd midXcond
                                $ eqAttValSqlCond is_autoresponse_ trueValue)
                                (tRef messages))
                        (tRef recipientinfo)
                        (joinEqCond (att2attrQualRel mid_ messages)
                                   (att2attrQualRel mid_ recipientinfo))))
         (choice autoresponder 
                 q_autoresponder
                 (choice remailmessage
                         q_remailmessage
                         q_basic))

-- autoresponder ∧ remailmessage⟪π (messages.mid, sender, rvalue, subject, body)
--        ((σ (is_autoresponse) messages) 
--         ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--    , autoresponder⟪ q_autoresponder_alt, remailmessage⟪ q_remailmessage_alt, q_basic_alt⟫⟫⟫
-- 
enronQ8part1_alt = 
  choice (F.And autoresponder remailmessage)
         (project ((pure $ trueAttrQualRel mid_ messages)
                  ++ fmap trueAttr [sender_, rvalue_, subject_, body_])
                  (join (select (eqAttValSqlCond is_autoresponse_ trueValue)
                                (tRef messages))
                        (tRef recipientinfo)
                        (joinEqCond (att2attrQualRel mid_ messages)
                                   (att2attrQualRel mid_ recipientinfo))))
         (choice autoresponder 
                 q_autoresponder_alt
                 (choice remailmessage
                         q_remailmessage_alt
                         q_basic_alt))

-- 
-- autoresponder ∧ remailmessage⟪π (sender, rvalue, subject, body, suffix)
--    subq_similar_to_filtermsg_q
--    , autoresponder⟪ q_autoresponder, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- subq_similar_to_filtermsg_q ← π (sender, rvalue, subject, body, suffix)
--   ((((σ (mid=X ∧ ¬is_autoresponse) messages) 
--   ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=filter_msg.eid} filter_msg)
-- 
enronQ8part2, enronQ8part2_alt :: Algebra
enronQ8part2 = 
  choice (F.And autoresponder remailmessage)
         (subq_similar_to_filtermsg_q)
         (choice autoresponder 
                 q_autoresponder
                 (choice remailmessage 
                         q_remailmessage
                         q_basic))  
    where
      subq_similar_to_filtermsg_q =
        project ([trueAttr sender_
                , trueAttr rvalue_
                , trueAttr subject_
                , trueAttr body_
                , trueAttr suffix_])
                (join (join (join (select (VsqlAnd midXcond
                                                   (eqAttValSqlCond is_autoresponse_ 
                                                                    falseValue)) 
                                          (tRef messages))
                                  (tRef recipientinfo)
                                  (joinEqCond (att2attrQualRel mid_ messages)
                                              (att2attrQualRel mid_ recipientinfo)))
                            (tRef employeelist)
                            (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                        (att2attrQualRel email_id_ employeelist)))
                      (tRef filter_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ filter_msg)))

-- autoresponder ∧ remailmessage⟪π (sender, rvalue, subject, body, suffix)
--    subq_similar_to_filtermsg_q
--    , autoresponder⟪ q_autoresponder, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- subq_similar_to_filtermsg_q ← π (sender, rvalue, subject, body, suffix)
--   ((((σ (mid=X ∧ ¬is_autoresponse) messages) 
--   ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=filter_msg.eid} filter_msg)
-- 
enronQ8part2_alt = 
  choice (F.And autoresponder remailmessage)
         (subq_similar_to_filtermsg_q)
         (choice autoresponder 
                 q_autoresponder_alt
                 (choice remailmessage 
                         q_remailmessage_alt
                         q_basic_alt))  
    where
      subq_similar_to_filtermsg_q =
        project ([trueAttrQualRel mid_ messages
                , trueAttr sender_
                , trueAttr rvalue_
                , trueAttr subject_
                , trueAttr body_
                , trueAttr suffix_])
                (join (join (join (select (eqAttValSqlCond is_autoresponse_ 
                                                           falseValue)
                                          (tRef messages))
                                  (tRef recipientinfo)
                                  (joinEqCond (att2attrQualRel mid_ messages)
                                              (att2attrQualRel mid_ recipientinfo)))
                            (tRef employeelist)
                            (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                        (att2attrQualRel email_id_ employeelist)))
                      (tRef filter_msg)
                      (joinEqCond (att2attrQualRel eid_ employeelist)
                                  (att2attrQualRel eid_ filter_msg)))

-- -- 9. Intent: Fix interaction AUTORESPONDER vs. MAILHOST.   -->THIS IS MANAGED IN Q_AUTORESP
-- enronQ9 :: Algebra
-- enronQ9 = Proj [trueAttr is_system_notification] $ genRenameAlgebra $ 
--                     Sel (VsqlCond midCondition) $ genRenameAlgebra $ 
--                       tRef messages
-- enronVQ9 :: Algebra
-- enronVQ9 = AChc (autoresponder `F.And` mailhost) enronQ9 Empty

-- 10. Purpose: When FORWARDMESSAGES is enabled and it creates a loop warn the users.
-- 
-- #variants = 
-- #unique_variants =
-- 
-- forwardmessages⟪ 
--    π (emp2.email_id, emp1.email_id)
--      ((((ρ (fwd1) forward_msg) 
--        ⋈_{fwd1.forwardaddr=emp1.email_id} (ρ (emp1) employeelist))
--        ⋈_{emp1.eid=fwd2.eid} (ρ (fwd2) forward_msg))
--        ⋈_{fwd2.forwardaddr=emp2.email_id} (ρ (emp2) employeelist))
--    , ε⟫
-- 
enronQ10, enronQ10_alt :: Algebra
enronQ10 = 
  choice forwardmessages
         (project [trueAttrQual email_id_ emp2Name
                  , trueAttrQual email_id_ emp1Name]
                  (join (join (join (renameQ fwd1 $ tRef forward_msg)
                                    (renameQ emp1Name $ tRef employeelist)
                                    (joinEqCond (att2attrQual forwardaddr_ fwd1)
                                                (att2attrQual email_id_ emp1Name)))
                              (renameQ fwd2 $ tRef forward_msg)
                              (joinEqCond (att2attrQual eid_ emp1Name)
                                          (att2attrQual eid_ fwd2)))
                        (renameQ emp2Name $ tRef employeelist)
                        (joinEqCond (att2attrQual forwardaddr_ fwd2)
                                    (att2attrQual email_id_ emp2Name))))
         Empty
    where
      emp1Name = "emp1"
      emp2Name = "emp2"
      fwd1 = "fwd1"
      fwd2 = "fwd2"

-- 
enronQ10_alt = enronQ10

-- 11. Purpose: Generate the header for an email when both FORWARDMESSAGES and REMAILMESSAGE
--              have been enabled. It generates the header for an email to be 
--              forwarded while checking if the foward address is the user's pseudonym
--              so that the remailer can detect if a loop may happen and avoid it.
-- 
-- #variants = 
-- #unique_variants =
--
-- forwardmessages ∧ remailmessage⟪ subq_fwd_remail_comb,
--    forwardmessages⟪ q_forwardmessages, remailmessage⟪ q_remailmessage, q_basic⟫⟫⟫
-- subq_fwd_remail_comb ← π (rvalue, forwardaddr, pseudonym, subject, body)
--   (((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
--      ⋈_{forward_msg.eid=remail_msg.eid} remail_msg)
-- 
enronQ11, enronQ11_alt :: Algebra
enronQ11 = 
  choice (F.And forwardmessages remailmessage)
         (subq_fwd_remail_comb)
         (choice forwardmessages
                 q_forwardmessages
                 (choice remailmessage
                         q_remailmessage
                         q_basic))
    where
      subq_fwd_remail_comb =
        project ([trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr pseudonym_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (join (select midXcond (tRef messages))
                                        (tRef recipientinfo)
                                        (joinEqCond (att2attrQualRel mid_ messages)
                                                    (att2attrQualRel mid_ recipientinfo)))
                                  (tRef employeelist)
                                  (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                              (att2attrQualRel email_id_ employeelist)))
                            (tRef forward_msg)
                            (joinEqCond (att2attrQualRel eid_ employeelist)
                                        (att2attrQualRel eid_ forward_msg)))
                      (tRef remail_msg)
                      (joinEqCond (att2attrQualRel eid_ forward_msg)
                                  (att2attrQualRel eid_ remail_msg)))

-- forwardmessages ∧ remailmessage⟪ subq_fwd_remail_comb,
--    forwardmessages⟪ q_forwardmessages_alt, 
--       remailmessage⟪ q_remailmessage_alt, q_basic_alt⟫⟫⟫
-- subq_fwd_remail_comb ← π (messages.mid, rvalue, forwardaddr, pseudonym, subject, body)
--   ((((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
--      ⋈_{forward_msg.eid=remail_msg.eid} remail_msg)
-- 
enronQ11_alt = 
  choice (F.And forwardmessages remailmessage)
         (subq_fwd_remail_comb)
         (choice forwardmessages
                 q_forwardmessages_alt
                 (choice remailmessage
                         q_remailmessage_alt
                         q_basic_alt))
    where
      subq_fwd_remail_comb =
        project ([trueAttrQualRel mid_ messages
                , trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr pseudonym_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (join (tRef messages)
                                        (tRef recipientinfo)
                                        (joinEqCond (att2attrQualRel mid_ messages)
                                                    (att2attrQualRel mid_ recipientinfo)))
                                  (tRef employeelist)
                                  (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                              (att2attrQualRel email_id_ employeelist)))
                            (tRef forward_msg)
                            (joinEqCond (att2attrQualRel eid_ employeelist)
                                        (att2attrQualRel eid_ forward_msg)))
                      (tRef remail_msg)
                      (joinEqCond (att2attrQualRel eid_ forward_msg)
                                  (att2attrQualRel eid_ remail_msg)))

-- 12. Purpose: Generate the header for an email when both FORWARDMESSAGES and FILTERMESSAGES
--              have been enabled. Generates the email to be forwarded (after recieving 
--              email X) and checks if the forwardaddr is in the filtered list.
-- 
-- #variants = 
-- #unique_variants =
--
-- forwardmessages ∧ filtermessages⟪ subq_fwd_filter_comb,
-- forwardmessages⟪ q_forwardmessages, filtermessages⟪ q_filtermessages, q_basic⟫⟫⟫
-- subq_fwd_filter_comb ← π (rvalue, forwardaddr, suffix, subject, body)
--   ((((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=emp1.email_id} (ρ (emp1) employeelist))
--      ⋈_{emp1.eid=forward_msg.eid} forward_msg)
--      ⋈_{forward_msg.forwardaddr=emp2.email_id} (ρ (emp2) employeelist))
--      ⋈_{emp2.eid=filter_msg.eid} filter_msg)
-- 
enronQ12, enronQ12_alt :: Algebra
enronQ12 = 
  choice (F.And forwardmessages filtermessages)
         (subq_fwd_filter_comb)
         (choice forwardmessages 
                 q_forwardmessages
                 (choice filtermessages
                         q_filtermessages
                         q_basic))
    where
      emp1Name = "emp1"
      emp2Name = "emp2"
      subq_fwd_filter_comb = 
        project ([trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr suffix_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (join (join (select midXcond (tRef messages))
                                              (tRef recipientinfo)
                                              (joinEqCond (att2attrQualRel mid_ 
                                                                           messages)
                                                          (att2attrQualRel mid_ 
                                                                           recipientinfo)))
                                        (renameQ emp1Name $ tRef employeelist)
                                        (joinEqCond (att2attrQualRel rvalue_ 
                                                                     recipientinfo)
                                                    (att2attrQual email_id_ 
                                                                  emp1Name)))
                                  (tRef forward_msg)
                                  (joinEqCond (att2attrQual eid_ emp1Name)
                                              (att2attrQualRel eid_ forward_msg)))
                            (renameQ emp2Name $ tRef employeelist)
                            (joinEqCond (att2attrQualRel forwardaddr_ forward_msg)
                                        (att2attrQual email_id_ emp2Name)))
                      (tRef filter_msg)
                      (joinEqCond (att2attrQual eid_ emp2Name)
                                  (att2attrQualRel eid_ filter_msg)))

-- forwardmessages ∧ filtermessages⟪ subq_fwd_filter_comb,
--    forwardmessages⟪ q_forwardmessages_alt, 
--       filtermessages⟪ q_filtermessages_alt, q_basic_alt⟫⟫⟫
-- subq_fwd_filter_comb ← π (messages.mid, rvalue, forwardaddr, suffix, subject, body)
--   (((((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=emp1.email_id} (ρ (emp1) employeelist))
--      ⋈_{emp1.eid=forward_msg.eid} forward_msg)
--      ⋈_{forward_msg.forwardaddr=emp2.email_id} (ρ (emp2) employeelist))
--      ⋈_{emp2.eid=filter_msg.eid} filter_msg)
-- 
enronQ12_alt = 
  choice (F.And forwardmessages filtermessages)
         (subq_fwd_filter_comb)
         (choice forwardmessages 
                 q_forwardmessages_alt
                 (choice filtermessages
                         q_filtermessages_alt
                         q_basic_alt))
    where
      emp1Name = "emp1"
      emp2Name = "emp2"
      subq_fwd_filter_comb = 
        project ([trueAttrQualRel mid_ messages
                , trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr suffix_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (join (join (tRef messages)
                                              (tRef recipientinfo)
                                              (joinEqCond (att2attrQualRel mid_ 
                                                                           messages)
                                                          (att2attrQualRel mid_ 
                                                                           recipientinfo)))
                                        (renameQ emp1Name $ tRef employeelist)
                                        (joinEqCond (att2attrQualRel rvalue_ 
                                                                     recipientinfo)
                                                    (att2attrQual email_id_ 
                                                                  emp1Name)))
                                  (tRef forward_msg)
                                  (joinEqCond (att2attrQual eid_ emp1Name)
                                              (att2attrQualRel eid_ forward_msg)))
                            (renameQ emp2Name $ tRef employeelist)
                            (joinEqCond (att2attrQualRel forwardaddr_ forward_msg)
                                        (att2attrQual email_id_ emp2Name)))
                      (tRef filter_msg)
                      (joinEqCond (att2attrQual eid_ emp2Name)
                                  (att2attrQualRel eid_ filter_msg)))

-- 13. Purpose: Generate the header for an email when both FORWARDMESSAGES and MAILHOST
--              have been enabled. It generates the header for an email to be 
--              forwarded while checking if the foward address isn't included in the
--              mailhost and causes a system notification email to be sent to the user.
--              so the mailhost can detect if a loop may happen and avoid it.
-- 
-- #variants = 
-- #unique_variants =
--
-- forwardmessages ∧ mailhost⟪ subq_fwd_mailhost_comb,
--    forwardmessages⟪ q_forwardmessages, mailhost⟪ q_mailhost, q_basic⟫⟫⟫
-- subq_fwd_remail_comb ← π (rvalue, forwardaddr, username, mailhost, subject, body)
--   (((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
--      ⋈_{forward_msg.eid=mailhost.eid} mailhost)
-- 
enronQ13, enronQ13_alt :: Algebra
enronQ13 = 
  choice (F.And forwardmessages remailmessage)
         (subq_fwd_remail_comb)
         (choice forwardmessages
                 q_forwardmessages
                 (choice remailmessage
                         q_remailmessage
                         q_basic))
    where
      subq_fwd_remail_comb =
        project ([trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr username_
                , trueAttr mailhost_attr_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (join (select midXcond (tRef messages))
                                        (tRef recipientinfo)
                                        (joinEqCond (att2attrQualRel mid_ messages)
                                                    (att2attrQualRel mid_ recipientinfo)))
                                  (tRef employeelist)
                                  (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                              (att2attrQualRel email_id_ employeelist)))
                            (tRef forward_msg)
                            (joinEqCond (att2attrQualRel eid_ employeelist)
                                        (att2attrQualRel eid_ forward_msg)))
                      (tRef mail_host)
                      (joinEqCond (att2attrQualRel eid_ forward_msg)
                                  (att2attrQualRel eid_ mail_host)))

-- forwardmessages ∧ mailhost⟪ subq_fwd_mailhost_comb,
--    forwardmessages⟪ q_forwardmessages_alt, 
--       mailhost⟪ q_mailhost_alt, q_basic_alt⟫⟫⟫
-- subq_fwd_remail_comb ← 
--  π (messages.mid, rvalue, forwardaddr, username, mailhost, subject, body)
--   ((((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--      ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--      ⋈_{employeelist.eid=forward_msg.eid} forward_msg)
--      ⋈_{forward_msg.eid=mailhost.eid} mailhost)
-- 
enronQ13_alt = 
  choice (F.And forwardmessages remailmessage)
         (subq_fwd_remail_comb)
         (choice forwardmessages
                 q_forwardmessages_alt
                 (choice remailmessage
                         q_remailmessage_alt
                         q_basic_alt))
    where
      subq_fwd_remail_comb =
        project ([trueAttrQualRel mid_ messages
                , trueAttr rvalue_
                , trueAttr forwardaddr_
                , trueAttr username_
                , trueAttr mailhost_attr_
                , trueAttr subject_
                , trueAttr body_])
                (join (join (join (join (select midXcond (tRef messages))
                                        (tRef recipientinfo)
                                        (joinEqCond (att2attrQualRel mid_ messages)
                                                    (att2attrQualRel mid_ recipientinfo)))
                                  (tRef employeelist)
                                  (joinEqCond (att2attrQualRel rvalue_ recipientinfo)
                                              (att2attrQualRel email_id_ employeelist)))
                            (tRef forward_msg)
                            (joinEqCond (att2attrQualRel eid_ employeelist)
                                        (att2attrQualRel eid_ forward_msg)))
                      (tRef mail_host)
                      (joinEqCond (att2attrQualRel eid_ forward_msg)
                                  (att2attrQualRel eid_ mail_host)))

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

