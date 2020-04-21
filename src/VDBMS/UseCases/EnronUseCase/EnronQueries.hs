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
-- π (rvalue, sender, auto_msg.subject, auto_msg.body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=auto_msg.eid} auto_msg)
-- 
q_autoresponder, q_autoresponder_alt :: Algebra
q_autoresponder = 
  project ([trueAttr rvalue_
          , trueAttr sender_
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
-- π (messages.mid, rvalue, sender, auto_msg.subject, auto_msg.body)
--   (((messages ⋈_{messages.mid=temp.mid} recipientinfo) 
--     ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=auto_msg.eid} auto_msg)
q_autoresponder_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr rvalue_
          , trueAttr sender_
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
-- π (pseudonym, rvalue, subject, body)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{messages.sender=employeelist.email_id} employeelist) 
--     ⋈_{employeelist.eid=remailmessage.eid} remail_msg)
-- 
q_remailmessage, q_remailmessage_alt :: Algebra
q_remailmessage = 
  project ([trueAttr pseudonym_
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
-- π (messages.mid, pseudonym, rvalue, subject, body)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--     ⋈_{messages.sender=employeelist.email_id} employeelist)
--     ⋈_{employeelist.eid=remailmessage.eid} remail_msg)
q_remailmessage_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr pseudonym_
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
-- π (sender, rvalue, subject, body, suffix)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=filter_msg.eid} filter_msg)
-- 
q_filtermessages, q_filtermessages_alt :: Algebra
q_filtermessages = 
  project ([trueAttr sender_
          , trueAttr rvalue_
          , trueAttr subject_
          , trueAttr body_
          , trueAttr suffix_])
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
-- π (messages.mid, sender, rvalue, subject, body, suffix)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=filter_msg.eid} filter_msg)
q_filtermessages_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr subject_
          , trueAttr body_
          , trueAttr suffix_])
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
-- π (sender, rvalue, subject, body, mailhost)
--   ((((σ (mid=X) messages) ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=mail_host.eid} mail_host)
-- 
q_mailhost, q_mailhost_alt :: Algebra
q_mailhost = 
  project ([trueAttr sender_
          , trueAttr rvalue_
          , trueAttr subject_
          , trueAttr body_
          , trueAttr mailhost_attr_])
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
-- π (messages.mid, sender, rvalue, subject, body, mailhost)
--   (((messages ⋈_{messages.mid=recipientinfo.mid} recipientinfo)
--   ⋈_{recipientinfo.rvalue=employeelist.email_id} employeelist) 
--   ⋈_{employeelist.eid=mail_host.eid} mail_host)
q_mailhost_alt = 
  project ([trueAttrQualRel mid_ messages
          , trueAttr sender_
          , trueAttr rvalue_
          , trueAttr subject_
          , trueAttr body_
          , trueAttr mailhost_attr_])
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
--             have been enabled(1).
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
-- , signature ⟪ q_signature, forwardmessages ⟪ q_forwardmessages, q_basic ⟫⟫⟫
-- 
enronQ1_alt = undefined
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
                 q_signature
                 (choice forwardmessages
                         q_forwardmessages
                         q_basic))
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

