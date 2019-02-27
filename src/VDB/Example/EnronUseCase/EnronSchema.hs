 -- | An example schema 
module VDB.Example.EnronUseCase.EnronSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type
import VDB.Variational
import VDB.Config

import qualified Data.Map as M 
import VDB.Example.SmartConstructor


-- 
--  Features
-- 

signature,addressbook, filtermsg, encrypt, autoresponder, forwardmsg, mailhost, remailmsg :: Feature
signature     = Feature "signature"
addressbook   = Feature "addressbook"
filtermsg     = Feature "filtermsg"
encrypt       = Feature "encrypt"
autoresponder = Feature "autoresponder"
forwardmsg    = Feature "forwardmsg"
mailhost      = Feature "mailhost"
remailmsg     = Feature "remailmsg"

-- 
-- Feature expressions
-- 

-- | FeatureExpr for  (signature, addressbook, filtermsg)
sign_addr_filter :: FeatureExpr
sign_addr_filter = (Ref signature) `And` (Ref addressbook) `And` (Ref filtermsg)


-- | FeatureExpr for (autoresponder, forwardmsg, mailhost)
auto_forward_mhost :: FeatureExpr
auto_forward_mhost = (Ref autoresponder) `And` (Ref forwardmsg) `And` (Ref mailhost)

-- | FeatureExpr for (encrypt, remail)
encrpt_remail :: FeatureExpr
encrpt_remail = (Ref remailmsg) `And` (Ref encrypt)

-- 
-- Relations
-- 
v_employee, v_message, v_recipientInfo, v_referenceInfo, v_auto_msg, v_forward_msg,
  v_remail_msg, v_filter_msg, v_mailhost, v_alias :: String
v_employee      = "v_employee"
v_message       = "v_message"
v_recipientInfo = "v_recipientInfo"
v_referenceInfo = "v_referenceInfo"
v_auto_msg      = "v_auto_msg"
v_forward_msg   = "v_forward_msg"
v_remail_msg    = "v_remail_msg"
v_filter_msg    = "v_filter_msg"
v_mailhost      = "v_mailhost"
v_alias         = "v_alias"


-- 
-- Attributes
-- 

-- | v_employee
employeeEid, firstname, lastname, email_id, employeeFolder, status, sign, public_key,employeeDid :: Attribute
employeeEid = Attribute "employeeEid"
firstname = Attribute "firstname"
lastname = Attribute "lastname"
email_id= Attribute "email_id"
employeeFolder= Attribute "employeeFolder"
status= Attribute "status"
sign= Attribute "sign"
public_key= Attribute "public_key"
employeeDid = Attribute "employeeDid"

-- | v_message 
messageMid, sender, date, message_id, subject, messageBody, messageFolder, is_signed, is_encrypted :: Attribute
messageMid = Attribute "messageMid"
sender = Attribute "sender"
date = Attribute "date"
message_id = Attribute "message_id"
subject = Attribute "subject"
messageBody = Attribute "messageBody"
messageFolder = Attribute "messageFolder"
is_signed = Attribute "is_signed"
is_encrypted = Attribute "is_encrypted"

 -- | v_recipientinfo
rid, recipientInfoMid, rtype, rvalue_email, rvalue_nickname :: Attribute
rid = Attribute "rid"
recipientInfoMid = Attribute "recipientInfoMid"
rtype = Attribute "rtype"
rvalue_email = Attribute "rvalue_email"
rvalue_nickname = Attribute "rvalue_nickname"

-- | v_referenceInfo
rfid, referenceInfoMid, reference :: Attribute 
rfid = Attribute "rfid"
referenceInfoMid = Attribute "referenceInfoMid"
reference = Attribute "reference"

-- | v_auto_msg 
auto_msgEid, auto_msgSubject, auto_msgBody :: Attribute 
auto_msgEid = Attribute "auto_msgEid"
auto_msgSubject = Attribute "auto_msgSubject"
auto_msgBody = Attribute "auto_msgBody"

-- | v_forward_msg 
v_forward_msgEid, forwardaddr :: Attribute
v_forward_msgEid = Attribute "v_forward_msgEid"
forwardaddr = Attribute "forwardaddr"

-- | v_remail_msg 
remail_msgEid, psuedonym :: Attribute
remail_msgEid = Attribute "remail_msgEid"
psuedonym = Attribute "psuedonym"


-- | v_filter_msg 
filter_msgEid, suffix :: Attribute
filter_msgEid = Attribute "filter_msgEid"
suffix = Attribute "suffix"

-- | v_ailhost 
mailhostDid, username :: Attribute
mailhostDid = Attribute "mailhostDid"
username = Attribute "username"

-- | v_alias
aliasEid, email, nickname :: Attribute 
aliasEid = Attribute "aliasEid"
email = Attribute "email"
nickname = Attribute "nickname"






--
-- ** schema 1
--    * enable feature: (signature, addressbook, filtermsg), 

--    * disable feature: (autoresponder, forwardmsg, mailhost),
--                    	 (encrypt, remailmsg)

-- | A configuration of enron email that disables all features.
enronConfigAllDisabled :: Config Bool
enronConfigAllDisabled = disableAll

-- | enron email first configuration.
-- enronConfig :: Config Bool
-- enronConfig = enableMany 
--   [signature, addressbook, filtermsg] enronConfigAllDisabled


enronSchema :: Schema 
enronSchema = ( Lit True, M.fromList [ ( Relation v_employee,  (Lit True, employee_rowtype))
                                              , ( Relation v_message,   ( Lit True , message_rowtype))
                                              , ( Relation v_recipientInfo, ( Lit True , recipientInfo_rowtype))
                                              , ( Relation v_referenceInfo, ( Lit True , referenceInfo_rowtype))
                                              , ( Relation v_auto_msg, ( Ref autoresponder , auto_msg_rowtype))
                                              , ( Relation v_forward_msg, ( Ref forwardmsg , forward_msg_rowtype))
                                              , ( Relation v_remail_msg, ( Ref remailmsg , remail_msg_rowtype))
                                              , ( Relation v_filter_msg, ( Ref filtermsg , filter_msg_rowtype))
                                              , ( Relation v_mailhost, ( Ref mailhost , mailhost_rowtype))
                                              , ( Relation  v_alias, ( Ref addressbook , alias_rowtype))
                                                   ]
               )

-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key, did, presCond)
employee_rowtype :: RowType 
employee_rowtype =M.fromList [ ("eid", (Lit True, TInt32))
                     , ("firstname",  (Lit True,TString))
                     , ("lastname", (Lit True, TString))
                     , ("email_id", (Lit True,TString))
                     , ("folder", (Lit True,TString))
                     , ("status", (Lit True, TString))
                     , ("sign", (Ref signature, TString))
                     , ("puclic_key", (Ref encrypt, TString))
                     , ("did", (Ref mailhost,TInt32))
                     ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_rowtype :: RowType
message_rowtype =  M.fromList  [ ("mid", (Lit True, TInt32)) 
                     , ("sender",  (Lit True,TString))
                     , ("date",  (Lit True,TString))
                     , ("message_id", (Lit True, TInt32))
                     , ("subject", (Lit True,TString))
                     , ("body", (Lit True,TString))
                     , ("folder", (Lit True,TString))
                     , ("is_signed", (Ref signature, TBool))
                     , ("is_encrypted", (Ref encrypt, TBool))
                     ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_rowtype :: RowType
recipientInfo_rowtype = M.fromList     [ ("rid", (Lit True, TInt32))
							           , ("mid",  (Lit True, TInt32))
							           , ("rtype",  (Lit True , TString))
							           , ("rvalue_email", (Lit True , TString))
							           , ("rvalue_nickname", (Lit True , TString))
							           ]

-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_rowtype :: RowType
referenceInfo_rowtype = M.fromList [ ("rfid", (Lit True, TInt32))
						           , ("mid",  (Lit True, TInt32))
						           , ("reference",  (Lit True , TString))
						           ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_rowtype :: RowType
auto_msg_rowtype =  M.fromList [ ("eid", (Lit True, TInt32)) 
					           ,  ("subject",  (Lit True , TString))
					           , ("body",  (Lit True , TString))
					           ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_rowtype :: RowType
forward_msg_rowtype =  M.fromList [ ("eid", (Lit True, TInt32))
				              , ("forwardaddr",  (Lit True , TString))
				              ]

-- remail_msg(eid, psuedonym, presCond)
remail_msg_rowtype:: RowType
remail_msg_rowtype =   M.fromList [ ("eid", (Lit True, TInt32)) 
					              , ("psuedonym",  (Lit True , TString))
					              ]

-- filter_msg(eid, suffix, presCond)
filter_msg_rowtype :: RowType
filter_msg_rowtype = M.fromList [ ("eid", (Lit True, TInt32)) 
					            , ("suffix",  (Lit True , TString))
					            ]

-- -- mailhost(did, domain, presCond)
mailhost_rowtype :: RowType
mailhost_rowtype = M.fromList [ ("did", (Lit True, TInt32))
					          , ("username",  (Lit True , TString))
					          ]

-- alias(eid, email, nickname, presCond)
alias_rowtype :: RowType
alias_rowtype = M.fromList [ ("eid", (Lit True, TInt32))
				       , ("email",  (Lit True , TString))
				       , ("nickname",  (Lit True , TString))
				       ]

