 -- | An example schema 
module VDBMS.UseCases.EnronUseCase.EnronSchema where

import VDBMS.Features.FeatureExpr.FeatureExpr
import qualified VDBMS.VDB.Name as N 
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Value.Value
import VDBMS.UseCases.SmartConstructor

--
-- 
--  * Features
-- 
addressbook, signature, encrypt, filtermsg, autoresponder, forwardmsg, mailhost, remailmsg :: FeatureExpr
addressbook   = Ref (Feature "addressbook")
signature     = Ref (Feature "signature")
encrypt       = Ref (Feature "encrypt")
filtermsg     = Ref (Feature "filtermsg")
autoresponder = Ref (Feature "autoresponder")
forwardmsg    = (Ref (Feature "forwardmsg"))
remailmsg     = Ref (Feature "remailmsg")
mailhost      = Ref (Feature "mailhost")

-- | FeatureExpr for  (signature, addressbook, filtermsg)
sign_addr_filter :: FeatureExpr
sign_addr_filter = signature `And` addressbook `And` filtermsg

-- | FeatureExpr for (autoresponder, forwardmsg, mailhost)
auto_forward_mhost :: FeatureExpr
auto_forward_mhost = autoresponder `And` forwardmsg `And` mailhost

--
-- * Relations 
-- 
v_employee, v_message, v_recipientinfo, v_auto_msg, v_referenceinfo, v_forward_msg :: N.Relation
v_remail_msg, v_filter_msg, v_mailhost, v_alias :: N.Relation
v_employee      = N.Relation "v_employee"
v_message       = N.Relation "v_message"
v_recipientinfo = N.Relation "v_recipientinfo"
v_auto_msg      = N.Relation "v_auto_msg"
v_referenceinfo = N.Relation "v_referenceinfo"
v_forward_msg   = N.Relation "v_forward_msg"
v_remail_msg    = N.Relation "v_remail_msg"
v_filter_msg    = N.Relation "v_filter_msg"
v_mailhost      = N.Relation "v_remail_msg"
v_alias         = N.Relation "v_alias"
--
-- * Attributes 
--
email_id :: N.Attr 
email_id = attr "email_id"

mid, sender, is_signed, is_encrypted, is_from_remailer :: N.Attr 
is_autoresponse, is_forward_msg, is_system_notification:: N.Attr 
mid = attr "mid"
sender = attr "sender"
is_signed = attr "is_signed"
is_encrypted = attr "is_encrypted"
is_from_remailer = attr "is_from_remailer"
is_autoresponse = attr "is_autoresponse"
is_forward_msg = attr "is_forward_msg"
is_system_notification = attr "is_system_notification"
forwardaddr :: N.Attr 
forwardaddr = attr "forwardaddr"

rvalue :: N.Attr 
rvalue = attr "rvalue"

reference :: N.Attr
reference = attr "reference"

pseudonym, suffix :: N.Attr 
pseudonym = attr "pseudonym"
suffix = attr "suffix"

--
-- * Enron V-schema
--

enronFeatureModel :: FeatureExpr
enronFeatureModel = Lit True 

enronVSchema :: Schema 
enronVSchema = (enronFeatureModel, constructOptRelMap [ (Lit True, v_employee, v_employee_vschema)
                                                      , (Lit True, v_message, v_message_vschema)
                                                      , (Lit True, v_recipientinfo, v_recipientinfo_vschema)
                                                      , (Lit True,      v_referenceinfo, v_referenceinfo_vschema)
                                                      , (autoresponder, v_auto_msg, v_auto_msg_vschema)
                                                      , (forwardmsg, v_forward_msg, v_forward_msg_vschema)
                                                      , (remailmsg, v_remail_msg, v_remail_msg_vschema)
                                                      , (filtermsg, v_filter_msg, v_filter_msg_vschema)
                                                      , (mailhost, v_mailhost, v_mailhost_vschema)
                                                      , (addressbook, v_alias, v_alias_vschema)
                                                      ])


v_employee_vschema, v_message_vschema, v_recipientinfo_vschema, v_referenceinfo_vschema, v_auto_msg_vschema :: [(FeatureExpr, N.Attribute, SqlType)] 
v_forward_msg_vschema, v_remail_msg_vschema, v_filter_msg_vschema, v_mailhost_vschema, v_alias_vschema :: [(FeatureExpr, N.Attribute, SqlType)] 
v_employee_vschema = [ (Lit True, N.Attribute "eid", TInt32)
                     , (Lit True, N.Attribute "firstname",  TString)
                     , (Lit True, N.Attribute "lastname",  TString)
                     , (Lit True, N.Attribute "email_id", TString)
                     , (Lit True, N.Attribute "folder", TString)
                     , (Lit True, N.Attribute "status", TString)
                     , (signature, N.Attribute "sign", TString)
                     , (encrypt,   N.Attribute "puclic_key", TString)
                     , (mailhost,  N.Attribute "mailhost", TString)
                     ]
               

v_message_vschema =[ (Lit True, N.Attribute "mid", TInt32) 
                   , (Lit True, N.Attribute "sender",  TString)
                   , (Lit True, N.Attribute "date",  TString)
                   , (Lit True, N.Attribute "message_id", TInt32)
                   , (Lit True, N.Attribute "subject", TString)
                   , (Lit True, N.Attribute "body", TString)
                   , (Lit True, N.Attribute "folder", TString)
                   , (Lit True, N.Attribute "is_system_notification", TBool)
                   , (signature, N.Attribute "is_signed", TBool)
                   , (encrypt, N.Attribute"is_encrypted", TBool)
                   , (remailmsg, N.Attribute"is_from_remailer", TBool)
                   , (autoresponder, N.Attribute"is_autoresponse", TBool)
                   , (forwardmsg, N.Attribute"is_forward_msg", TBool)
                   ] 

v_recipientinfo_vschema = constructAllTrueRelSchema  [ ("rid", TInt32)
                                                     , ("mid",  TInt32)
                                                     , ("rtype",  TString)
                                                     , ("rvalue", TString)
                                                     ]

v_referenceinfo_vschema = constructAllTrueRelSchema  [ ("rfid", TInt32)
                                                     , ("mid",  TInt32)
                                                     , ("reference",  TString)
                                                     ]

 
v_auto_msg_vschema = constructAllTrueRelSchema [ ("eid", TInt32) 
                                               , ("subject",  TString)
                                               , ("body",  TString)
                                               ]
v_forward_msg_vschema = constructAllTrueRelSchema [ ("eid", TInt32)
                                                  , ("forwardaddr",  TString)
                                                  ]
v_remail_msg_vschema = constructAllTrueRelSchema [ ("eid", TInt32) 
                                                 , ("pseudonym",  TString)
                                                 ]

v_filter_msg_vschema = constructAllTrueRelSchema  [ ("eid", TInt32) 
                                                  , ("suffix",  TString)
                                                  ]
v_mailhost_vschema = constructAllTrueRelSchema  [ ("eid", TInt32)
                                                , ("username",  TString)
                                                , ("mailhost",  TString)
                                                ]

v_alias_vschema = constructAllTrueRelSchema  [ ("eid", TInt32)
                                             , ("email",  TString)
                                             , ("nickname",  TString)
                                             ]