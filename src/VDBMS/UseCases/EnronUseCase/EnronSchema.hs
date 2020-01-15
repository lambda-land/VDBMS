 -- | An example schema 
module VDBMS.UseCases.EnronUseCase.EnronSchema where

import VDBMS.Features.FeatureExpr.FeatureExpr
import qualified VDBMS.VDB.Name as N 
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Value.Value
import VDBMS.UseCases.SmartConstructor

-- 
--  * Features
-- 
addressbook, signature, encryption, filtermessages, autoresponder, forwardmessages, mailhost, remailmessage :: FeatureExpr
addressbook    = Ref (Feature "addressbook")
signature      = Ref (Feature "signature")
encryption     = Ref (Feature "encryption")
filtermessages = Ref (Feature "filtermessages")
autoresponder  = Ref (Feature "autoresponder")
forwardmessages = Ref (Feature "forwardmessages")
remailmessage = Ref (Feature "remailmessage")
mailhost      = Ref (Feature "mailhost")

-- | FeatureExpr for  (signature, addressbook, filtermessages)
sign_addr_filter :: FeatureExpr
sign_addr_filter = signature `And` addressbook `And` filtermessages

-- | FeatureExpr for (autoresponder, forwardmessages, mailhost)
auto_forward_mhost :: FeatureExpr
auto_forward_mhost = autoresponder `And` forwardmessages `And` mailhost

--
-- * Relations 
-- 
employeelist, messages, recipientinfo, auto_msg, referenceinfo, forward_msg :: N.Relation
remail_msg, filter_msg, mail_host, alias :: N.Relation
employeelist  = N.Relation "employeelist"
messages      = N.Relation "messages"
recipientinfo = N.Relation "recipientinfo"
auto_msg      = N.Relation "auto_msg"
referenceinfo = N.Relation "referenceinfo"
forward_msg   = N.Relation "forward_msg"
remail_msg    = N.Relation "remail_msg"
filter_msg    = N.Relation "filter_msg"
mail_host     = N.Relation "remail_msg"
alias         = N.Relation "alias"

--
-- * Attributes 
--
email_id :: N.Attr 
email_id = attr "email_id"

mid, sender, subject, is_signed, is_encrypted, is_from_remailer :: N.Attr 
is_autoresponse, is_forward_msg, is_system_notification:: N.Attr 
mid = attr "mid"
sender = attr "sender"
subject = attr "subject"
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
-- * Enron VDB Feature Model
--
enronFeatureModel :: FeatureExpr
enronFeatureModel = Lit True 

--
-- * Enron V-Schema for Software Product Lines
--
enronVSchema :: Schema 
enronVSchema = (enronFeatureModel, constructOptRelMap [ (Lit True, employeelist, employeelist_vrelation)
                                                      , (Lit True, messages, messages_vrelation)
                                                      , (Lit True, recipientinfo, recipientinfo_vrelation)
                                                      , (Lit True, referenceinfo, referenceinfo_vrelation)
                                                      , (forwardmessages, forward_msg, forward_msg_vrelation)
                                                      , (filtermessages, filter_msg, filter_msg_vrelation)
                                                      , (remailmessage, remail_msg, remail_msg_vrelation)
                                                      , (autoresponder, auto_msg, auto_msg_vrelation)
                                                      , (addressbook, alias, alias_vrelation)
                                                      , (mailhost, mail_host, mail_host_vrelation)
                                                      ])

employeelist_vrelation, messages_vrelation, recipientinfo_vrelation, referenceinfo_vrelation, auto_msg_vrelation :: [(FeatureExpr, N.Attribute, SqlType)] 
forward_msg_vrelation, remail_msg_vrelation, filter_msg_vrelation, mail_host_vrelation, alias_vrelation :: [(FeatureExpr, N.Attribute, SqlType)] 
employeelist_vrelation = [ (Lit True, N.Attribute "eid", TInt32)
                         , (Lit True, N.Attribute "firstname",  TString)
                         , (Lit True, N.Attribute "lastname",  TString)
                         , (Lit True, N.Attribute "email_id", TString)
                         , (Lit True, N.Attribute "folder", TString)
                         , (Lit True, N.Attribute "status", TString)
                         , (signature, N.Attribute "verification_key", TString)
                         , (encryption,   N.Attribute "puclic_key", TString)
                         ]
               
messages_vrelation = [ (Lit True, N.Attribute "mid", TInt32) 
                     , (Lit True, N.Attribute "sender",  TString)
                     , (Lit True, N.Attribute "date",  TString)
                     , (Lit True, N.Attribute "message_id", TInt32)
                     , (Lit True, N.Attribute "subject", TString)
                     , (Lit True, N.Attribute "body", TString)
                     , (Lit True, N.Attribute "folder", TString)
                     , (Lit True, N.Attribute "is_system_notification", TBool)
                     , (signature, N.Attribute "is_signed", TBool)
                     , (encryption, N.Attribute"is_encrypted", TBool)
                     , (autoresponder, N.Attribute"is_autoresponse", TBool)
                     , (forwardmessages, N.Attribute"is_forward_msg", TBool)
                     ] 

recipientinfo_vrelation = constructAllTrueRelSchema  [ ("rid", TInt32)
                                                     , ("mid",  TInt32)
                                                     , ("rtype",  TString)
                                                     , ("rvalue", TString)
                                                     ]

referenceinfo_vrelation = constructAllTrueRelSchema  [ ("rfid", TInt32)
                                                     , ("mid",  TInt32)
                                                     , ("reference",  TString)
                                                     ]
                                                     
forward_msg_vrelation = constructAllTrueRelSchema [ ("eid", TInt32)
                                                  , ("forwardaddr",  TString)
                                                  ]

auto_msg_vrelation = constructAllTrueRelSchema [ ("eid", TInt32) 
                                               , ("subject",  TString)
                                               , ("body",  TString)
                                               ]

remail_msg_vrelation = constructAllTrueRelSchema [ ("eid", TInt32) 
                                                 , ("pseudonym",  TString)
                                                 ]

filter_msg_vrelation = constructAllTrueRelSchema  [ ("eid", TInt32) 
                                                  , ("suffix",  TString)
                                                  ]
mail_host_vrelation = constructAllTrueRelSchema  [ ("eid", TInt32)
                                                , ("username",  TString)
                                                , ("mailhost",  TString)
                                                ]

alias_vrelation = constructAllTrueRelSchema  [ ("eid", TInt32)
                                             , ("email",  TString)
                                             , ("nickname",  TString)
                                             ]
