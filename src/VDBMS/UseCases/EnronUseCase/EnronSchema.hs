 -- | An example schema 
module VDBMS.UseCases.EnronUseCase.EnronSchema where

import VDBMS.Features.FeatureExpr.FeatureExpr
import qualified VDBMS.VDB.Name as N 
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Value.Value
import VDBMS.QueryLang.RelAlg.Variational.SmartConstructor
import VDBMS.VDB.Schema.Relational.Types
import VDBMS.Features.Config (Config)

-- 
--  * Features
-- 
addressbook, signature, encryption, filtermessages, autoresponder, forwardmessages, mailhost, remailmessage :: FeatureExpr
addressbook     = Ref (Feature "addressbook")
signature       = Ref (Feature "signature")
encryption      = Ref (Feature "encrypt")
filtermessages  = Ref (Feature "filtermsg")
autoresponder   = Ref (Feature "autoresponder")
forwardmessages = Ref (Feature "forwardmsg")
remailmessage   = Ref (Feature "remailmsg")
mailhost        = Ref (Feature "mailhost")

enronFeatures :: [Feature]
enronFeatures = [Feature "addressbook"
               , Feature "signature"
               , Feature "encrypt"
               , Feature "filtermsg"
               , Feature "autoresponder"
               , Feature "forwardmsg"
               , Feature "remailmsg"
               , Feature "mailhost"]

-- 
--  * Configuration of variants
-- 
enronConfig1 :: Config Bool
enronConfig1 (Feature "forwardmsg") = True
enronConfig1 (Feature "filtermsg")  = True
enronConfig1 _                           = False

enronConfig2 :: Config Bool
enronConfig2 (Feature "signature")     = True
enronConfig2 (Feature "encrypt")    = True
enronConfig2 (Feature "remailmsg") = True
enronConfig2 _                         = False

-- | The features map for group email:
--   signature + encryption + addressbook + autoresponder + mailhost
--   (To make the case that group email and privacy email have features overlapped)
enronConfig3 :: Config Bool
enronConfig3 (Feature "signature")     = True
enronConfig3 (Feature "encrypt")    = True
enronConfig3 (Feature "addressbook")   = True
enronConfig3 (Feature "autoresponder") = True
enronConfig3 (Feature "mailhost")      = True
enronConfig3 _                         = False

enronConfig4 :: Config Bool
enronConfig4 (Feature "forwardmsg") = True
enronConfig4 (Feature "filtermsg")  = True
enronConfig4 (Feature "signature")       = True
enronConfig4 (Feature "encrypt")      = True
enronConfig4 (Feature "remailmsg")   = True
enronConfig4 (Feature "addressbook")     = True
enronConfig4 (Feature "autoresponder")   = True
enronConfig4 (Feature "mailhost")        = True
enronConfig4 _                           = False

enronConfig5 :: Config Bool
enronConfig5 _ = False

enronConfs :: [Config Bool]
enronConfs = [enronConfig1, enronConfig2, 
              enronConfig3, enronConfig4, enronConfig5]

-- | FeatureExpr for  (signature, addressbook, filtermessages)
sign_addr_filter :: FeatureExpr
sign_addr_filter = signature `And` addressbook `And` filtermessages

-- | FeatureExpr for (autoresponder, forwardmessages, mailhost)
auto_forward_mhost :: FeatureExpr
auto_forward_mhost = autoresponder `And` forwardmessages `And` mailhost

--
-- * Relations 
-- 
employeelist, messages, recipientinfo, auto_msg, forward_msg :: N.Relation
remail_msg, filter_msg, mail_host, alias :: N.Relation
employeelist  = N.Relation "v_employee"
messages      = N.Relation "v_message"
recipientinfo = N.Relation "v_recipientinfo"
auto_msg      = N.Relation "v_auto_msg"
-- referenceinfo = N.Relation "referenceinfo"
forward_msg   = N.Relation "v_forward_msg"
remail_msg    = N.Relation "v_remail_msg"
filter_msg    = N.Relation "v_filter_msg"
mail_host     = N.Relation "v_mailhost"
alias         = N.Relation "v_alias"

--
-- * Attributes 
--

email_id :: N.Attr 
email_id = attr "email_id"

mid, eid, sender, subject, is_signed, is_encrypted, is_from_remailer :: N.Attr 
is_autoresponse, is_forward_msg, is_system_notification, nickname, username, mailhost_attr:: N.Attr 
mid = attr "mid"
eid = attr "eid"
sender = attr "sender"
subject = attr "subject"
is_signed = attr "is_signed"
is_encrypted = attr "is_encrypted"
is_from_remailer = attr "is_from_remailer"
is_autoresponse = attr "is_autoresponse"
is_forward_msg = attr "is_forward_msg"
is_system_notification = attr "is_system_notification"
nickname = attr "nickname"
username = attr "username"
mailhost_attr = attr "mailhost"

forwardaddr :: N.Attr 
forwardaddr = attr "forwardaddr"

rvalue :: N.Attr 
rvalue = attr "rvalue"

-- reference :: N.Attr
-- reference = attr "reference"

pseudonym, suffix :: N.Attr 
pseudonym = attr "pseudonym"
suffix = attr "suffix"

eid_, firstname_, lastname_, email_id_, folder_, status_, verification_key_, public_key_, username_, mailhost_attr_ :: N.Attribute 
eid_ = N.Attribute "eid"
firstname_ = N.Attribute "firstname"
lastname_ = N.Attribute "lastname"
email_id_ = N.Attribute "email_id"
folder_ = N.Attribute "folder"
status_ = N.Attribute "status"
verification_key_ = N.Attribute "verification_key"
public_key_ = N.Attribute "public_key"
username_ = N.Attribute "username"
mailhost_attr_ = N.Attribute "mailhost"

mid_, sender_, date_, message_id_, subject_, body_, is_signed_, is_encrypted_ :: N.Attribute 
is_autoresponse_, is_forward_msg_, is_system_notification_, nickname_:: N.Attribute 
mid_ = N.Attribute "mid"
sender_ = N.Attribute "sender"
date_ = N.Attribute "date"
message_id_ = N.Attribute "message_id"
subject_ = N.Attribute "subject"
body_    = N.Attribute "body"
is_signed_ = N.Attribute "is_signed"
is_encrypted_ = N.Attribute "is_encrypted"
is_autoresponse_ = N.Attribute "is_autoresponse"
is_forward_msg_ = N.Attribute "is_forward_msg"
is_system_notification_ = N.Attribute "is_system_notification"
nickname_ = N.Attribute "nickname"

rid_, rtype_, rvalue_, suffix_, forwardaddr_, pseudonym_:: N.Attribute
rid_ = N.Attribute "rid"  
-- rfid_ = N.Attribute "rfid"
rtype_ = N.Attribute "rtype"
rvalue_ = N.Attribute "rvalue"
-- reference_ = N.Attribute "reference"
suffix_ = N.Attribute "suffix"
forwardaddr_ = N.Attribute "forwardaddr"
pseudonym_ = N.Attribute "pseudonym"
--
-- * Enron VDB Feature Model
--
enronFeatureModel :: FeatureExpr
enronFeatureModel = Lit True 

--
-- * Enron V-Schema for Software Product Lines
--
enronVSchema :: Schema 
enronVSchema = ((enronFeatures, enronConfs), (enronFeatureModel, constructOptRelMap [ (Lit True, employeelist, employeelist_vrelation)
                                                      , (Lit True, messages, messages_vrelation)
                                                      , (Lit True, recipientinfo, recipientinfo_vrelation)
                                                      -- , (Lit True, referenceinfo, referenceinfo_vrelation)
                                                      , (forwardmessages, forward_msg, forward_msg_vrelation)
                                                      , (filtermessages, filter_msg, filter_msg_vrelation)
                                                      , (remailmessage, remail_msg, remail_msg_vrelation)
                                                      , (autoresponder, auto_msg, auto_msg_vrelation)
                                                      , (addressbook, alias, alias_vrelation)
                                                      , (mailhost, mail_host, mail_host_vrelation)
                                                      ]))

employeelist_vrelation, messages_vrelation, recipientinfo_vrelation, auto_msg_vrelation :: [(FeatureExpr, N.Attribute, SqlType)] 
forward_msg_vrelation, remail_msg_vrelation, filter_msg_vrelation, mail_host_vrelation, alias_vrelation :: [(FeatureExpr, N.Attribute, SqlType)] 
employeelist_vrelation = [ (Lit True, eid_, TInt32)
                         , (Lit True, firstname_,  TString)
                         , (Lit True, lastname_,  TString)
                         , (Lit True, email_id_, TString)
                         , (Lit True, folder_, TString)
                         , (Lit True, status_, TString)
                         , (signature, verification_key_, TString)
                         , (encryption,   public_key_, TString)
                         ]
               
messages_vrelation = [ (Lit True, mid_, TInt32) 
                     , (Lit True, sender_,  TString)
                     , (Lit True, date_,  TString)
                     , (Lit True, message_id_, TInt32)
                     , (Lit True, subject_, TString)
                     , (Lit True, body_, TString)
                     , (Lit True, folder_, TString)
                     , (Lit True, is_system_notification_, TBool)
                     , (signature, is_signed_, TBool)
                     , (encryption, is_encrypted_, TBool)
                     , (autoresponder, is_autoresponse_, TBool)
                     , (forwardmessages, is_forward_msg_, TBool)
                     ] 

recipientinfo_vrelation = constructAllTrueRelSchema  [ ("rid", TInt32)
                                                     , ("mid",  TInt32)
                                                     , ("rtype",  TString)
                                                     , ("rvalue", TString)
                                                     ]

-- referenceinfo_vrelation = constructAllTrueRelSchema  [ ("rfid", TInt32)
--                                                      , ("mid",  TInt32)
--                                                      , ("reference",  TString)
--                                                      ]
                                                     
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
                                             , ("email_id",  TString)
                                             , ("nickname",  TString)
                                             ]

--
-- Pure Relational Schemas For Employee Evolution 
--

--  ** Schema Variant for Basic Email
basicEmailSchema :: RSchema
basicEmailSchema  = constructRSchema   [ ( employeelist,  basic_employeelist)
                                       , ( messages,    basic_messages)
                                       , ( recipientinfo,  recipientinfo_table)
                                       -- , ( referenceinfo, referenceinfo_table)
                                       ]
-- | employeelist(eid, firstname, lastname, email_id , folder , status)
basic_employeelist :: [(N.Attribute, SqlType)]
basic_employeelist = [ ( eid_, TInt32)
                     , ( firstname_,  TString)
                     , ( lastname_,  TString)
                     , ( email_id_, TString)
                     , ( folder_, TString)
                     , ( status_, TString)
                     ]
-- | messages(mid, sender, date, message id , subject, body, folder,, is_system_notification)
basic_messages :: [(N.Attribute, SqlType)]
basic_messages = [ (mid_, TInt32) 
                 , (sender_,  TString)
                 , (date_,  TString)
                 , (message_id_, TInt32)
                 , (subject_, TString)
                 , (body_, TString)
                 , (folder_, TString)
                 , (is_system_notification_, TBool)
                 ] 

-- | recipientinfo(rid, mid, rtype, rvalue)
recipientinfo_table :: [(N.Attribute, SqlType)]
recipientinfo_table =  [ (rid_, TInt32)
                       , (mid_,  TInt32)
                       , (rtype_,  TString)
                       , (rvalue_, TString)
                       ]
-- | referenceinfo(rid, mid, reference)
-- referenceinfo_table :: [(N.Attribute, SqlType)]
-- referenceinfo_table =  [ (rfid_, TInt32)
--                        , (mid_,  TInt32)
--                        , (reference_,  TString)
--                        ]

--  ** Schema Variant for Enhanced Email (basic + forwardmessages + filtermessages)
enhancedEmailSchema :: RSchema
enhancedEmailSchema  = constructRSchema   [ ( employeelist,  enhanced_employeelist)
                                           , ( messages,    enhanced_messages)
                                           , ( recipientinfo, recipientinfo_table)
                                           -- , ( referenceinfo, referenceinfo_table)
                                           , ( forward_msg, forward_msg_table)
                                           , ( filter_msg, filter_msg_table)
                                           ]

enhanced_employeelist :: [(N.Attribute, SqlType)]
enhanced_employeelist = basic_employeelist

enhanced_messages :: [(N.Attribute, SqlType)]
enhanced_messages = basic_messages ++ [(is_forward_msg_, TBool)]

forward_msg_table :: [(N.Attribute, SqlType)]
forward_msg_table = [ (eid_, TInt32)
                    , (forwardaddr_,  TString)
                    ]

filter_msg_table :: [(N.Attribute, SqlType)]
filter_msg_table =  [ (eid_, TInt32) 
                    , (suffix_,  TString)
                    ] 

--  ** Schema Variant for Privacy-focus Email (basic + signature + encryption + remailmessage)
privacyEmailSchema :: RSchema
privacyEmailSchema  = constructRSchema   [ ( employeelist,  privacy_employeelist)
                                         , ( messages,    privacy_messages)
                                         , ( recipientinfo, recipientinfo_table)
                                         -- , ( referenceinfo, referenceinfo_table)
                                         , ( remail_msg, remail_msg_table)
                                         ]
privacy_employeelist :: [(N.Attribute, SqlType)]
privacy_employeelist = basic_employeelist ++                          
                        [ (verification_key_, TString)
                        , (public_key_, TString)
                        ]

privacy_messages :: [(N.Attribute, SqlType)]
privacy_messages = basic_messages ++                    
                      [ (is_signed_, TBool)
                      , (is_encrypted_, TBool)
                      ]

remail_msg_table :: [(N.Attribute, SqlType)]
remail_msg_table = [ (eid_, TInt32) 
                   , (pseudonym_,  TString)
                   ]

--  ** Schema Variant for Group Email 
--     (basic + addressbook + signature + encryption + autoresponder + mailhost)
groupEmailSchema :: RSchema
groupEmailSchema  = constructRSchema   [ ( employeelist,  group_employeelist)
                                         , ( messages,    group_messages)
                                         , ( recipientinfo, recipientinfo_table)
                                         -- , ( referenceinfo, referenceinfo_table)
                                         , ( auto_msg, auto_msg_table)
                                         , ( alias, alias_table)
                                         , ( mail_host, mailhost_table)
                                         ]
group_employeelist :: [(N.Attribute, SqlType)]
group_employeelist = privacy_employeelist

group_messages  :: [(N.Attribute, SqlType)]
group_messages = privacy_messages ++ [(is_autoresponse_, TBool)]

sToAttribtue :: [(String, SqlType)] -> [(N.Attribute, SqlType)]
sToAttribtue = map (\(x,y) -> (N.Attribute x , y))

auto_msg_table  :: [(N.Attribute, SqlType)]
auto_msg_table =  sToAttribtue [ ("eid", TInt32)
                               , ("subject",  TString)
                               , ("body",  TString)
                               ]

alias_table  :: [(N.Attribute, SqlType)]
alias_table = sToAttribtue [ ("eid", TInt32)
                           , ("email",  TString)
                           , ("nickname",  TString)
                           ]

mailhost_table  :: [(N.Attribute, SqlType)]
mailhost_table = sToAttribtue  [ ("eid", TInt32)
                               , ("username",  TString)
                               , ("mailhost",  TString)
                               ]
--  ** Schema Variant for Premium Email 
premiumEmailSchema :: RSchema
premiumEmailSchema  = constructRSchema   [ ( employeelist,  premium_employeelist)
                                         , ( messages,    premium_messages)
                                         , ( recipientinfo, recipientinfo_table)
                                         -- , ( referenceinfo, referenceinfo_table)
                                         , ( forward_msg, forward_msg_table)
                                         , ( filter_msg, filter_msg_table)
                                         , ( remail_msg, remail_msg_table)
                                         , ( auto_msg, auto_msg_table)
                                         , ( alias, alias_table)
                                         , ( mail_host, mailhost_table)
                                         ]
                      where premium_employeelist = privacy_employeelist
                            premium_messages = group_messages ++ [(is_forward_msg_, TBool)]




