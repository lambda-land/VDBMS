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
mid = attr "mid"
sender = attr "sender"
is_signed = attr "is_signed"
is_encrypted = attr "is_encrypted"
is_from_remailer = attr "is_from_remailer"
forwardaddr :: N.Attr 
forwardaddr = attr "forwardaddr"

rvalue :: N.Attr 
rvalue = attr "rvalue"

pseudonym, suffix :: N.Attr 
pseudonym = attr "pseudonym"
suffix = attr "suffix"


-- vemployee_eid, vemployee_firstname, vemployee_lastname, vemployee_email_id :: N.Attr
-- vemployee_folder,vemployee_status, vemployee_sign, vemployee_public_key,vemployee_did :: N.Attr 
-- vemployee_eid       = qualifiedAttr v_employee (attr "eid") 
-- vemployee_firstname = qualifiedAttr v_employee (attr "firstname") 
-- vemployee_lastname  = qualifiedAttr v_employee (attr "lastname")
-- vemployee_email_id   = qualifiedAttr v_employee(attr "email_id")  
-- vemployee_folder    = qualifiedAttr v_employee (attr "folder")  
-- vemployee_status    = qualifiedAttr v_employee (attr "status")
-- vemployee_sign      = qualifiedAttr v_employee (attr "sign") 
-- vemployee_public_key= qualifiedAttr v_employee (attr "puclic_key")  
-- vemployee_did       = qualifiedAttr v_employee (attr "did")  

-- vmessage_mid, vmessage_sender, vmessage_date, vmessage_message_id :: N.Attr 
-- vmessage_subject, vmessage_body, vmessage_folder, vmessage_is_signed, vmessage_is_encrypted :: N.Attr
-- vmessage_mid          = qualifiedAttr v_message (attr "mid") 
-- vmessage_sender       = qualifiedAttr v_message (attr "sender")
-- vmessage_date         = qualifiedAttr v_message (attr "date")
-- vmessage_message_id   = qualifiedAttr v_message (attr "message_id") 
-- vmessage_subject      = qualifiedAttr v_message (attr "subject") 
-- vmessage_body         = qualifiedAttr v_message (attr "body") 
-- vmessage_folder        = qualifiedAttr v_message (attr "folder") 
-- vmessage_is_signed    = qualifiedAttr v_message (attr "is_signed") 
-- vmessage_is_encrypted = qualifiedAttr v_message (attr "is_encrypted")  

-- vrecipientinfo_rid, vrecipientinfo_mid, vrecipientinfo_rtype, vrecipientinfo_rvalue :: N.Attr
-- vrecipientinfo_rid   = qualifiedAttr v_recipientinfo (attr "rid") 
-- vrecipientinfo_mid   = qualifiedAttr v_recipientinfo (attr "mid") 
-- vrecipientinfo_rtype = qualifiedAttr v_recipientinfo (attr "rtype") 
-- vrecipientinfo_rvalue= qualifiedAttr v_recipientinfo (attr "rvalue") 

-- vreferenceinfo_rfid, vreferenceinfo_mid, vreferenceinfo_reference :: N.Attr
-- vreferenceinfo_rfid = qualifiedAttr v_referenceinfo (attr "rfid") 
-- vreferenceinfo_mid= qualifiedAttr v_referenceinfo (attr "mid")  
-- vreferenceinfo_reference= qualifiedAttr v_referenceinfo (attr "reference") 

-- vautomsg_eid, v_auto_msg_subject, v_auto_msg_body :: N.Attr 
-- vautomsg_eid = qualifiedAttr v_auto_msg (attr "eid") 
-- vautomsg_subject = qualifiedAttr v_auto_msg (attr "subject") 
-- vautomsg_body = qualifiedAttr v_auto_msg (attr "body") 

-- vforwardmsg_eid, v_forward_msg_forwardaddr :: N.Attr 
-- vforwardmsg_eid = qualifiedAttr v_forward_msg (attr "eid")
-- vforwardmsg_forwardaddr= qualifiedAttr v_forward_msg (attr "forwardaddr") 


-- v_remail_msg_eid, v_remail_msg_pseudonym, v_filter_msg_eid, v_filter_msg_suffix :: N.Attr 
-- v_mailhost_did, v_mailhost_username, v_alias_eid,v_alias_email, v_alias_nickname :: N.Attr 
-- v_alias_eid = qualifiedAttr v_alias (attr "eid") 
-- v_alias_email= qualifiedAttr v_alias (attr "email") 
-- v_remail_msg_eid = qualifiedAttr v_remail_msg (attr "eid")
-- v_remail_msg_pseudonym = qualifiedAttr v_remail_msg (attr "pseudonym")
-- v_mailhost_did= qualifiedAttr v_mailhost (attr "did") 
-- v_mailhost_username= qualifiedAttr v_mailhost (attr "username")
-- v_alias_eid= qualifiedAttr v_alias (attr "eid")
-- v_alias_email= qualifiedAttr v_alias (attr "email")
-- v_alias_nickname = qualifiedAttr v_alias (attr "nickname")


{-
--
-- ** schema 1
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                    (autoresponder, forwardmsg, mailhost),
--                     remailmsg
--    * disable feature: None


enronSchema1 :: Schema 
enronSchema1 = ( sign_addr_filter `Or` encryption `Or` auto_forward_mhost `Or` remailmsg, 
                                   constructRelMap [ ( "employeelist_v1",  employeelist_v1)
                                                   , ( "message_v1",    message_v1)
                                                   , ( "recipientInfo_v1",  recipientInfo_v1)
                                                   , ( "referenceInfo_v1",  referenceInfo_v1)
                                                   , ( "auto_msg_v1",  recipientInfo_v1)
                                                   , ( "forward_msg_v1",  recipientInfo_v1)
                                                   , ( "remail_msg_v1",  recipientInfo_v1)
                                                   , ( "filter_msg_v1",  recipientInfo_v1)
                                                   , ( "mailhost_v1",  mailhost_v1)
                                                   , ( "alias_v1",  alias_v1)

                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key, did, presCond)
employeelist_v1 :: [(String, SqlType)]
employeelist_v1 = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               , ("puclic_key", TString)
               , ("did", TInt32)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v1 :: [(String, SqlType)]
message_v1 =  [ ("mid", TInt32) 
                   , ("sender",  TString)
                   , ("date",  TString)
                   , ("message_id", TInt32)
                   , ("subject", TString)
                   , ("body", TString)
                   , ("folder", TString)
                   , ("is_signed", TBool)
                   , ("is_encrypted", TBool)
                   ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v1 :: [(String, SqlType)]
recipientInfo_v1 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v1 :: [(String, SqlType)]
referenceInfo_v1 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v1 :: [(String, SqlType)]
auto_msg_v1 =  [ ("eid", TInt32) 
               ,  ("subject",  TString)
               , ("body",  TString)
               ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v1 :: [(String, SqlType)]
forward_msg_v1 =  [ ("eid", TInt32)
                  , ("forwardaddr",  TString)
                  ]

-- remail_msg(eid, pseudonym, presCond)
remail_msg_v1 :: [(String, SqlType)]
remail_msg_v1 =   [ ("eid", TInt32) 
                  , ("pseudonym",  TString)
                  ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v1 :: [(String, SqlType)]
filter_msg_v1 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]

-- mailhost(did, domain, presCond)
mailhost_v1 :: [(String, SqlType)]
mailhost_v1 = [ ("did", TInt32)
              , ("domain",  TString)
              ]

-- alias(eid, email, nickname, presCond)
alias_v1 :: [(String, SqlType)]
alias_v1 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]

--
-- ** schema 2
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                    (autoresponder, forwardmsg, mailhost),
--                     
--    * disable feature: remailmsg

enronSchema2 :: Schema 
enronSchema2 = ( sign_addr_filter `Or` encryption `Or` auto_forward_mhost, 
                                   constructRelMap [ ( "employeelist_v2",  employeelist_v2)
                                                   , ( "message_v2",    message_v2)
                                                   , ( "recipientInfo_v2",  recipientInfo_v2)
                                                   , ( "referenceInfo_v2",  referenceInfo_v2)
                                                   , ( "auto_msg_v2",  recipientInfo_v2)
                                                   , ( "forward_msg_v2",  recipientInfo_v2)
                                                   , ( "filter_msg_v2",  recipientInfo_v2)
                                                   , ( "mailhost_v1",  mailhost_v1)
                                                   , ( "alias_v2",  alias_v2)

                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key,did, presCond)
employeelist_v2 :: [(String, SqlType)]
employeelist_v2 = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               , ("did", TInt32)
               , ("puclic_key", TString)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v2 :: [(String, SqlType)]
message_v2 =  [ ("mid", TInt32) 
                   , ("sender",  TString)
                   , ("date",  TString)
                   , ("message_id", TInt32)
                   , ("subject", TString)
                   , ("body", TString)
                   , ("folder", TString)
                   , ("is_signed", TBool)
                   , ("is_encrypted", TBool)
                   ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v2 :: [(String, SqlType)]
recipientInfo_v2 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v2 :: [(String, SqlType)]
referenceInfo_v2 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v2 :: [(String, SqlType)]
auto_msg_v2 =  [ ("eid", TInt32) 
               ,  ("subject",  TString)
               , ("body",  TString)
               ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v2 :: [(String, SqlType)]
forward_msg_v2 =  [ ("eid", TInt32)
                  , ("forwardaddr",  TString)
                  ]


-- filter_msg(eid, suffix, presCond)
filter_msg_v2 :: [(String, SqlType)]
filter_msg_v2 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]

-- mailhost(did, domain, presCond)
mailhost_v2 :: [(String, SqlType)]
mailhost_v2 = [ ("did", TInt32)
              , ("domain",  TString)
              ]

-- alias(eid, email, nickname, presCond)
alias_v2 :: [(String, SqlType)]
alias_v2 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]


--
-- ** schema 3
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                     remailmsg
--    * disable feature: (autoresponder, forwardmsg, mailhost)


enronSchema3 :: Schema 
enronSchema3 = ( sign_addr_filter `Or` encryption `Or` remail, 
                                   constructRelMap [ ( "employeelist_v3",  employeelist_v3)
                                                   , ( "message_v3",    message_v3)
                                                   , ( "recipientInfo_v3",  recipientInfo_v3)
                                                   , ( "referenceInfo_v3",  referenceInfo_v3)
                                                   , ( "remail_msg_v3",  recipientInfo_v3)
                                                   , ( "filter_msg_v3",  recipientInfo_v3)
                                                   , ( "alias_v3",  alias_v3)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key, did, presCond)
employeelist_v3 :: [(String, SqlType)]
employeelist_v3 = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               , ("puclic_key", TString)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v3 :: [(String, SqlType)]
message_v3 =  [ ("mid", TInt32) 
               , ("sender",  TString)
               , ("date",  TString)
               , ("message_id", TInt32)
               , ("subject", TString)
               , ("body", TString)
               , ("folder", TString)
               , ("is_signed", TBool)
               , ("is_encrypted", TBool)
               ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v3 :: [(String, SqlType)]
recipientInfo_v3 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v3 :: [(String, SqlType)]
referenceInfo_v3 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]


-- remail_msg(eid, pseudonym, presCond)
remail_msg_v3 :: [(String, SqlType)]
remail_msg_v3 =   [ ("eid", TInt32) 
                  , ("pseudonym",  TString)
                  ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v3 :: [(String, SqlType)]
filter_msg_v3 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]


-- alias(eid, email, nickname, presCond)
alias_v3 :: [(String, SqlType)]
alias_v3 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]


--
-- ** schema 4
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                     
--    * disable feature: (autoresponder, forwardmsg, mailhost)
--                       remailmsg


enronSchema4 :: Schema 
enronSchema4 = ( sign_addr_filter `Or` encryption, 
                                   constructRelMap [ ( "employeelist_v4",  employeelist_v4)
                                                   , ( "message_v4",    message_v4)
                                                   , ( "recipientInfo_v4",  recipientInfo_v4)
                                                   , ( "referenceInfo_v4",  referenceInfo_v4)
                                                   , ( "filter_msg_v4",  recipientInfo_v4)
                                                   , ( "alias_v4",  alias_v4)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key, did, presCond)
employeelist_v4 :: [(String, SqlType)]
employeelist_v4 = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               , ("puclic_key", TString)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v4 :: [(String, SqlType)]
message_v4 =  [ ("mid", TInt32) 
               , ("sender",  TString)
               , ("date",  TString)
               , ("message_id", TInt32)
               , ("subject", TString)
               , ("body", TString)
               , ("folder", TString)
               , ("is_signed", TBool)
               , ("is_encrypted", TBool)
               ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v4 :: [(String, SqlType)]
recipientInfo_v4 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v4 :: [(String, SqlType)]
referenceInfo_v4 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]


-- filter_msg(eid, suffix, presCond)
filter_msg_v4 :: [(String, SqlType)]
filter_msg_v4 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]


-- alias(eid, email, nickname, presCond)
alias_v4 :: [(String, SqlType)]
alias_v4 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]


--
-- ** schema 5
--    * enable feature: (signature, addressbook, filtermsg), 
--                    (autoresponder, forwardmsg, mailhost),
--                     remailmsg
--    * disable feature: encryption
--                     


enronSchema5 :: Schema 
enronSchema5 = ( sign_addr_filter `Or` auto_forward_mhost `Or` remail, 
                                   constructRelMap [ ( "employeelist_v5",  employeelist_v5)
                                                   , ( "message_v5",    message_v5)
                                                   , ( "recipientInfo_v5",  recipientInfo_v5)
                                                   , ( "referenceInfo_v5",  referenceInfo_v5)
                                                   , ( "auto_msg_v5",  recipientInfo_v5)
                                                   , ( "forward_msg_v5",  recipientInfo_v5)
                                                   , ( "remail_msg_v5",  recipientInfo_v5)
                                                   , ( "filter_msg_v5",  recipientInfo_v5)
                                                   , ( "mailhost_v5",  mailhost_v5)
                                                   , ( "alias_v5",  alias_v5)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, did, presCond)
employeelist_v5 :: [(String, SqlType)]
employeelist_v5 = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               , ("did", TInt32)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v5 :: [(String, SqlType)]
message_v5 =  [ ("mid", TInt32) 
                   , ("sender",  TString)
                   , ("date",  TString)
                   , ("message_id", TInt32)
                   , ("subject", TString)
                   , ("body", TString)
                   , ("folder", TString)
                   , ("is_signed", TBool)
                   ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v5 :: [(String, SqlType)]
recipientInfo_v5 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]

-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v5 :: [(String, SqlType)]
referenceInfo_v5 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v5 :: [(String, SqlType)]
auto_msg_v5 =  [ ("eid", TInt32) 
               ,  ("subject",  TString)
               , ("body",  TString)
               ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v5 :: [(String, SqlType)]
forward_msg_v5 =  [ ("eid", TInt32)
                  , ("forwardaddr",  TString)
                  ]

-- remail_msg(eid, pseudonym, presCond)
remail_msg_v5 :: [(String, SqlType)]
remail_msg_v5 =   [ ("eid", TInt32) 
                  , ("pseudonym",  TString)
                  ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v5 :: [(String, SqlType)]
filter_msg_v5 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]

-- mailhost(did, domain, presCond)
mailhost_v5 :: [(String, SqlType)]
mailhost_v5 = [ ("did", TInt32)
              , ("domain",  TString)
              ]

-- alias(eid, email, nickname, presCond)
alias_v5 :: [(String, SqlType)]
alias_v5 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]

--
-- ** schema 6
--    * enable feature: (signature, addressbook, filtermsg), 
--                    (autoresponder, forwardmsg, mailhost),
--                     
--    * disable feature: encryption
--                      ,remailmsg
--                     


enronSchema6 :: Schema 
enronSchema6 = ( sign_addr_filter `Or` auto_forward_mhost, 
                                   constructRelMap [ ( "employeelist_v6",  employeelist_v6)
                                                   , ( "message_v6",    message_v6)
                                                   , ( "recipientInfo_v6",  recipientInfo_v6)
                                                   , ( "referenceInfo_v6",  referenceInfo_v6)
                                                   , ( "auto_msg_v6",  recipientInfo_v6)
                                                   , ( "forward_msg_v6",  recipientInfo_v6)
                                                   , ( "filter_msg_v6",  recipientInfo_v6)
                                                   , ( "mailhost_v6",  mailhost_v6)
                                                   , ( "alias_v6",  alias_v6)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, did, presCond)
employeelist_v6 :: [(String, SqlType)]
employeelist_v6 = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               , ("did", TInt32)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v6 :: [(String, SqlType)]
message_v6 =  [ ("mid", TInt32) 
                   , ("sender",  TString)
                   , ("date",  TString)
                   , ("message_id", TInt32)
                   , ("subject", TString)
                   , ("body", TString)
                   , ("folder", TString)
                   , ("is_signed", TBool)
                   ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v6 :: [(String, SqlType)]
recipientInfo_v6 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]

-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v6 :: [(String, SqlType)]
referenceInfo_v6 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v6 :: [(String, SqlType)]
auto_msg_v6 =  [ ("eid", TInt32) 
               ,  ("subject",  TString)
               , ("body",  TString)
               ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v6 :: [(String, SqlType)]
forward_msg_v6 =  [ ("eid", TInt32)
                  , ("forwardaddr",  TString)
                  ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v6 :: [(String, SqlType)]
filter_msg_v6 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]

-- mailhost(did, domain, presCond)
mailhost_v6 :: [(String, SqlType)]
mailhost_v6 = [ ("did", TInt32)
              , ("domain",  TString)
              ]

-- alias(eid, email, nickname, presCond)
alias_v6 :: [(String, SqlType)]
alias_v6 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]

--
-- ** schema 7
--    * enable feature: (signature, addressbook, filtermsg), 
--                      remailmsg
--    * disable feature: encryption, 
--                       (autoresponder, forwardmsg, mailhost),



enronSchema7 :: Schema 
enronSchema7 = (sign_addr_filter `Or` remail, 
                                   constructRelMap [ ( "employeelist_v7",  employeelist_v7)
                                                   , ( "message_v7",    message_v7)
                                                   , ( "recipientInfo_v7",  recipientInfo_v7)
                                                   , ( "referenceInfo_v7",  referenceInfo_v7)
                                                   , ( "remail_msg_v7",  recipientInfo_v7)
                                                   , ( "filter_msg_v7",  recipientInfo_v7)
                                                   , ( "alias_v7",  alias_v7)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign,  presCond)
employeelist_v7 :: [(String, SqlType)]
employeelist_v7 = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v7 :: [(String, SqlType)]
message_v7 =  [ ("mid", TInt32) 
                   , ("sender",  TString)
                   , ("date",  TString)
                   , ("message_id", TInt32)
                   , ("subject", TString)
                   , ("body", TString)
                   , ("folder", TString)
                   , ("is_signed", TBool)
                   ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v7 :: [(String, SqlType)]
recipientInfo_v7 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v7 :: [(String, SqlType)]
referenceInfo_v7 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]



-- remail_msg(eid, pseudonym, presCond)
remail_msg_v7 :: [(String, SqlType)]
remail_msg_v7 =   [ ("eid", TInt32) 
                  , ("pseudonym",  TString)
                  ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v7 :: [(String, SqlType)]
filter_msg_v7 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]


-- alias(eid, email, nickname, presCond)
alias_v7 :: [(String, SqlType)]
alias_v7 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]

--
-- ** schema 8
--    * enable feature: (signature, addressbook, filtermsg), 
--
--    * disable feature: encryption, 
--                       (autoresponder, forwardmsg, mailhost),
--                       remailmsg



enronSchema8 :: Schema 
enronSchema8 = ( sign_addr_filter, constructRelMap [ ( "employeelist_v8",  employeelist_v8)
                                                   , ( "message_v8",    message_v8)
                                                   , ( "recipientInfo_v8",  recipientInfo_v8)
                                                   , ( "referenceInfo_v8",  referenceInfo_v8)
                                                   , ( "filter_msg_v8",  recipientInfo_v8)
                                                   , ( "alias_v8",  alias_v8)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign,  presCond)
employeelist_v8 :: [(String, SqlType)]
employeelist_v8  = [ ("eid", TInt32), 
                 ("firstname",  TString)
               , ("lastname",  TString)
               , ("email_id", TString)
               , ("folder", TString)
               , ("status", TString)
               , ("sign", TString)
               ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v8 :: [(String, SqlType)]
message_v8 =  [ ("mid", TInt32) 
                   , ("sender",  TString)
                   , ("date",  TString)
                   , ("message_id", TInt32)
                   , ("subject", TString)
                   , ("body", TString)
                   , ("folder", TString)
                   , ("is_signed", TBool)
                   ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v8 :: [(String, SqlType)]
recipientInfo_v8 = [ ("rid", TInt32)
                   , ("mid",  TInt32)
                   , ("rtype",  TString)
                   , ("rvalue_email", TString)
                   , ("rvalue_nickname", TString)
                   ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v8 :: [(String, SqlType)]
referenceInfo_v8 = [ ("rfid", TInt32)
                   , ("mid",  TInt32)
                   , ("reference",  TString)
                   ]



-- filter_msg(eid, suffix, presCond)
filter_msg_v8 :: [(String, SqlType)]
filter_msg_v8 = [ ("eid", TInt32) 
                , ("suffix",  TString)
                ]


-- alias(eid, email, nickname, presCond)
alias_v8 :: [(String, SqlType)]
alias_v8 = [ ("eid", TInt32)
           , ("email",  TString)
           , ("nickname",  TString)
           ]
-}
