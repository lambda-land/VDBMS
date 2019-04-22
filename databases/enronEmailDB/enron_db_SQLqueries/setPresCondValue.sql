-- v_employee 
-- c1 
-- UPDATE v_employee SET presCond='signature AND addressbook AND  filtermag AND (NOT autoresponder)  AND (NOT forwardmsg) AND (mailhost) AND ( NOT encrypt) AND (NOT remailmsg)'
-- WHERE eid < 75;

-- c2
-- UPDATE v_employee SET presCond='signature AND addressbook AND  filtermag AND  autoresponder AND forwardmsg AND mailhost AND ( NOT encrypt) AND (NOT remailmsg)'
-- WHERE eid >=75 and eid <125;

-- c3
-- UPDATE v_employee SET presCond='signature AND addressbook AND  filtermag AND  autoresponder AND forwardmsg AND mailhost AND encrypt AND remailmsg'
-- WHERE eid >=75 and eid <125;

-- UPDATE v_message SET presCond = 'TRUE'

-- UPDATE v_recipientinfo SET presCond = 'TRUE' 

-- UPDATE v_referenceinfo SET presCond = 'TRUE'

-- UPDATE v_auto_msg SET presCond = 'TRUE'

-- UPDATE v_forward_msg SET presCond = 'TRUE' 

-- UPDATE v_remail_msg SET presCond = 'TRUE'

-- UPDATE v_filter_msg SET presCond = 'TRUE'

-- UPDATE v_mailhost SET presCond = 'TRUE'

UPDATE v_alias SET presCond = 'TRUE'