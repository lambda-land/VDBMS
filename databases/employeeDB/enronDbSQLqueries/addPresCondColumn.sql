-- alter table v_employee
-- ADD COLUMN presCond VARCHAR(31) ;

UPDATE v_employee 
SET presCond= "signature or addressbook or filtermsg"
WHERE v_employee.eid  <75

-- UPDATE v_employee 
-- SET presCond= "signature or addressbook or filtermsg or autoresponder or forwardmsg or mailhost"
-- WHERE v_employee.eid  >=75 and v_employee.eid  < 125 

-- UPDATE v_employee 
-- SET presCond= "signature or addressbook or filtermsg or autoresponder or forwardmsg or mailhost or encrypt or remailmsg"
-- WHERE v_employee.eid  >= 125 

