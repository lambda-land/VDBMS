select email_id, sign, concat("signature", " AND ", "(NOT remailmsg)") as presCond
from v_employee 
where eid = 123