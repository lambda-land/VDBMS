-- | translated Query for interaction between encrypt and autoresponder
(SELECT NULL as originalSubject, auto.subject as autoSubject, auto.body as autoBody, concat("encrypt", " AND ", "autoresponder") as presCond
FROM (v_recipientinfo rec
inner join v_employee emp on rec.rvalue = emp.email_id)
inner join v_auto_msg auto on auto.eid = emp.eid
Where  rec.mid = 9138)

-- (SELECT NULL as originalSubject, NULL as autoSubject,NULL as autoBody, concat("encrypt", " AND ", "(NOT autoresponder)") as presCond
-- FROM v_employee)

union all 

(SELECT msg.subject as originalSubject, auto.subject as autoSubject, auto.body as autoBody, concat("(NOT encrypt)", " AND ", "autoresponder") as presCond
FROM (v_recipientinfo rec
inner join v_employee emp on rec.rvalue = emp.email_id)
inner join v_auto_msg auto on auto.eid = emp.eid, v_message msg
Where  rec.mid = 9138 and msg.mid = 9138)

