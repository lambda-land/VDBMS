SELECT msg.subject as originalSubject, auto.subject as autoSubject, auto.body as autoBody
FROM (v_recipientinfo rec
inner join v_employee emp on rec.rvalue = emp.email_id)
inner join v_auto_msg auto on auto.eid = emp.eid, v_message msg
Where  rec.mid = 9138 and msg.mid = 9138