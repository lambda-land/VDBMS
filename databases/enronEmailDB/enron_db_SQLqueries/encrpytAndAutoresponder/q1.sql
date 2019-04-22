SELECT *
FROM (v_recipientinfo rec
inner join v_employee emp on rec.rvalue = emp.email_id)
inner join v_auto_msg auto on auto.eid = emp.eid
Where  rec.mid = 9138 