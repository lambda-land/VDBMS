INSERT INTO auto_msg_view (eid, subject, body)
SELECT eid, "out of office", "Hi,
I'm enjoying a holiday at sea and will be off the grid until the 15th of January! I'll get back to you that week. You could also reach out to my colleagues via support@email.com.
Thanks for your patience and talk to you then!
Best regards,
"
FROM v_employee WHERE eid>=75;