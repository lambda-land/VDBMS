import psycopg2

conn = psycopg2.connect(user="ataeip", password="Pata@1993", dbname="enronemail")
cur = conn.cursor()

messages = []
recipients = []
references = []

with open('emailDatasets/enron-mysqldum_v5.sql') as myFile:
	for line in myFile:
		if line.startswith("INSERT INTO `message`"):
			processMessage = True 
			processRecipient = False
			processRef = False
		elif line.startswith("INSERT INTO `recipientinfo`"):
			processRecipient = True
			processRef = False
			processMessage = False
		elif line.startswith("INSERT INTO `referenceinfo`"):
			processRef = True
			processMessage = False
			processRecipient = False
		elif (line.startswith("\t(") and processMessage):
			messages.append([])
			messages[len(messages) - 1].append((line.split(", ")[0]).replace("\t(",""))
			#messages[len(messages) - 1].append((line.split(", ")[1]).replace("'",""))
			#messages[len(messages) - 1].append((line.split(", ")[2]).replace("'",""))
			#messages[len(messages) - 1].append((line.split(", ")[3]).replace("'",""))
			messages[len(messages) - 1].append((line.split("'")[1]))
			messages[len(messages) - 1].append((line.split("'")[3]))
			messages[len(messages) - 1].append((line.split("'")[5]))
			messages[len(messages) - 1].append((line.split("'")[7]))
			messages[len(messages) - 1].append((line.split("'")[9]))
			messages[len(messages) - 1].append((line.split("'")[11]))
		elif (line.startswith("\t(") and processRecipient):
			recipients.append([])
			recipients[len(recipients) - 1].append((line.split(", ")[0]).replace("\t(",""))
			recipients[len(recipients) - 1].append((line.split(", ")[1]))
			recipients[len(recipients) - 1].append((line.split(", ")[2]).replace("'",""))
			recipients[len(recipients) - 1].append((line.split(", ")[3]).replace("'",""))
			#recipients[len(recipients) - 1].append((line.split(",")[4]).replace(")","").replace(" ",""))
		elif (line.startswith("\t(") and processRef):
			references.append([])
			references[len(references) - 1].append((line.split(", ")[0]).replace("\t(",""))
			references[len(references) - 1].append((line.split(", ")[1]))
			references[len(references) - 1].append((line.split(", ",2)[2]).replace("),\n","").replace(");\n","").replace("'",""))



for msg in messages:

	mid = msg[0]
	sender = msg[1]
	date = msg[2]
	message_id = msg[3]
	subject = msg[4]
	body = msg[5]
	folder = msg[6]

	insertMsg = """insert into message values 
	(%s, %s, %s, %s, %s, %s, %s);
	"""

	data = (mid, sender, date, message_id, subject, body, folder)
	#print data

	cur.execute(insertMsg, data)
	conn.commit()

for rec in recipients:
	
	rid = rec[0]
	mid = rec[1]
	rtype = rec[2]
	rvalue = rec[3]
	#dater = rec[4]

	insertRec = """insert into recipientinfo 
	(rid, mid, rtype, rvalue) values
	(%s, %s, %s, %s);
	"""

	data = (rid, mid, rtype, rvalue)
	#print data

	cur.execute(insertRec, data)
	conn.commit()


for ref in references:

	rfid = ref[0]
	mid = ref[1]
	reference = ref[2]

	insertRef = """insert into referenceinfo values
	(%s, %s, %s);
	"""

	data = (rfid, mid, reference)
	#print data

	cur.execute(insertRef, data)
	conn.commit()






cur.close()
#result = conn.query(insertionQuery)


#for mid in result.getresult():
#	print mid

conn.close()