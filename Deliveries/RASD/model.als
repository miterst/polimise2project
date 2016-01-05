
abstract sig User { }

some sig Passenger extends User {
	mkRequest: set Request, //can make multiple requests and reservations, also none
	mkReservation: set Reservation
 }

some sig Administrator extends User { }

enum DriverStatus { Available, Busy }

some sig TaxiDriver extends User {		
	status: one DriverStatus,
	drivesTaxi: one Taxi,
	recvRequest: some Request,
	recvReservation: some Reservation
}

some sig Integer {}

some sig Taxi {
	tCode: one Integer,
	drivenBy: one TaxiDriver,
	inQueue: one Queue
}

some sig Location {}

sig Ride {
	origin: one Location,
	destination: one Location
}

some sig Request  extends Ride { 
	closeZone: one Zone //which taxi zone is close
}

some sig Reservation extends Ride {	forWhen: one DateTime }

some sig DateTime {}


some sig Queue {
	taxiIn: some Taxi,
	inZone: one Zone
}

some sig Zone {
	queueIn: some Queue
}

//only one system
one sig System {
	processRequest: Request some -> some TaxiDriver, 
	processReservation: Reservation some -> some TaxiDriver,
	confirmRequest: Request one -> one Passenger,
	confirmReservation: Reservation one -> one Passenger
}


//received request or reservations are equal to those send be passengers
fact { 
	Passenger.mkRequest = System.processRequest.TaxiDriver
	Passenger.mkReservation = System.processReservation.TaxiDriver
}

//taxi has single driver
fact {
    drivesTaxi = ~drivenBy
	all t: Taxi | #(t.drivenBy) = 1
}

//driver don't receive request if he is busy
fact {
		all d: TaxiDriver | #(System.processRequest.d) > 0 => d.status = Available 
}

//send confirmation for coresponding request 
fact {
	System.processRequest.TaxiDriver = System.confirmRequest.Passenger
	System.processReservation.TaxiDriver = System.confirmReservation.Passenger	
}

//taxi can't be in two queues 
fact {
	all t: Taxi | #(t.inQueue) = 1
  	inQueue = ~taxiIn
}

//every queue has one zone
fact {	
	all q: Queue | #(q.inZone) = 1
	inZone = ~queueIn
}

//origin != destination
fact {
	all rq: Request | rq.origin != rq.destination
	all rs: Reservation | rs.origin != rs.destination
}

//no two reservations from the same passenger at the same time
fact {
	all p: Passenger  | no disj r1, r2: p.mkReservation | r1.forWhen = r2.forWhen
}


//no two taxi have the same codes
fact {
	no disj t1, t2: Taxi | t1.tCode = t2.tCode
}

//send request to the taxi in the corresponding zone
fact {
	all s: System | all d: TaxiDriver | (s.processRequest.d).closeZone = d.drivesTaxi.inQueue.inZone		
}



pred show {}

run show 
