open util/boolean

sig Plate {}

sig DateAndTime {}

abstract sig User {}

sig Operator extends User {
	carAssigned: lone Car,
	requestAssigned: lone AssistanceRequest
}

sig AssistanceRequest {
	user: one RegisteredUser,
	location: one Location
}

enum CarState {
	reservable, charging, reserved, outOfOrder, lowBattery
}

enum SurchargeOrDiscount {
	surcharge, discount
}

abstract sig ExtraCharge {
	type: one SurchargeOrDiscount,
	percentage: one Int
}

lone sig SharingDiscount extends ExtraCharge {}

lone sig BatteryLevelDiscount extends ExtraCharge {}

lone sig PlugDiscount extends ExtraCharge {}

lone sig CarStatusPenalty extends ExtraCharge {}
	
one sig Fleet {
	cars: set Car
}

sig Car {
	plate: one Plate,
	status: one CarState,
	position: one Location,
	batteryLeft: one Int,
	plugged: one Bool
}
{
	batteryLeft > 0
	batteryLeft < 100
}

sig CarLeftConditions {
	batteryLeft: one Int,
	plugged: one Bool,
	distantFromPlug: one Bool
}
{
	batteryLeft > 0
	batteryLeft < 100
}

sig Location {}

sig Guest extends User {}

sig RegisteredUser extends User {
	activeReservation: lone Reservation,
	succededReservations: set Reservation,
	rides: set Ride,
	disabled: one Bool
}

sig SystemManager extends User {}

sig ParkingArea {
	bounds: set Location
}

one sig Parkings {
	normalAreas: set ParkingArea,
	plugAreas: set ParkingArea
}

sig Ride {
	totalPrice: Int,
	reservation: one Reservation,
	timeStart: one DateAndTime,
	timeEnd: one DateAndTime,
	vehicle: one Car,
	sharedUsers: set RegisteredUser,
	park: one ParkingArea,
	carLeftState: one CarLeftConditions,
	extras: set ExtraCharge,
	paymentOk: one Bool
}
{
	totalPrice > 0
}

sig Reservation {
	time: one DateAndTime,
	car: one Car
}


//Disabled user must have one ride whose payment is not ok and cannot make reservations
fact DisabledUserMustHaveProblems {
	all u: RegisteredUser | u.disabled = True implies (one r: Ride | r in u.rides and r.paymentOk = False) and #u.activeReservation = 0
	all r: Ride | r.paymentOk = False implies (one u: RegisteredUser | r in u.rides and u.disabled = True)
}

//No more than 1 active reservation for same car
fact OneReservationPerCar {
	no disj u1, u2 : RegisteredUser | 
		(some r1 : u1.activeReservation, r2 : u2.activeReservation | r1.car = r2.car)
}

assert noOneCarMultipleRes {
	no disj u1, u2 : RegisteredUser | 
		(some r1 : u1.activeReservation, r2 : u2.activeReservation | r1.car = r2.car)
}

check noOneCarMultipleRes for 5



//No user is a "shared user" of one of his/her rides
fact UsersShareOnlyWithOthers {
	no r: Ride, u: RegisteredUser | r in u.rides and u in r.sharedUsers
}

assert noSelfShared {
	no r: Ride, u: RegisteredUser | r in u.rides and u in r.sharedUsers
}

check noSelfShared for 5



//A reservation is either active or past (succeded)
fact ReservationsAreActiveOrPast {
	no u: RegisteredUser | (some r: Reservation | r in u.activeReservation and r in u.succededReservations)
}

//There is no reservation that corresponds to multiple users
fact noOneResForMultiUsers {
	no r: Reservation | (some disj u1, u2: RegisteredUser |
		((r in u1.succededReservations or r in u1.activeReservation) and
		(r in u2.succededReservations or r in u2.activeReservation)))
}

assert noOneResForMultiUsers {
	no r: Reservation | (some disj u1, u2: RegisteredUser |
		((r in u1.succededReservations or r in u1.activeReservation) and
		(r in u2.succededReservations or r in u2.activeReservation)))
}

check noOneResForMultiUsers for 5

//No reservation for multiple rides
fact ReservationsAreExclusive {
	all disj r1, r2: Ride | r1.reservation != r2.reservation
}

//Car in a ride is the same of the reservation
fact RideAndResSameCar {
	all r: Ride | r.reservation.car = r.vehicle
}

assert noDifferentCarsForResAndRide {
	no r: Ride, res: Reservation | res = r.reservation and not res.car=r.vehicle
}

check noDifferentCarsForResAndRide for 5

//There is no ride without a user
fact RidesAlwaysHaveAUser {
	all r: Ride | (one u: RegisteredUser | r in u.rides)
}

assert NoRideWithoutUser {
	no r: Ride | (no u: RegisteredUser | r in u.rides)
}

check NoRideWithoutUser for 5

//There is no ride without corresponding succeded reservation and vv
fact RidesAndPastReservationsProperty {
	all r: Ride, res: Reservation, u: RegisteredUser |
		(res = r.reservation and r in u.rides implies res in u.succededReservations) and
		(res = r.reservation and res in u.succededReservations implies r in u.rides)
}

assert NoRideWithoutReservation {
	no r: Ride, res: Reservation, u: RegisteredUser |
		((r in u.rides and res = r.reservation and not res in u.succededReservations) or
		(res in u.succededReservations and res = r.reservation and not r in u.rides))
}

check NoRideWithoutReservation for 5

//There is no ride linked to more than 1 user
fact EveryRideOneUser {
	//no disj u1, u2: RegisteredUser | (some r: Ride | r in u1.rides and r in u2.rides)
	all disj u1, u2: RegisteredUser | #(u1.rides & u2.rides) = 0
}

//Normal parking spots and plug parking spots do not collide (i.e. have always 
//different locations)
fact PlugAndSpotsDifferent {
	all disj pa1, pa2: ParkingArea | #(pa1.bounds & pa2.bounds) = 0
	#(Parkings.normalAreas & Parkings.plugAreas) = 0
}

assert NoCollidingSpots {
	no disj pa1, pa2: ParkingArea | some l: Location | l in (pa1.bounds & pa2.bounds)
}

check NoCollidingSpots for 5

//There is no parking spot that is not neither a normal nor a plug spot
fact AllParkingsHaveType {
	all pa: ParkingArea | pa in Parkings.normalAreas or pa in Parkings.plugAreas
}

//If a car is plugged, then it must be in a plug parking spot
fact PluggedCars {
	all c: Car | c.plugged.isTrue implies (some p: ParkingArea | p in Parkings.plugAreas and c.position in p.bounds)
}

----------------------------------------------------------------------------------------------------
//Service management predicates

//Predicate: add  and remove parking spots (for service managers)
pred addNormalParkingArea(p: ParkingArea, pp, pp': Parkings) {
	p not in pp.normalAreas implies pp'.normalAreas = pp.normalAreas + p
}

pred addPlugParkingArea(p: ParkingArea, pp, pp': Parkings) {
	p not in pp.plugAreas implies pp'.plugAreas = pp.plugAreas + p
}

run addNormalParkingArea for 5

run addPlugParkingArea for 5

pred removeParkingArea(p: ParkingArea, pp, pp': Parkings) {
	p in pp.normalAreas implies pp'.normalAreas = pp.normalAreas - p and
	p in pp.plugAreas implies pp'.plugAreas = pp.plugAreas - p
}

run removeParkingArea for 5

//Predicate: add and remove cars to fleet
pred addCarToFleet(c: Car, fl, fl': Fleet) {
	c not in fl.cars implies fl'.cars = fl.cars + c
}

run addCarToFleet for 5

pred removeCarFromFleet(c: Car, fl, fl': Fleet) {
	c in fl.cars implies fl'.cars = fl.cars - c
}

run removeCarFromFleet for 5

----------------------------------------------------------------------------------------------------
//Service management

//Cars assigned to operators must have some problem
fact OperatorsCars {
	all c: Car | (one o: Operator | c = o.carAssigned) implies c.status in lowBattery + outOfOrder
}

//Operators have only one duty active
fact OperatorsExclusive {
	all o: Operator | #o.carAssigned = 1 implies #o.requestAssigned = 0
	all o: Operator | #o.requestAssigned = 1 implies #o.carAssigned = 0
}

//Cars that need assistance can only be assigned to one operator
fact MaxOneOperatorPerCar {
	all disj o1, o2: Operator | #(o1.requestAssigned & o2.requestAssigned) = 0
	all disj o1, o2: Operator | #(o1.carAssigned & o2.carAssigned) = 0
}

//There are no users that have more than 1 pending requests
fact OneRequestPerUser {
	all disj a1, a2: AssistanceRequest | #(a1.user & a2.user) = 0
}

----------------------------------------------------------------------------------------------------
//Car properties and constraints

//All cars are in the fleet
fact CarFleet {
	all c: Car | c in Fleet.cars
}

//Cars have different (uniques) plates
fact UniquePlates {
	all disj c1, c2: Car | c1.plate != c2.plate
}

//If a car has low battery and it is not plugged, it must be broken or marked as lowBattery
fact UnpluggedLowBatteryCarsNotReservable {
	all c: Car | (c.batteryLeft < 20 and c.plugged = False) implies (c.status = outOfOrder or c.status = lowBattery)
}

//If a car has low battery but it is plugged, it may be outOfOrder or charging, waiting for its
//battery to reach 80%
fact PluggedLowBatteryCarsNotReservable {
	all c: Car | (c.batteryLeft < 20 and c.plugged = True) implies (c.status = outOfOrder or c.status = charging)
}

//Two cars cannot be in the same position at the same time
fact CarsHaveDifferentPositions {
	all disj c1, c2: Car | c1.position != c2.position
}

//If a car is reservable or already reserved, it must be in a parking spot
fact ReservableCarsAreParked {
	all c: Car | (c.status = reservable or c.status = reserved) implies c.position in (Parkings.plugAreas.bounds + Parkings.normalAreas.bounds)
}

//Cars in active reservations can only be "reserved" (i.e. working and not reservable)
fact ReservedCarsNotReservableOrBroken {
	no u: RegisteredUser, c: Car, r: Reservation | c = r.car and r = u.activeReservation and c.status != reserved
}

//If a car is "reserved", than there must exist a user that has an active reservation on it
fact ReservedCarsHaveAReservingUser {
	all c: Car | (c.status = reserved implies (some u: RegisteredUser | u.activeReservation.car = c))
}

//If a car has no special conditions, it must be either outOfOrder or reservable
fact CarsArePossiblyReservable {
	all c: Car | c.batteryLeft > 20 and c.status != reserved and c.status != outOfOrder implies c.status = reservable
}

----------------------------------------------------------------------------------------------------
//Discounts or surcharge properties
fact CarLeftConditionsProperties {
	all clc: CarLeftConditions | (some rd: Ride | clc = rd.carLeftState)
	all clc: CarLeftConditions, rd: Ride | clc = rd.carLeftState and clc.plugged = True implies rd.park in Parkings.plugAreas and clc.distantFromPlug = False
	all rd: Ride | rd.park in Parkings.plugAreas implies (one clc: CarLeftConditions | clc = rd.carLeftState and clc.plugged = True and clc.distantFromPlug = False)

}

//Share discount
fact SharingDiscountProperties {
	all sd: SharingDiscount | (some r: Ride | sd in r.extras) and sd.percentage = 10 and sd.type = discount
	all r: Ride, sd: SharingDiscount | sd in r.extras implies #r.sharedUsers > 2
	all r: Ride | #r.sharedUsers > 2 implies one sd: SharingDiscount | sd in r.extras
}

//PlugDiscount
fact PlugDiscountProperties {
	all pd: PlugDiscount | (some r: Ride | pd in r.extras) and pd.percentage = 30 and pd.type = discount
	all r: Ride, pd: PlugDiscount | pd in r.extras implies r.carLeftState.plugged = True
	all r: Ride | r.carLeftState.plugged = True implies one pd: PlugDiscount | pd in r.extras
}

//BatteryLevelDiscount
fact BatteryLevelDiscountProperties {
	all bld: BatteryLevelDiscount | (some r:Ride | bld in r.extras) and bld.percentage = 20 and bld.type = discount
	all r: Ride, bld: BatteryLevelDiscount | bld in r.extras implies r.carLeftState.batteryLeft > 50
	all r: Ride | r.carLeftState.batteryLeft > 50 implies one bld: BatteryLevelDiscount | bld in r.extras
}

//CarStatusPenalty
fact CarStatusPenaltyProperties {
	all csp: CarStatusPenalty | (some r: Ride | csp in r.extras) and csp.percentage = 30 and csp.type = surcharge
	all r: Ride, csp: CarStatusPenalty | csp in r.extras implies (r.carLeftState.batteryLeft < 20 or r.carLeftState.distantFromPlug = True)
	all r: Ride | (r.carLeftState.batteryLeft < 20 or r.carLeftState.distantFromPlug = True) implies one csp: CarStatusPenalty | csp in r.extras
}


----------------------------------------------------------------------------------------------------
//Constraints on time (before, after) not possible with this model. We simply state some constraint to get
//more plausible worlds:
fact NoInstantaneousRide {
	all r:Reservation, rd:Ride | r = rd.reservation implies r.time!=rd.timeStart and r.time!=rd.timeEnd
}

fact NoZeroTimeRide {
	all rd:Ride | rd.timeStart != rd.timeEnd
}

fact NoSimultaneousRides {
 no disj r1, r2: Ride | some u: RegisteredUser | (r1 in u.rides and r2 in u.rides) and r1.timeStart = r2.timeStart
} 


---------------------------------------------------------------------------------------------------
pred show() {
	#RegisteredUser > 1
	#Ride > 1
	#Reservation > 1
	#activeReservation > 0
	#SharingDiscount > 0
	//some c: Car | c.batteryLeft < 20 and c.plugged = True
	some c: Car | c.status = lowBattery
	some c: Car | c.status = reservable
	some c: Car | c.status = reserved
	some c: Car | c.status = outOfOrder
	some c: Car | c.status = charging
	//all r: RegisteredUser | some rd: Ride | rd in r.rides
	#Operator > 1
	#carAssigned > 0
	#requestAssigned > 0
	
}

run show for 6 but 8 int

pred showDisabled() {
	some u: RegisteredUser | u.disabled = True
}

run showDisabled for 6 but 8 int

pred showExtras() {
	#SharingDiscount > 0
	#CarStatusPenalty > 0
	#PlugDiscount > 0
	#BatteryLevelDiscount > 0
}

run showExtras for 6 but 8 int




