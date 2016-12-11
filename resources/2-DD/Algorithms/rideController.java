class RideController {
	public static final float CHARGE_PER_MINUTE = 0.25f;
	public static final int SHARED_USERS_BONUS = 2;
	public static final int BATTERY_LEVEL_BONUS = 50;
	public static final int SURCHARGE_BATTERY_LEVEL = 20;
	public static final int MAX_DISTANCE_FOR_SHARING = 100; // In meters


	PaymentProcessor pProc;
	Map<Ride, Timer> timers = new HashMap<Ride, Timer>(); // A timer for every ride
	UsersManagement uMan;

	// This gets called from ReservationManager at markSucceded()
	public boolean createRideForRes (String user, Reservation res, List<RegisteredUser> sharedUsers) {
		// Check the position of every registered shared user and keep only those whose distance from
		// the car is less than MAX_DISTANCE_FOR_SHARING
		List<RegisteredUsers> actualSharedUsers = checkPositionForSharedUsers(sharedUsers, res.getCar());
		Ride activeRide = new Ride(res.getCar(), res, actualSharedUsers); // Create Ride object
		List<Ride> userRides = uMan.getCompleteUserData(user).getRides();
		userRides.add(activeRide); // Adds the new ride as last of user' rides
		CarDataService carInt = res.getCar().getCarDataService();
		
		if(carInt != null)
			boolean unlocked = carInt.unlock(); // Unlocks the car
			if (unlocked)
				return true;
			else
				return false;
		else return false;
		}

	private List<RegisteredUser> checkPositionForSharedUsers(List<RegisteredUsers> candidates, Car c) {
		List<RegisteredUser> finalSharingUsers = new ArrayList<RegisteredUser>();
		for(RegisteredUser u : candidates) { // For every user candidate for sharing
			Location actualLoc = uMan.positionShare(u.getUsername());
			// If the distance to the car is lower than MAX_DISTANCE_FOR_SHARING
			if(Location.distance(c.getLocation(), actualLoc) < MAX_DISTANCE_FOR_SHARING)
				finalSharingUsers.add(u); // Add them to the returned list
		}
		return finalSharingUsers;
	}
			

	public void startCounting (Ride ride) {
		if(!timers.containsKey(ride)) {
			Timer timer = new Timer(true);
			timer.scheduleAtFixedRate (new TimeUpdater(ride), 0, 60000); //Schedules time update every minute
			timers.put(ride, timer);
		} else {
			timers.get(ride).scheduleAtFixedRate (new TimeUpdater(ride), 0, 60000);
		}
		
	}	

	private class TimeUpdater extends TimerTask {
		Ride ride;
				
		public TimeUpdater (Ride ride) {
			this.ride = ride;
			}

		@Override
		public void run(){
			ride.setTime(ride.getTime() + 1); //Updates the time count in the system
			ride.getCar().getCarDataService().updateTime(ride.getTime()); //Sends updated count to the car
		}
	}

	public void stopCounting (Ride ride) {
		if(timers.containsKey(ride)) {
			timers.get(ride).cancel();
			timers.remove(ride);
		}
	}

	public boolean termRide (String user, Ride rd, ParkingArea pa, CarLeftConditions clc) { //Invocated by ClientReqDisp that must have already checked the termination conditions
		RegisteredUser owner = uMan.getCompleteUserData(user);
		lastUserRide = owner.getRides().get(owner.getRides().size - 1);
		if (lastUserRide.equals(rd)) {
			lastUserRide.setPark(pa);
			lastUserRide.setCarLeftConditions(clc);
			computeTempPrice(lastUserRide); //Calculates price without extras
			processExtras(lastUserRide, pa, clc); //Adds extras
			bool paymentOk = pProc.executeTransaction(username, lastUserRide, lastUserRide.getTotalCost()); //Delegates payment to PaymentProcessor
			lastUserRide.setPaymentOk(paymentOk);
			boolean locked = lastUserRide.getCar().getCarDataService().lock(); // Lock the car
			if(locked)
				return true;
			else return false;
		} else return false;
	}

	private void computeTempPrice(Ride ride) {
		float totalPrice = ride.getTime() * CHARGE_PER_MINUTE;
		ride.setTotalCost(totalPrice);
	}

	private void processExtras(Ride ride, ParkingArea pa, CarLeftConditions clc) {
		List<Extra> extras = new ArrayList<Extra>();
		
		//Extras added from the least to the most convenient
		checkSharingDiscountEligibility(extras, ride);
		checkBatteryLevelDiscountEligibility(extras, clc);
		checkPlugDiscount(extras, pa, clc);
		checkCarStatusPenalty(extras, clc);

		for(Extra e: extras)
			applyExtra(ride, e);
		
		ride.setExtras(extras);
	}

	private void checkSharingDiscountEligibility(List<Extra> extras, Ride ride) {
		if(ride.getSharedUsers().size() > SHARED_USERS_BONUS)
			extras.add(new SharingDiscount());
	}

	private void checkBatteryLevelDiscountEligibility(List<Extra> extras, CarLeftConditions clc) {
		if(clc.getBatteryLeft() > BATTERY_LEVEL_BONUS)
			extras.add(new BatteryLevelDiscount());
	}

	private void checkPlugDiscount(List<Extra> extras, ParkingArea pa, CarLeftConditions clc) {
		if(pa.isPlug() && clc.isPlugged() == true)
			extras.add(new PlugDiscount());
	}

	private void checkCarStatusPenalty(List<Extra> extras, CarLeftConditions clc) {
		if(clc.isDistantFromPlug() && clc.getBatteryLeft() < SURCHARGE_BATTERY_LEVEL)
			extras.add(new CarStatusPenalty());
	}

	private void applyExtra(Ride ride, Extra e) {
		float diff = ride.getTotalCost * e.getPercentage() / 100f;
		if(e.getExtraType() == surcharge)
			ride.setTotalCost(ride.getTotalCost() + diff);
		else if (e.getExtraType() == discount)
			ride.setTotalCost(ride.getTotalCost() - diff);
	}
	
		
			







