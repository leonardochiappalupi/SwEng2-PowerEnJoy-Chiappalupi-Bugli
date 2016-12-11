class ReservationManager {
	public static final int MAX_SHARED_USERS = 4;
	public static final int RESERVATION_TIMEOUT_MINUTES = 60;
	
	UsersManagement uMan;
	PaymentProcessor pProc;
	RideController rContr;
	Map<Reservation, Timer> feeTimers = new HashMap<Reservation, Timer>(); // Timers for reservation fees
	Map<Reservation, List<String>> sharedUsers = new HashMap<Reservation, List<String>>(); 
	// A simple map to link shared users with relative reservations
	
	public boolean createReservation (String user, Car car) {
		RegisteredUser userData = uMan.getCompleteUserData(user);
		if(userData.getActiveReservation() == null){ // If the user has not already an active res.
			Reservation reservation = new Reservation (car); // Create the reservation
			car.setStatus(Status.reserved); // Set the car status as "reserved"
			userData.setActiveReservation(reservation); // Set the created reservation as the user' active
			Timer newTimer = new Timer(true); // Create a timer for this reservation
			feeTimers.put(reservation, newTimer); // Put the timer in the map
			newTimer.scheduleAtFixedRate(new feeTimer(user, reservation), 0, 1000); // Schedule it
			return true;
		} else return false;
	}
	
	// Add a shared user to a reservation
	public void addSharedUser (String user, Reservation res, String sharingUser) {
		RegisteredUser userData = uMan.getCompleteUserData(user);
		if(userData.getActiveReservation().equals(res)){ // If the reservation is the user' active one
			List<String> currentSharedUsers = sharedUsers.get(res); // Get the shared users for that res.
			// If sh. users are not over the maximum and do not already feature the new user:
			if(!currentSharedUsers.contains(sharingUser) && currentSharedUsers.size() < MAX_SHARED_USERS)
				currentSharedUsers.addSharedUser(sharingUser); // Add the new shared user
			
		}
	}
	
	private class feeTimer extends TimerTask {
		private int secondsRemaining = 60 * RESERVATION_TIMEOUT_MINUTES;
		private Reservation res;
		private String user;
		
		public feeTimer(String user, Reservation res){
			this.res = res;
			this.user = user;
		}
		
		@Override
		public void run(){
			secondsRemaining--; // Called every second
			if(secondsRemaining <= 0){ // If the timer reaches zero
				cancelReservation(user, res); // Cancel the reservation
				pProc.payFee(res); // Pay the fee
			}
				
		}
	}
	
	public void stopReservationTimer(Reservation res) {
		Timer t = feeTimers.get(res);
		if(t!=null){
			t.cancel;
			feeTimers.remove(res);
		}
	}
	
	public void cancelReservation(String user, Reservation res) {
		RegisteredUser userData = uMan.getCompleteUserData(user);
		if(userData.getActiveReservation().equals(res)){
			stopReservationTimer(res); // Stop the possibly active timer for this res.
			userData.setActiveReservation(null); // Remove the res. from the user' active
			res.getCar().setStatus(Status.reservable); // Reset the car status
		}
	}
	
	// Called to move from a reservation to the ride
	public boolean markSucceded(String user, Reservation res) {
		stopReservationTimer(res); // Stop the relative timer
		RegisteredUser userData = uMan.getCompleteUserData(user);
		userData.setActiveReservation(null); 
		userData.getSuccededReservations().add(res); // Move this res. to user' succeded ones
		// Delegate the control to RideController by issuing the creation of the new ride
		return rContr.createRideForRes(user, res, getSharedUsersCompleteList(sharedUsers.get(res)));
		
	}
		
	// Get a list of RegisteredUsers by a list of their usernames
	private List<RegisteredUser> getSharedUsersCompleteList(List<String> usernames) {
		List<RegisteredUser> usersData = new ArrayList<RegisteredUsers>();
		for(String username : usernames)
			userData.add(uMan.getCompleteUserData(username));
		return usersData;
	}
	