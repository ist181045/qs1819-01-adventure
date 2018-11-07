/**
 * Software Specification 2018-2019 -- G12
 * 67030 - Leo Valente
 * 81045 - Rui Ventura
 * 81728 - Madalena Assembleia
 */
open util/ordering [Date] as D
open util/ordering [Time] as T

sig Date, Time {}

one sig AdventureBuilder {
  accounts: set Account -> Time,
  roomRes: set RoomReservation -> Time,
  offers: set ActivityOffer -> Time,
  actRes: set ActivityReservation -> Time,
  adventures: set Adventure -> Time
}

sig Client {}

sig Broker extends Client {}


sig Bank {
  accounts: some Account
}

sig Account {
  bank: one Bank, // 4
  client: one Client, // 3
  balance: Int one -> Time
}


sig Hotel {
  rooms: some Room // 10
}

sig Room {
  hotel: one Hotel, // 11
  type: one RoomType // 12
}

abstract sig RoomType {} // 12
one sig Single, Double extends RoomType {} // 12

sig RoomReservation {
  room: one Room,
  client: one Client,
  arrival, departure: one Date
}


sig ActivityProvider {
  activities: some Activity
}

sig Activity {
  provider: one ActivityProvider,
  capacity: one Int
}

sig ActivityOffer {
  activity: one Activity,
  begin, end: one Date,
  availability: Int one -> set Time
}

sig ActivityReservation {
  offer: one ActivityOffer,
  client: one Client,
  people: one Int
}

sig Adventure {
  client: one Client,
  people: one Int,
  broker: one Broker,
  roomRes: some RoomReservation,
  actRes: one ActivityReservation,
  cost: one Int,
  clientAcc: one Account,
  brokerAcc: one Account,
  state: AdventureState one -> Time // 21
}

abstract sig AdventureState {} // 21
one sig InitialState, PayedState, ConfirmedState extends AdventureState {}

//sig Invoice {
//  client: one Client,
//  type: one PurchaseType,
//  amount: one Int,
//  tax: one Int // ????
//}
//
//abstract sig PurchaseType {}
//one sig Leisure, Business extends PurchaseType {}


// Operations ------------------------------------------------------------------
// Auxiliary

// accounts
pred accountIsOpen[t: Time, acc: Account] {
  acc in AdventureBuilder.accounts.t
}

pred noAccountsChangeExcept[t, t': Time, acc: Account] {
  AdventureBuilder.accounts.t' = AdventureBuilder.accounts.t + acc
}

pred noAccBalanceChangeExcept[t, t': Time, acc: Account] {
  all a: Account - acc | a.balance.t' = a.balance.t
}

// rooms
pred roomResExists[t: Time, res: RoomReservation] {
  res in AdventureBuilder.roomRes.t
}

pred noRoomResMadeExcept[t, t': Time, res: RoomReservation] {
  AdventureBuilder.roomRes.t' = AdventureBuilder.roomRes.t + res
}

pred noRoomResCancelledExcept[t, t': Time, res: RoomReservation] {
  AdventureBuilder.roomRes.t' = AdventureBuilder.roomRes.t - res
}

pred datesConflict[a, a', d, d': Date] {
  a' = d || (a' = a || gt[a', a] && lt[a', d])
         || (d' = d || lt[d', d] && gt[d', a])
         || (lt[a', a] && gt[d', d])
}

pred roomResConflict[r, r': RoomReservation] {
  let a = r.arrival, a' = r'.arrival, d = r.departure, d' = r'.departure |
    r.room = r'.room || datesConflict[a, a', d, d']
}

// activities
pred offerExists[t: Time, off: ActivityOffer] {
  off in AdventureBuilder.offers.t
}

pred noOfferAvailChangeExcept[t, t': Time, off: ActivityOffer] {
  all o: ActivityOffer - off | o.availability.t' = o.availability.t
}

pred noOffersChangeExcept[t, t': Time, off: ActivityOffer] {
  AdventureBuilder.offers.t' = AdventureBuilder.offers.t + off
}

pred activityResExists[t: Time, res: ActivityReservation] {
  res in AdventureBuilder.actRes.t
}

pred noActResMadeExcept[t, t': Time, res: ActivityReservation] {
  AdventureBuilder.actRes.t' = AdventureBuilder.actRes.t + res
}

pred noActResCancelledExcept[t, t': Time, res: ActivityReservation] {
  AdventureBuilder.actRes.t' = AdventureBuilder.actRes.t - res
}

// adventures
pred adventureExists[t: Time, adv: Adventure] {
  adv in AdventureBuilder.adventures.t
}

pred noAdventureCreatedExcept[t, t': Time, adv: Adventure] {
  AdventureBuilder.adventures.t' = AdventureBuilder.adventures.t + adv
}

pred noAdventureCancelledExcept[t, t': Time, adv: Adventure] {
  AdventureBuilder.adventures.t' = AdventureBuilder.adventures.t - adv
}

pred noAdvStateChangeExcept[t, t': Time, adv: Adventure] {
  all a: Adventure - adv | a.state.t' = a.state.t
}

// Helper Ops

pred reserveActivity[t, t': Time, res: ActivityReservation] {
  // pre cond
  not activityResExists[t, res]
  offerExists[t, res.offer]
  res.people > 0 // 18
  // post cond
  activityResExists[t', res]
  offerExists[t', res.offer]
  let avail = res.offer.availability.t,
      result = minus[avail, res.people] | // 19
    result >= 0 &&
    res.offer.availability.t' = result
  // post/frame cond
  noActResMadeExcept[t, t', res]
}

pred cancelActivityReservation[t, t': Time, res: ActivityReservation] {
  // pre cond
  activityResExists[t, res]
  offerExists[t, res.offer]
  // post cond
  not activityResExists[t', res]
  offerExists[t', res.offer]
  let avail = res.offer.availability.t,
      result = plus[avail, res.people] |
    res.offer.availability.t' = result
  // post/frame
  noActResCancelledExcept[t, t', res]
  // frame cond
  noAccountsChangeExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', res.offer]
}

pred reserveRooms[t, t': Time, res: RoomReservation] {
  // pre cond
  not roomResExists[t, res]
  lt[res.arrival, res.departure]
  all r: RoomReservation - res | not roomResConflict[r, res]
  all r: res.room | one h: Hotel | r.hotel = h && r in h.rooms // 24
  // post cond
  roomResExists[t', res]
  // frame cond
  noRoomResMadeExcept[t, t', res]
}

// Main Ops

pred openAccount[t, t': Time, acc: Account] {
  // pre cond
  not accountIsOpen[t, acc] // 1
  // post cond
  accountIsOpen[t', acc] // 2
  acc.balance.t' = 0
  // frame cond
  noAccountsChangeExcept[t, t', acc]
  noAccBalanceChangeExcept[t, t', acc]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', none]
  noRoomResMadeExcept[t, t', none]
  noActResMadeExcept[t, t', none]
  noAdventureCreatedExcept[t, t', none]
  noAdvStateChangeExcept[t, t', none]
}

pred clientDeposit[t, t': Time, acc: Account, amt: Int] {
  // pre cond
  accountIsOpen[t, acc] // 7
  let result = plus[acc.balance.t, amt] {
    // pre cond
    result >= 0 // 8
    // post cond
    acc.balance.t' = result
  }
  // frame cond
  noAccountsChangeExcept[t, t', none] // 9
  noAccBalanceChangeExcept[t, t', acc]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', none]
  noRoomResMadeExcept[t, t', none]
  noActResMadeExcept[t, t', none]
  noAdventureCreatedExcept[t, t', none]
  noAdvStateChangeExcept[t, t', none]
}

pred makeActivityOffer[t, t': Time, off: ActivityOffer, avail: Int] {
  // pre cond
  not offerExists[t, off]
  lt[off.begin, off.end] // 16
  let cap = off.activity.capacity |
    cap > 0 && // 15
    (0 <= avail && avail <= cap) // 17
  // post cond
  offerExists[t', off]
  off.availability.t' = avail
  // frame cond
  noAccountsChangeExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', off]
  noOfferAvailChangeExcept[t, t', off]
  noRoomResMadeExcept[t, t', none]
  noActResMadeExcept[t, t', none]
  noAdventureCreatedExcept[t, t', none]
  noAdvStateChangeExcept[t, t', none]
}

pred createAdventure[t, t': Time, adv: Adventure] {
  // pre cond
  not adventureExists[t, adv]
  accountIsOpen[t, adv.brokerAcc]
  accountIsOpen[t, adv.clientAcc]
  adv.broker = adv.brokerAcc.client
  adv.client = adv.clientAcc.client
  adv.client not in Broker
  adv.people > 0 // 22
  
  adv.cost > 0
  adv.client = adv.actRes.client // 23
  adv.client = adv.roomRes.client // 23
  // post cond
  adventureExists[t', adv]
  adv.state.t' = InitialState
  // post/frame
  reserveActivity[t, t', adv.actRes]
  reserveRooms[t, t', adv.roomRes]
  // frame cond
  noAccountsChangeExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', adv.actRes.offer]
  noAdventureCreatedExcept[t, t', adv]
  noAdvStateChangeExcept[t, t', adv]
}

// Asserts ---------------------------------------------------------------------
// openAccount
assert canOpenAnyUnopenedAccount {
  all t: Time | no acc: Account | let t' = t.next |
    accountIsOpen[t, acc] && openAccount[t, t', acc]
}
check canOpenAnyUnopenedAccount for 2 but 1 Account // 1

assert cannotOpenAccountAgain {
  all t, t', t'': Time, acc: Account |
    openAccount[t, t', acc] && openAccount[t', t'', acc] => t'' = t'
}
check cannotOpenAccountAgain // 2

assert eachOpenAccountBelongsToExactlyOneClient {
  all t: Time, acc: Account |
    accountIsOpen[t, acc] => one acc.client
}
check eachOpenAccountBelongsToExactlyOneClient // 3

assert eachOpenAccountBelongsToExactlyOneBank {
  all t: Time, acc: Account |
    accountIsOpen[t, acc] => one acc.bank
}
check eachOpenAccountBelongsToExactlyOneBank // 4

// clientDeposit
assert canOnlyDepositOnOpenAccounts {
  all t: Time, acc: Account, amt: Int | let t' = t.next |
    clientDeposit[t, t', acc, amt] => accountIsOpen[t, acc]
}

check canOnlyDepositOnOpenAccounts // 7

assert balanceIsNeverNegative {
  all t: Time | no acc: Account |
    accountIsOpen[t, acc] && acc.balance.t < 0
}

check balanceIsNeverNegative // 8

assert openAccountsRemainOpen {
  all t: Time, acc: Account, amt: Int | let t' = t.next |
    clientDeposit[t, t', acc, amt] =>
    accountIsOpen[t, acc] && accountIsOpen[t', acc]
}
check openAccountsRemainOpen // 9

// reserveRooms
assert roomResArrivalLessThanDeparture {
  all t: Time, res: AdventureBuilder.roomRes.t |
    lt[res.arrival, res.departure]
}
check roomResArrivalLessThanDeparture for 5 // 13

// makeActivityOffer
assert activityCapacityIsPositive {
  all t: Time, act: AdventureBuilder.offers.t.activity | act.capacity > 0
}
check activityCapacityIsPositive // 15

assert arrivalCantBeBeforeDeparture {
  all t: Time, off: AdventureBuilder.offers.t | lt[off.begin, off.end]
}
check arrivalCantBeBeforeDeparture // 16

assert offerAvailabilityIsInbounds {
  all t: Time, off: AdventureBuilder.offers.t | let avail = off.availability.t |
    (0 <= avail && avail <= off.activity.capacity)
}
check offerAvailabilityIsInbounds // 17

// reserveActivity
assert activityIsForSomePeople {
  all t: Time, res: AdventureBuilder.actRes.t | res.people > 0
}
check activityIsForSomePeople // 18

assert offerAvailChangesUponReserv {
  all t: Time, res: AdventureBuilder.actRes.t |
      let t' = t.next, avail = res.offer.availability.t |
    reserveActivity[t, t', res] =>
    res.offer.availability.t' = minus[avail, res.people]
}
check offerAvailChangesUponReserv // 19

// createAdventure
assert adventureIsForSomePeople {
  all t: Time | no adv: AdventureBuilder.adventures.t |
    adventureExists[t, adv] && adv.people < 1
}
check adventureIsForSomePeople for 5 // 22

assert advClientIsClientOfReservations {
  all t: Time, adv: AdventureBuilder.adventures.t |
    adv.client = adv.roomRes.client && adv.client = adv.actRes.client
}
check advClientIsClientOfReservations for 5 // 23

assert advRoomResAreInSameHotel {
  all t: Time, res: AdventureBuilder.adventures.t.roomRes |
    one h: Hotel | res.room.hotel = h
}
check advRoomResAreInSameHotel for 5 // 24
// Transitions -----------------------------------------------------------------

pred init[t: Time] {
  no AdventureBuilder.(accounts +
                       roomRes +
                       offers +
                       actRes +
                       adventures).t
}

fact traces {
  init [T/first]
  all t: Time - T/last | let t' = t.next |
    some acc: Account, off: ActivityOffer, adv: Adventure, avail, amt: Int {
      openAccount[t, t', acc] or
      clientDeposit[t, t', acc, amt] or
      makeActivityOffer[t, t', off, avail] or
      createAdventure[t, t', adv]
    }
}
