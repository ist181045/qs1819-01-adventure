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
  bank: one Bank,
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

abstract sig RoomType {}
one sig Single, Double extends RoomType {}

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

pred noAccountsOpenExcept[t, t': Time, acc: Account] {
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
  // a  d/a' d' or a' d'/a  d
  // |---|---|     |----|---|
  a' = d || d' = a ||
  // a/a' d  or  a   a'  d
  //  |---|      |---|---|
  gte[a', a] && lt[a', d] ||
  // a   d'  d  or a  d/d'
  // |---|---|     |---|
  gt[d', a] && lte[d', d] ||
  // a'  a   d   d'
  // |---|---|---|
  lt[a', a] && lt[d, d']
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

//TODO: deposit (needed?)

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
  noAccountsOpenExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', res.offer]
}

pred reserveRooms[t, t': Time, res: RoomReservation] {
  // pre cond
  not roomResExists[t, res]
  all r: res | lt[r.arrival, r.departure] // 13
  no r: res, r': AdventureBuilder.roomRes.t | roomResConflict[r, r'] // 14
  hotel = ~rooms // 24
  // post cond
  roomResExists[t', res]
  // frame cond
  noRoomResMadeExcept[t, t', res]
}

pred cancelRoomReservations[t, t': Time, res: RoomReservation] {
  // pre cond
  roomResExists[t, res]
  // post cond
  not roomResExists[t', res]
  // frame cond
  noRoomResCancelledExcept[t, t', res]
}

//TODO: makeInvoice

//TODO: cancelInvoice

// Main Ops

pred openAccount[t, t': Time, acc: Account] {
  // pre cond
  not accountIsOpen[t, acc] // 1
  bank = ~accounts // 4
  // post cond
  accountIsOpen[t', acc] // 2
  acc.balance.t' = 0
  // frame cond
  noAccountsOpenExcept[t, t', acc]
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
  let result = plus[acc.balance.t, amt] |
  // pre cond
    result > 0 && // 8
  // post cond
    acc.balance.t' = result
  // frame cond
  noAccountsOpenExcept[t, t', none] // 9
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
    0 <= avail && avail <= cap // 17
  // post cond
  offerExists[t', off]
  off.availability.t' = avail
  // frame cond
  noAccountsOpenExcept[t, t', none]
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
  noAccountsOpenExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', adv.actRes.offer]
  noAdventureCreatedExcept[t, t', adv]
  noAdvStateChangeExcept[t, t', adv]
}

//TODO: payAdventure

//TODO: cancelAdventure

//TODO: confirmAdventure

//TODO: makeAnnualTaxRed

// Asserts ---------------------------------------------------------------------
assert canOpenAnyUnopenedAccount {
  // if an account can be opened, it must have been closed
  all t, t', t'': Time, acc: Account |
    lt[t, t'] && openAccount[t', t'', acc] =>
    not accountIsOpen[t, acc]
}
check canOpenAnyUnopenedAccount for 3 // 1

assert cannotOpenAccountAgain {
  all t, t', t'', t''': Time | no acc: Account |
    lt[t, t'] && lt[t', t''] && lt[t'', t'''] &&
    openAccount[t, t', acc] && openAccount[t'', t''', acc]
}
check cannotOpenAccountAgain for 4 // 2

assert eachOpenAccountBelongsToExactlyOneClient {
  all t: Time, acc: Account | no disj cli, cli': Client |
    accountIsOpen[t, acc] && acc.client = cli && acc.client = cli'
}
check eachOpenAccountBelongsToExactlyOneClient for 3 // 3

assert eachOpenAccountBelongsToExactlyOneBank {
  all t: Time, acc: Account, bk, bk': Bank |
    accountIsOpen[t, acc] && acc in bk.accounts & bk'.accounts =>
    bk = bk'
}
check eachOpenAccountBelongsToExactlyOneBank for 3 // 4

//ASK 5: A bank can have several accounts

//ASK 6: A client can have several OPEN accounts

assert canOnlyDepositInOpenAccounts {
  all t, t': Time, acc: Account, amt: Int |
    clientDeposit[t, t', acc, amt] => accountIsOpen[t, acc]
}
check canOnlyDepositInOpenAccounts for 3 // 7

assert balanceIsNeverNegative {
  all t: Time, acc: Account |
    accountIsOpen[t, acc] => acc.balance.t >= 0
}
check balanceIsNeverNegative for 3 // 8

assert openAccountsRemainOpen {
  all t, t': Time, acc: Account |
    lt[t, t'] && accountIsOpen[t, acc] => accountIsOpen[t', acc]
}
check openAccountsRemainOpen // 9

//ASK 10: A hotel can have several rooms

//ASK 11: Each hotel room belongs to exactly one hotel.

//ASK 12: Each hotel room is either single or double

assert roomResArrivalLessThanDeparture {
  all t: Time, res: RoomReservation |
    roomResExists[t, res] => lt[res.arrival, res.departure]
}
check roomResArrivalLessThanDeparture for 5 // 13

//TODO 14: Room resrvations for the same room must not overlap

assert activityCapacityIsPositive {
  // bit of fun w/ set comprehensions
  all t: Time, off: ActivityOffer |
    no act: { act: off.activity | offerExists[t, off] } | act.capacity <= 0
}
check activityCapacityIsPositive // 15

assert arrivalCantBeBeforeDeparture {
  all t: Time, off: ActivityOffer |
    offerExists[t, off] => lt[off.begin, off.end]
}
check arrivalCantBeBeforeDeparture // 16

assert offerAvailabilityIsInbounds {
  all t: Time, off: AdventureBuilder.offers.t |
      let avail = off.availability.t, cap = off.activity.capacity |
    0 <= avail && avail <= cap
}
check offerAvailabilityIsInbounds // 17

assert activityIsForSomePeople {
  all t: Time, res: AdventureBuilder.actRes.t | res.people > 0
}
check activityIsForSomePeople // 18

assert offerAvailChangesUponReserv {
  all t, t': Time, res: AdventureBuilder.actRes.t |
      let avail = res.offer.availability.t |
    reserveActivity[t, t', res] =>
    res.offer.availability.t' = minus[avail, res.people]
}
check offerAvailChangesUponReserv // 19

assert offersRemain {
  all t, t': Time, off: ActivityOffer |
    lt[t, t'] && offerExists[t, off] => offerExists[t', off]
}
check offersRemain // 20

//ASK 21: Each adventure in AB is in one single state

assert adventureIsForSomePeople {
  all t: Time, adv: AdventureBuilder.adventures.t | adv.people > 0
}
check adventureIsForSomePeople for 5 // 22

assert advClientIsClientOfReservations {
  all t: Time, adv: Adventure, res: adv.roomRes |
    adventureExists[t, adv] =>
    adv.client = res.client &&
    adv.client = adv.actRes.client
}
check advClientIsClientOfReservations for 5 // 23

assert advRoomResAreInSameHotel {
  all t: Time, adv: Adventure, res: adv.roomRes, h, h': Hotel |
    adventureExists[t, adv] && res.room in h.rooms & h'.rooms =>
    h = h'
}
check advRoomResAreInSameHotel for 5 // 24

//TODO 25: For each adventure in AB, #people that the room reservs are for
//         matches number of people doing the activity

//TODO 26: It is only possible to pay for existing adventures

//TODO 27: For each adventure in AB, account used for paying belongs to the
//         client the adventure was created for

//TODO 28: For each adventure in AB, the account of the broker who arranged the
//         activity is credited

// cancelAdventure
//TODO 29: Only adventures in PayedState can be cancelled

//TODO 30: Activity reservations in AB cannot disappear, unless an adventure is
//         cancelled

//TODO 31: If adventure is payed, must have been created

//TODO 32: If adventure is confirmed, must have been payed for

//TODO 33: Clients w/ invoices in AB have at least an open bank account

//TODO 34: Invoices in AB can disappear

//TODO 35: If an adventure is payed, then the corresp. invoice is created
//ASK How are these different
//TODO 36: An invoice cannot be created unless payment happened

//TODO 37: Tax on purchase depends on the kind of purchase and the price.
//         tax >= 0 always

//TODO 38: Annual tax red credits exactly one client account for each client
//         w/ invoices in AB

//TODO 39: Balances, on open accounts, cannot decrease w/ annual tax red

//TODO 40: Balances, ..., can increase w/ ...

//TODO 41: Client accounts for which the clients do not have invoices are not
//         affected by tax red
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
    some acc: Account, off: ActivityOffer, adv: Adventure, avail, amt: Int |
      openAccount[t, t', acc] or
      clientDeposit[t, t', acc, amt] or
      makeActivityOffer[t, t', off, avail] or
      createAdventure[t, t', adv]
}

// Reachability ----------------------------------------------------------------
run openAccount for 2
run clientDeposit for 3
run makeActivityOffer for 2
run createAdventure for 5