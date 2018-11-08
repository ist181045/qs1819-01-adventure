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
  adventures: set Adventure -> Time,
  invoices: set Invoice -> Time
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

fact { bank = ~accounts } // 4


sig Hotel {
  rooms: set Room // 10
}

sig Room {
  hotel: one Hotel,
  type: one RoomType // 12
}

fact { hotel = ~rooms } // 11, 24

abstract sig RoomType {}
one sig Single, Double extends RoomType {}

sig RoomReservation {
  room: one Room,
  client: one Client,
  arrival, departure: one Date
}{
  lt[arrival, departure] // 13
}


sig ActivityProvider {
  activities: some Activity
}

sig Activity {
  provider: one ActivityProvider,
  capacity: one Int
}{
  capacity > 0 // 15
}

fact { provider = ~activities }

sig ActivityOffer {
  activity: one Activity,
  begin, end: one Date,
  availability: Int one -> set Time
}{
  lt[begin, end] // 16
}

sig ActivityReservation {
  offer: one ActivityOffer,
  client: one Client,
  people: one Int
}{
  people > 0 // 18
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
}{
  people > 0 // 22
  cost > 0
  clientAcc.client = client // 27
  brokerAcc.client = broker // 28
  client in Client - Broker
}

abstract sig AdventureState {}
one sig InitialState, PayedState, ConfirmedState, CancelledState extends AdventureState {}

sig Invoice {
  client: one Client,
  type: one PurchaseType,
  amount: one Int,
  tax: one Int
}

abstract sig PurchaseType {}
one sig Leisure, Business extends PurchaseType {}


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

  lt[a, d'] && gt[d, a']
  //// a  d/a' d' or a' d'/a  d
  //// |---|---|     |----|---|
  //a' = d || d' = a ||
  //// a/a' d  or  a   a'  d
  ////  |---|      |---|---|
  //gte[a', a] && lt[a', d] ||
  //// a   d'  d  or a  d/d'
  //// |---|---|     |---|
  //gt[d', a] && lte[d', d] ||
  //// a'  a   d   d'
  //// |---|---|---|
  //lt[a', a] && lt[d, d']
}
pred roomResConflict[r, r': RoomReservation] {
  let a = r.arrival, a' = r'.arrival, d = r.departure, d' = r'.departure |
    r != r' && r.room = r'.room && datesConflict[a, a', d, d']
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

// invoices
pred invoiceExists[t: Time, inv: Invoice] {
  inv in AdventureBuilder.invoices.t
}

pred noInvoicesAppearExcept[t, t': Time, inv: Invoice] {
  AdventureBuilder.invoices.t' = AdventureBuilder.invoices.t + inv
}

pred noInvoicesDisappearExcept[t, t': Time, inv: Invoice] {
  AdventureBuilder.invoices.t' = AdventureBuilder.invoices.t - inv
}

// Secondary Ops

pred deposit[t, t': Time, acc: Account, amt: Int] {
  let result = plus[acc.balance.t, amt] |
  // pre cond
    result > 0 && // 8
  // post cond
    acc.balance.t' = result
}

pred reserveActivity[t, t': Time, res: ActivityReservation] {
  // pre cond
  not activityResExists[t, res]
  offerExists[t, res.offer]
  // post cond
  activityResExists[t', res]
  let avail = res.offer.availability.t,
      result = minus[avail, res.people] { // 19
    result >= 0
    res.offer.availability.t' = result
  }
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
  noActResCancelledExcept[t, t', res] // 30
}

pred reserveRooms[t, t': Time, res: RoomReservation] {
  // pre cond
  not roomResExists[t, res]
  // all r: res, r': { r'': RoomReservation | roomResExists[t, r''] } |
  //   not roomResConflict[r, r'] // 14
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

pred makeInvoice[t, t': Time, inv: Invoice, adv: Adventure] {
  // pre cond
  not invoiceExists[t, inv]
  // post cond
  inv.type = Leisure
  inv.client = adv.client
  inv.amount = adv.cost
  inv.tax > 0
  invoiceExists[t', inv]
}

pred cancelInvoice[t, t': Time, inv: Invoice] {
  // pre cond
  invoiceExists[t, inv]
  // pre cond
  not invoiceExists[t', inv]
}

// Main Ops

pred openAccount[t, t': Time, acc: Account] {
  // pre cond
  not accountIsOpen[t, acc] // 1
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
  noInvoicesAppearExcept[t, t', none]
}

pred clientDeposit[t, t': Time, acc: Account, amt: Int] {
  // pre cond
  accountIsOpen[t, acc] // 7
  // post/frame cond
  deposit[t, t', acc, amt]
  // frame cond
  noAccountsOpenExcept[t, t', none] // 9
  noAccBalanceChangeExcept[t, t', acc]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', none]
  noRoomResMadeExcept[t, t', none]
  noActResMadeExcept[t, t', none]
  noAdventureCreatedExcept[t, t', none]
  noAdvStateChangeExcept[t, t', none]
  noInvoicesAppearExcept[t, t', none]
}

pred makeActivityOffer[t, t': Time, off: ActivityOffer, avail: Int] {
  // pre cond
  not offerExists[t, off]
  0 <= avail && avail <= off.activity.capacity // 17
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
  noInvoicesAppearExcept[t, t', none]
}

fun residentsForReservation[r: RoomReservation]: Int {
  plus[#(r -> r.(room.type :> Single)),
       mul[2, #(r -> r.(room.type :> Double))]]
}

pred createAdventure[t, t': Time, adv: Adventure] {
  // pre cond
  not adventureExists[t, adv]
  accountIsOpen[t, adv.brokerAcc]
  accountIsOpen[t, adv.clientAcc]
  offerExists[t, adv.actRes.offer]
  adv.client = adv.actRes.client // 23
  adv.client = adv.roomRes.client // 23
  let res = adv.roomRes |
      adv.people = adv.actRes.people &&
      adv.people = residentsForReservation[res] // 25
  // post cond
  adventureExists[t', adv]
  adv.state.t' = InitialState
  // frame cond
  noAccountsOpenExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', none] // 20: also a frame cond of ops that don't
                                    //     affect offers (unlike makeActivityOffer)
  noOfferAvailChangeExcept[t, t', adv.actRes.offer]
  noRoomResMadeExcept[t, t', none]
  noActResMadeExcept[t, t', none]
  noAdventureCreatedExcept[t, t', adv]
  noAdvStateChangeExcept[t, t', adv]
  noInvoicesAppearExcept[t, t', none]
}

pred payAdventure[t, t': Time, adv: Adventure, inv: Invoice] {
  // pre cond
  adventureExists[t, adv] // 26
  adv.state.t = InitialState // 31
  // pre/frame cond
  deposit[t, t', adv.clientAcc, negate[plus[adv.cost, inv.tax]]]
  deposit[t, t', adv.brokerAcc, adv.cost]
  // post cond
  adv.state.t' = PayedState
  // post/frame cond
  makeInvoice[t, t', inv, adv] // 33
  reserveActivity[t, t', adv.actRes]
  reserveRooms[t, t', adv.roomRes]
  // frame cond
  noAccountsOpenExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', adv.(clientAcc+brokerAcc)]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', adv.actRes.offer]
  noAdventureCreatedExcept[t, t', none]
  noAdvStateChangeExcept[t, t', adv]
  noInvoicesAppearExcept[t, t', inv]
}

pred cancelAdventure[t, t': Time, adv: Adventure, inv: Invoice] {
  // pre cond
  adventureExists[t, adv]
  adv.state.t = PayedState // 29
  inv.client = adv.clientAcc.client
  inv.type = Leisure
  inv.amount = adv.cost
    // post/frame cond
  deposit[t, t', adv.clientAcc, plus[inv.amount, inv.tax]]
  deposit[t, t', adv.brokerAcc, negate[inv.amount]]
  cancelInvoice[t, t', inv]
    // frame cond
    noInvoicesDisappearExcept[t, t', inv]
  // post/frame cond
  cancelActivityReservation[t, t', adv.actRes]
  cancelRoomReservations[t, t', adv.roomRes]
  // post cond
  not adventureExists[t', adv]
  adv.state.t' = CancelledState
  // frame cond
  noAccountsOpenExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', adv.(clientAcc+brokerAcc)]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', adv.actRes.offer]
  noAdventureCancelledExcept[t, t', adv]
  noAdvStateChangeExcept[t, t', adv]
}

pred confirmAdventure[t, t': Time, adv: Adventure] {
  // pre cond
  adventureExists[t, adv]
  adv.state.t = PayedState // 32
  // post cond
  adv.state.t' = ConfirmedState
  // frame cond
  noAccountsOpenExcept[t, t', none]
  noAccBalanceChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', none]
  noAdventureCreatedExcept[t, t', none]
  noAdvStateChangeExcept[t, t', adv]
  noInvoicesAppearExcept[t, t', none]
}

//TODO: makeAnnualTaxRed

// Asserts ---------------------------------------------------------------------
assert canOpenAnyUnopenedAccount {
  // if an account can be opened, it must have been closed
  all t, t', t'': Time, acc: Account |
    lte[t, t'] && openAccount[t', t'', acc] =>
    not accountIsOpen[t, acc]
}
check canOpenAnyUnopenedAccount // 1

assert cannotOpenAccountAgain {
  all disj t, t', t'': Time | no acc: Account |
    lte[t, t'] &&
    accountIsOpen[t, acc] && openAccount[t', t'', acc]
}
check cannotOpenAccountAgain // 2

assert eachOpenAccountBelongsToExactlyOneBank {
  all t: Time, acc: Account, bk, bk': Bank |
    accountIsOpen[t, acc] && acc in bk.accounts & bk'.accounts =>
    bk = bk'
}
check eachOpenAccountBelongsToExactlyOneBank // 4

// at least one instance after 2 ops shows client w/ > 1 account
run openAccount for 3 but exactly 2 Account, exactly 2 Client // 5

// If scope goes under 3, on instance will be found because deposit can
// only occur if an account has been opened
run clientDeposit for 3 but 2 Account // 7

assert balanceIsNeverNegative {
  all t: Time, acc: Account | accountIsOpen[t, acc] => acc.balance.t >= 0
}
check balanceIsNeverNegative // 8

assert openAccountsRemainOpen {
  all t, t': Time, acc: Account |
    lt[t, t'] && accountIsOpen[t, acc] => accountIsOpen[t', acc]
}
check openAccountsRemainOpen for 8 // 9

pred hotelsHaveSomeRooms { all h: Hotel | #h.rooms > 1 }
// shows multiple hotels can have more than 1 room
run hotelsHaveSomeRooms for 1 but exactly 1 Hotel, exactly 3 Room // 10

assert eachRoomBelongsToExactlyOneHotel {
  all r: Room | no disj h, h': Hotel | r in h.rooms & h'.rooms
}
check eachRoomBelongsToExactlyOneHotel // 11

//TODO 14: Room resrvations for the same room must not overlap
assert roomResForSameRoomDontOverlap {
  all t: Time | no disj r, r': RoomReservation |
      let a = r.arrival, a' = r'.arrival, d = r.departure, d' = r'.departure |
    roomResExists[t, r] && roomResExists[t, r'] &&
    r.room = r'.room && datesConflict[a, a', d, d']
}
check roomResForSameRoomDontOverlap for 7 // 14

assert offerAvailabilityIsInbounds {
  all t: Time, off: { _: ActivityOffer | offerExists[t, _] } |
      let avail = off.availability.t, cap = off.activity.capacity |
    0 <= avail && avail <= cap
}
check offerAvailabilityIsInbounds // 17

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

assert advClientIsClientOfReservations {
  all t: Time, adv: Adventure, res: adv.roomRes |
    adventureExists[t, adv] =>
    adv.client = res.client &&
    adv.client = adv.actRes.client
}
check advClientIsClientOfReservations for 5 // 23

assert advRoomResAreInSameHotel {
  all t: Time, adv: Adventure | no disj h, h': Hotel |
    adventureExists[t, adv] && adv.roomRes.room in h.rooms & h'.rooms
}
check advRoomResAreInSameHotel for 5 // 24

assert roomResidentsMatchPeopleActivityFor {
  all t: Time, adv: Adventure |
    adventureExists[t, adv] => adv.people = adv.actRes.people &&
                               adv.people = residentsForReservation[adv.roomRes]
}
check roomResidentsMatchPeopleActivityFor for 5 // 25

assert canOnlyPayForExistingAdventures {
  all t, t': Time, adv: Adventure | some inv: Invoice |
    payAdventure[t, t', adv, inv] => adventureExists[t, adv]
}
check canOnlyPayForExistingAdventures for 7 // 26

// cancelAdventure
// takes 7 'times' to pay an adventure. only after that can we cancel
run cancelAdventure for 10 but exactly 1 Adventure // 29

assert actResOnlyDisappearAfterCancel {
  all t, t': Time, adv: Adventure | some inv: Invoice |
    cancelAdventure[t, t', adv, inv] => not activityResExists[t', adv.actRes]
}
check actResOnlyDisappearAfterCancel for 8 // 30

assert payedAdventureWasCreated {
  all t, t': Time, adv: Adventure | some inv: Invoice |
    payAdventure[t, t', adv, inv] => adventureExists[t, adv]
}
check payedAdventureWasCreated for 7 // 31

//TODO 32: If adventure is confirmed, must have been payed for
assert advConfirmedThenMustHaveBeenPayed {
  all t, t': Time, adv: Adventure |
    adventureExists[t, adv] && adv.state.t' = ConfirmedState =>
    adv.state.t = PayedState
}
check advConfirmedThenMustHaveBeenPayed for 8

assert clientsWithInvsHaveSomeOpenAccount {
  all t, t': Time, adv: Adventure | some inv: Invoice |
    payAdventure[t, t', adv, inv] => some accounts.t.client :> inv.client
}
check clientsWithInvsHaveSomeOpenAccount for 8 // 33

//TODO 34: Invoices in AB can disappear...

//TODO 35: If an adventure is payed, then the corresp. invoice is created
assert advPayedThenInvoiceCreated {
  all t, t': Time, adv: Adventure | some inv: Invoice |
    lt[t, t'] && adventureExists[t', adv] &&
    adv.state.t' = PayedState &&
    adv.client = inv.client => invoiceExists[t', inv]
}
check advPayedThenInvoiceCreated for 8
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
                       adventures +
                       invoices).t
}

fact traces {
  init [T/first]
  all t: Time - T/last | let t' = t.next |
    some acc: Account,
         off: ActivityOffer,
         adv: Adventure,
         inv: Invoice,
         avail, amt: Int |
      openAccount[t, t', acc] or
      clientDeposit[t, t', acc, amt] or
      makeActivityOffer[t, t', off, avail] or
      createAdventure[t, t', adv] or
      payAdventure[t, t', adv, inv] or
      confirmAdventure[t, t', adv] or
      cancelAdventure[t, t', adv, inv]
}

// Reachability ----------------------------------------------------------------
run openAccount for 2
run clientDeposit for 3 // at least 1 open account
run makeActivityOffer for 2
run createAdventure for 5 // 2 accs, 1 deposit, 1 offer => 2 + 1 + 1 = 5
run payAdventure for 7 // +1 deposit
run cancelAdventure for 8
run confirmAdventure for 8