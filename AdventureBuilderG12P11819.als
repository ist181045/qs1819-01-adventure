/**
 * Software Specification 2018-2019 -- G12
 * 67030 - Leo Valente
 * 81045 - Rui Ventura
 * 81728 - Madalena Assembleia
 */
open util/boolean
open util/ordering [Date] as D
open util/ordering [Time] as T

sig Date, Time {}

one sig AdventureBuilder {
  accounts: set Account -> Time,
  offers: set ActivityOffer -> Time,
  actRes: set ActivityReservation -> Time
}

sig Client {}

sig Broker extends Client {}


sig Bank {
  accounts: set Account
}

sig Account {
  bank: one Bank, // 4
  client: one Client, // 3
  balance: Int one -> Time
}

//
//sig Hotel {
//  rooms: set Room
//}
//
//sig Room {
//  hotel: one Hotel,
//  type: one RoomType
//}
//
//abstract sig RoomType {}
//one sig Single, Double extends RoomType {}
//
//sig RoomReservation {
//  room: one Room,
//  client: one Client,
//  arrival, departure: one Date,
//  cancelled: Bool one -> Time
//}
//

sig ActivityProvider {
  activities: set Activity
}

sig Activity {
  provider: one ActivityProvider,
  capacity: one Int
}{
  // HACK: Cheesy way of ensuring activities' cap is positive
  capacity > 0 // 15
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

//
//sig Adventure {
//  client: one Client,
//  people: one Int,
//  broker: one Broker,
//  roomRes: some RoomReservation,
//  actRes: one ActivityReservation,
//  cost: one Int,
//  clientAcc: one Account,
//  brokerAcc: one Account,
//  state: one AdventureState
//}
//
//abstract sig AdventureState {}
//one sig Initial, Payed, Confirmed extends AdventureState {}
//
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

pred accountIsOpen[t: Time, acc: Account] {
  acc in AdventureBuilder.accounts.t
}

pred noOpenChangeExcept[t, t': Time, acc: Account] {
  AdventureBuilder.accounts.t' = AdventureBuilder.accounts.t + acc
}

pred noAccountChangeExcept[t, t': Time, acc: Account] {
  all a: Account - acc | a.balance.t' = a.balance.t
}

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

pred noActResChangeExcept[t, t': Time, res: ActivityReservation] {
  AdventureBuilder.actRes.t' = AdventureBuilder.actRes.t + res
}

// Helper Ops

pred reserveActivity[t, t': Time, res: ActivityReservation] {
  // pre cond
  t' = t.next
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
  // frame cond
  noOpenChangeExcept[t, t', none]
  noAccountChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', res.offer]
  noActResChangeExcept[t, t', res]
}

// Main Ops

pred openAccount[t, t': Time, acc: Account] {
  // pre cond
  not accountIsOpen[t, acc] // 1
  // post cond
  accountIsOpen[t', acc] // 2
  acc.balance.t' = 0
  // frame cond
  noOpenChangeExcept[t, t', acc]
  noAccountChangeExcept[t, t', acc]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', none]
  noActResChangeExcept[t, t', none]
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
  noOpenChangeExcept[t, t', none] // 9
  noAccountChangeExcept[t, t', acc]
  noOffersChangeExcept[t, t', none]
  noOfferAvailChangeExcept[t, t', none]
  noActResChangeExcept[t, t', none]
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
  noOpenChangeExcept[t, t', none]
  noAccountChangeExcept[t, t', none]
  noOffersChangeExcept[t, t', off]
  noOfferAvailChangeExcept[t, t', off]
  noActResChangeExcept[t, t', none]
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

// makeActivityOffer
assert activityCapacityIsPositive {
  all act: Activity | act.capacity > 0
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

// Transitions -----------------------------------------------------------------

pred init[t: Time] {
  no AdventureBuilder.(accounts +
                       offers +
                       actRes).t
}

fact traces {
  init [T/first]
  all t: Time - T/last | let t' = t.next |
    some acc: Account, off: ActivityOffer, actRes: ActivityReservation, avail, amt: Int {
      openAccount[t, t', acc] or
      clientDeposit[t, t', acc, amt] or
      makeActivityOffer[t, t', off, avail] or
      reserveActivity[t, t', actRes]
    }
}
