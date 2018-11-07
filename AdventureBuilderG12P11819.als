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
  accounts: Account -> Time
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
//  arrival: one Date,
//  departure: one Date
//}
//
//
//sig ActivityProvider {
//  activities: set Activity
//}
//
//sig Activity {
//  provider: one ActivityProvider,
//  capacity: one Int
//}
//
//sig ActivityOffer {
//  activity: one Activity,
//  begin, end: one Date,
//  availability: Int one -> set Time
//}
//
//sig ActivityReservation {
//  offer: one ActivityOffer,
//  client: one Client,
//  people: one Int
//}
//
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

//pred noOffersChangeExcept[t, t': Time, off: ActivityOffer] {
//  all o: ActivityOffer - off |
//    o.availability.t' = o.availability.t
//}

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
}

//pred makeActivityOffer[t, t': Time, off: ActivityOffer, avail: Int] {
//  // pre cond
//  lt[off.begin, off.end] // 16
//    off.activity.capacity > 0
//    avail >= 0
//    avail <= off.activity.capacity
//    //0 <= avail && avail <= act.capacity // 17
//  // post cond
//  off.availability.t' = avail
//  // frame cond
//  noOpenChangeExcept[t, t', none]
//  noAccountChangeExcept[t, t', none]
//  noOffersChangeExcept[t, t', off]
//}

// Asserts ---------------------------------------------------------------------
// openAccount
assert canOpenAnyUnopenedAccount {
  all t: Time, acc: Account | let t' = t.next |
    openAccount[t, t', acc] iff not accountIsOpen[t, acc]
}
check canOpenAnyUnopenedAccount for 2 but 1 Account // 1

assert cannotOpenAccountAgain {
  all t, t', t'': Time, acc: Account |
    openAccount[t, t', acc] && openAccount[t', t'', acc] => t'' = t'
}
check cannotOpenAccountAgain for 3 but 1 Account // 2

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

check canOnlyDepositOnOpenAccounts for 3 but 1 Account // 7

assert balanceIsNeverNegative {
  all t: Time | no acc: Account |
    accountIsOpen[t, acc] && acc.balance.t < 0
}

check balanceIsNeverNegative for 3 but 1 Account // 8

assert openAccountsRemainOpen {
  all t: Time, acc: Account, amt: Int | let t' = t.next |
    clientDeposit[t, t', acc, amt] =>
    accountIsOpen[t, acc] && accountIsOpen[t', acc]
}
check openAccountsRemainOpen for 3 but 1 Account // 9

// makeActivityOffer
//assert activityCapacityIsPositive {
//  all act: Activity | act.capacity >= 0
//}
//check activityCapacityIsPositive // 15
//
//assert arrivalCantBeBeforeDeparture {
//  all off: ActivityOffer |
//    lt[off.begin, off.end]
//}
//check arrivalCantBeBeforeDeparture // 16
//
//assert offerAvailabilityIsInbounds {
//  all t: Time, off: ActivityOffer | let avail = off.availability.t |
//    (0 <= avail && avail <= off.activity.capacity)
//}
//check offerAvailabilityIsInbounds // 17
// Transitions -----------------------------------------------------------------

pred init[t: Time] {
  no AdventureBuilder.accounts.t
}

fact traces {
  init [T /first]
  all t: Time - T /last | let t' = t.next |
    some acc: Account, /*off: ActivityOffer, avail,*/ amt: Int {
      openAccount[t, t', acc] or
      clientDeposit[t, t', acc, amt] //or
      //makeActivityOffer[t, t', off, avail]
    }
}
