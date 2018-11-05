/**
 * Software Specification 2018-2019 -- G12
 * 67030 - Leo Valente
 * 81045 - Rui Ventura
 * 81728 - Madalena Assembleia
 */
open util/ordering [Date] as D
open util/ordering [Time] as T

sig Date, Time {}

sig Client {}

sig Broker extends Client {}


sig Bank {
  accounts: set Account
}

sig Account {
  bank: lone Bank,
  client: lone Client,
  balance: Int lone -> set Time,
  isOpen: set Time
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
//  activites: set Activity
//}
//
//sig Activity {
//  provider: one ActivityProvider,
//  capacity: one Int
//}
//
//sig ActivityOffer {
//  activity: one Activity,
//  begin: one Date,
//  end: one Date,
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


pred init[t: Time] {
}

pred noOpenChangeExcept[t, t': Time] {
  isOpen.t = isOpen.t'
}

pred noAccountChangeExcept[t, t': Time, acc: Account] {
  all a: Account - acc | a in isOpen.t => a in isOpen.t'
}

pred openAccount[t, t': Time, acc: Account, c: Client, b: Bank] {
  // pre cond
  acc not in isOpen.t // 1, 2
  // post cond
  acc.balance.t' = 0
  c = acc.client
  b = acc.bank
  acc in b.accounts
  acc in isOpen.t'
  // frame cond
  noAccountChangeExcept[t, t', acc]
}

fact trans {
  init [T /first]
  all t: Time - T /last | let t' = t.next |
    some acc: Account, c: Client, b: Bank {
      openAccount[t, t', acc, c, b]
  }
}

run {} for 4
