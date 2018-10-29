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
  bank: one Bank,
  client: one Client,
  balance: Int one -> set Time
}


sig Hotel {
  rooms: set Room
}

sig Room {
  hotel: one Hotel,
  type: one RoomType
}

abstract sig RoomType {}
one sig Single, Double extends RoomType {}

sig RoomReservation {
  room: one Room,
  client: one Client,
  arrival: one Date,
  departure: one Date
}


sig ActivityProvider {
  activites: set Activity
}

sig Activity {
  provider: one ActivityProvider,
  capacity: one Int
}

sig ActivityOffer {
  activity: one Activity,
  begin: one Date,
  end: one Date,
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
  roomRes: one RoomReservation,
  actRes: one ActivityReservation,
  cost: one Int,
  clientAcc: one Account,
  brokerAcc: one Account,
  state: one AdventureState
}

abstract sig AdventureState {}
one sig InitialState, PayedState, ConfirmedState {}

sig Invoice {
  client: one Client,
  type: one PurchaseType,
  amount: one Int,
  tax: one Int // ????
}

abstract sig PurchaseType {}
one sig Leisure, Business extends PurchaseType {}
