module chapter6/hotel4 --- model in Fig 6.10 with the NonIntervening fact

open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key, Time {} // key combinations (not cards)

sig Room {
	keys: set Key,
	currentKey: keys one -> Time  // current key associated w/ card
	}

fact {
	// each key belongs to at most one room
	Room <: keys in Room lone -> Key // declaration formula, specifies 'keys' is from Room, not Guest
	}

one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time, // last key combination issued
	occupant: (Room -> Guest) -> Time // maps rooms to guests
	}

sig Guest {
	keys: Key -> Time // guest holds keys
	}

fun nextKey [k: Key, ks: set Key]: set Key {
	min [k.nexts & ks] // smallest key in the ordering that follows k in ks
	}

pred init [t: Time] {
	no Guest.keys.t // no guests have keys
	no FrontDesk.occupant.t // no occupants for rooms
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t // locks are synced with front desk (nontrivial in practice)
	}

abstract sig Event { // generic event Sig, events involve guests
	pre, post: Time,
	guest: Guest
	}

abstract sig RoomKeyEvent extends Event { // generic sig for events involving a room and a key (checkout doesn't)
	room: Room,
	key: Key
	}

sig Entry extends RoomKeyEvent { } {
	key in guest.keys.pre // guest currently holds key
	let ck = room.currentKey |
		(key = ck.pre and ck.post = ck.pre) or // key is current key
		(key = nextKey[ck.pre, room.keys] and ck.post = key) // key is successor, and lock changes to reflect that
	currentKey.post = currentKey.pre ++ room->key // currentkey mapping is replaced by mapping to guest's key, even if the same
	}

sig Checkin extends RoomKeyEvent { } {
	keys.post = keys.pre + guest -> key // new key added to guest
	let occ = FrontDesk.occupant {
		no occ.pre [room] // room has no occupant
		occ.post = occ.pre + room -> guest // guest becomes new occupant
		}
	let lk = FrontDesk.lastKey {
		lk.post = lk.pre ++ room -> key // lastkey updated to reflect guest's new key,
							  		    // ++ overrides any key in lk.t which starts with r (no duplicate r -> x keys in lastkey)
		key = nextKey [lk.pre [room], room.keys] // key is the next key for the room
		}
	}

sig Checkout extends Event { } {
	let occ = FrontDesk.occupant {
		some occ.pre.guest // guest is occupying room
		occ.post = occ.pre - Room -> guest // guest is no longer occupying room
		}
	}

fact Traces {
	init [first] // initial condition holds for first time
	all t: Time-last |
		let t' = t.next |
			some e: Event { // for every sequential pair of times, there is an event
				e.pre = t and e.post = t'
				currentKey.t != currentKey.t' => e in Entry // if the key mapping for a room changes, someone must have entered
				occupant.t != occupant.t' => e in Checkin + Checkout // if the occupant changes, someone checked in or out
				(lastKey.t != lastKey.t' or keys.t != keys.t') => e in Checkin // if the front desk key mapping changes,
																			   // or a guest gets a key, someone checked in
			}
	}

assert NoBadEntry {
	all e: Entry |
		let o=FrontDesk.occupant.(e.pre) [e.room] | 
			some o => e.guest in o // if a guest enters a room that is occupied, they must be the occupant
								   // note: guests can still enter unoccupied rooms after checking out, but
								   // this isn't considered a problem
	}

fact NoIntervening {
	all c: Checkin |
		c.post = last // every checkin event is either the last event
		or some e: Entry { // or is immediately followed by an entry event w/ the same room and guest
			e.pre = c.post
			e.room = c.room
			e.guest = c.guest
		}
	}

// After adding the NoIntervening fact,
// this command no longer generates a counterexample
check NoBadEntry for 5 but 3 Room, 3 Guest, 9 Time, 8 Event
