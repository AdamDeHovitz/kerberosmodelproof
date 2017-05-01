module chapter6/hotel2 --- the final model in Fig 6.7

open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key {} // key combinations (not cards)
sig Time {}

sig Room {
	keys: set Key,
	currentKey: keys one -> Time // current key associated w/ card
	}

fact DisjointKeySets {
	-- each key belongs to at most one room
	Room<:keys   in   Room lone-> Key // declaration formula, specifies 'keys' is from Room, not Guest
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

pred entry [t, t': Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t // guest has to be holding k
	let ck = r.currentKey |
		(k = ck.t and ck.t' = ck.t) or  // key is current key
		(k = nextKey[ck.t, r.keys] and ck.t' = k) // key is successor, so lock changes to that one
	noRoomChangeExcept [t, t', r] // this is the only room that can change
	noGuestChangeExcept [t, t', none] // no guests can change (none argument)
	noFrontDeskChange [t, t'] // Front desk can't change
	}

pred noFrontDeskChange [t, t': Time] {
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	FrontDesk.occupant.t = FrontDesk.occupant.t'
	}

pred noRoomChangeExcept [t, t': Time, rs: set Room] {
	all r: Room - rs | r.currentKey.t = r.currentKey.t'
	}
	
pred noGuestChangeExcept [t, t': Time, gs: set Guest] {
	all g: Guest - gs | g.keys.t = g.keys.t'
	}

pred checkout [t, t': Time, g: Guest] {
	let occ = FrontDesk.occupant {
		some occ.t.g // guest is occupying room
		occ.t' = occ.t - Room ->g // guest is no longer occupying room
		}
	FrontDesk.lastKey.t = FrontDesk.lastKey.t' // front desk key mapping doesn't change
	noRoomChangeExcept [t, t', none] // rooms don't change
	noGuestChangeExcept [t, t', none] // guests don't change
	}

pred checkin [t, t': Time, g: Guest, r: Room, k: Key] {
	g.keys.t' = g.keys.t + k // new key added to guest
	let occ = FrontDesk.occupant {
		no occ.t [r] // room has no occupant
		occ.t' = occ.t + r -> g // guest is now occupant
		}
	let lk = FrontDesk.lastKey {
		lk.t' = lk.t ++ r -> k // lastkey updated to reflect guest's new key,
							   // ++ overrides any key in lk.t which starts with r (no duplicate r -> x keys in lastkey)
		k = nextKey [lk.t [r], r.keys] // guest's new key is equal to the next key for the room
		}
	noRoomChangeExcept [t, t', none] // no rooms change
	noGuestChangeExcept [t, t', g] // only g changes
	}

fact traces {
	init [first] // init holds for the first time
	all t: Time-last | let t' = t.next | // for each sequential pair of times,
		some g: Guest, r: Room, k: Key |
			entry [t, t', g, r, k] // someone enters
			or checkin [t, t', g, r, k] // someone checks in
			or checkout [t, t', g] // or someone checks out
	}

// if a guest checks in, but doesn't use their key (doesn't enter), and then checks out,
// the lock will never be updated with their key. The next guest for that room will receive
// the same key as the first, will be able to enter, and the lock will update. The first guest's
// key still works at this point, even though they are checked out.
fact NoIntervening { 
	all t: Time-last | let t' = t.next, t" = t'.next |
		all g: Guest, r: Room, k: Key |
			checkin [t, t', g, r, k] => (entry [t', t", g, r, k] or no t") // checkin implies immediate entry, or no further actions
	}

assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key |
		let t' = t.next, o = FrontDesk.occupant.t[r] | 
			entry [t, t', g, r, k] and some o => g in o // if a guest enters a room that is occupied, they must be the occupant
														// note: guests can still enter unoccupied rooms after checking out, but
														// this isn't considered a problem
	}

// After adding the NoIntervening fact,
// these commands no longer generate counterexamples
check NoBadEntry for 3 but 2 Room, 2 Guest, 5 Time
check NoBadEntry for 3 but 3 Room, 3 Guest, 7 Time
check NoBadEntry for 5 but 3 Room, 3 Guest, 9 Time
