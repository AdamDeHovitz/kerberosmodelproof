
open util/ordering[Time] as to

sig Time {}

abstract sig Information {}
sig Key extends Information {}
sig Encrypted extends Information {}
abstract sig Name extends Information {}

one sig Global{
	encryption: Encrypted -> Key -> Information -> Time
	//encryption[encrypted][key] to get value
}

abstract sig Actor{
	info: Information -> Time	
}

one sig KDC extends Actor {}
one sig TGS extends Actor {}
one sig Service extends Actor {}
//one sig Service
abstract sig Client extends Actor {}
one sig UserA extends Client {}
//one sig Malicious extends Client{}

one sig A extends Name{}
one sig S extends Name{}
one sig Ka extends Key{}
one sig Ktgs extends Key{}
one sig Ks extends Key{}
one sig Kas extends Key{}
one sig Kat extends Key{}

pred init [t: Time] {
	Client.info.t = A + Ka
	KDC.info.t = Ka + Ktgs + Kat
	TGS.info.t = Ktgs + Ks
	Service.info.t = Ks + S
	no Global.encryption.t
	}

abstract sig Event {
	pre, post: Time
	}

fact Traces {
	init [first]
	all t: Time-last |
		let t' = t.next |
			some e: Event {
				e.pre = t and e.post = t'
			}
	}

fact Encryption {
	//Encypted object can only point to at most one unencypted object
	all e: Encrypted |  lone Global.encryption[e].Time
}

pred oneActorChange[a : Actor, t : Time, t' : Time] {
	all ac : (Actor - a) |
		ac.info.t = ac.info.t'
}

sig Message extends Event {
	from: Actor,
	to: Actor,
	inf: set Information
} {
	some inf
	inf in from.info.pre
	inf not in to.info.pre
	to.info.post = to.info.pre + inf
	oneActorChange[to, pre, post]
	Global.encryption.pre = Global.encryption.post
}

sig Encrypt extends Event {
	a : Actor,
	i : Information,
	k : Key,
	e : Encrypted
} {
	i in a.info.pre
	i not in Encrypted // no double encryptions, for speed (maybe remove)
	k in a.info.pre
	e not in a.info.pre // To remove pointless redundancy
	a.info.post = a.info.pre + e
	Global.encryption.post = Global.encryption.pre + (e -> k -> i)
	oneActorChange[a, pre, post]
}

sig Decrypt extends Event {
	a : Actor,
	i : Information,
	k : Key,
	e : Encrypted
} {
	k in a.info.pre
	e in a.info.pre
	i not in a.info.pre // remove redundancy
	a.info.post = a.info.pre + i
	(e -> k -> i) in Global.encryption.pre
	Global.encryption.post = Global.encryption.pre
	oneActorChange[a, pre, post]
}

fact noUnencrypted{ //naive, probably shouldn't be final
	all m : Message | m.inf in Encrypted
}

pred canAccess {
	S in UserA.info.last
}

run {canAccess} for 13 Event, 14 Time, 14 Information


// NOTE: Maybe make encryption a pre-populated set to speed up 
// solving. Have messages which involve encryption just assume
// that it is decrypted and added to known values on the other end
// and have everyone start with encrypted versions of whatever they
// have

// This would also mean a somewhat complicated operation of adding the
// encrypted versions of everything a user knows to their known set
// when they get a new key
// Potentially, I think this could speed up solving a fair amount
