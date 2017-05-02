
open util/ordering[Time] as to

sig Time {}

abstract sig Information {}
sig Key extends Information {}
sig Encrypted extends Information {}
abstract sig Name extends Information {}

one sig Global{
	encryption: Encrypted -> Key -> Information,
	initial: Actor -> set Information
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
	TGS.info.t = Ktgs + Ks + Kas
	Service.info.t = Ks + S
	Global.initial = ((Client -> (A + Ka)) + (KDC -> (Ka + Ktgs + Kat)) 
		+ (TGS -> (Ktgs + Ks + Kas)) + (Service -> (Ks + S + Kas)))
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
	//Encrypted object can only point to at most one unencrypted object
	all enc: Encrypted | (one Global.encryption[enc] and  some en : Encrypt | en.e = enc)
}

pred actorChange[a : Actor, t : Time, t' : Time] {
	all ac : (Actor - a) |
		ac.info.t = ac.info.t'
	//(Actor - a).info.t = (Actor - a).info.t'
}

sig Message extends Event {
	from: Client,
	to: Actor,
	inf: set Information
} {
	some inf
	inf in from.info.pre
	inf not in to.info.pre
	to.info.post = to.info.pre + inf + Global.encryption[inf][to.info.pre]
	//from.info.post = from.info.pre
	actorChange[to, pre, post]
}

sig Reply extends Event {
	from: Actor,
	to: Client,
	inf: set Information,
	message: one Message
} {
	some inf
	inf in from.info.pre
	inf not in to.info.pre
	to.info.post = to.info.pre + inf + Global.encryption[inf][to.info.pre]
	from.info.post = from.info.pre & Global.initial[from] // Forget learned values, except Service can learn Kas
	actorChange[(to + from), pre, post]
}

fact noInterruption {
	all m : Message | one r : Reply | {
		gt[r.pre, m.pre]
		m.to = r.from
		r.to = m.from
		r.message = m
		no m2 : Message | {
			gt[m2.pre, m.pre]
			lt[m2.pre, r.pre]
			m2.to = m.to || m2.from = m.from
		}
	}
}

fact noUnsolicitied {
	Reply.message = Message
	#Reply = #Message
}

sig Encrypt extends Event {
	a : Actor,
	i : Information,
	k : Key,
	e : Encrypted
} {
	i in a.info.pre
	//i not in Encrypted // no double encryptions, for speed (maybe remove)
	k in a.info.pre
	//e not in a.info.pre // To remove pointless redundancy
	a.info.post = a.info.pre + e
	(e -> k -> i) in Global.encryption// = Global.encryption + (e -> k -> i)
	actorChange[a, pre, post]
}

//sig Decrypt extends Event {
//	a : Actor,
//	i : Information,
//	k : Key,
//	e : Encrypted
//} {
//	k in a.info.pre
//	e in a.info.pre
//	i not in a.info.pre // remove redundancy
//	a.info.post = a.info.pre + i
//	(e -> k -> i) in Global.encryption
//	oneActorChange[a, pre, post]
//}

fact noUnencrypted{ //naive, probably shouldn't be final
	all m : Message | m.inf in Encrypted
	all r : Reply | r.inf in Encrypted
}

// If not included, then Service will send key to KDC or TGS, which
// would defeat the purpose of the system.
//fact onlyUsertoService {
//	all m : Message | (m.from = Service) implies (m.to in Client)
//	all m : Message | (m.to = Service) implies (m.from in Client)
//}

fact noSecretKeysLost {
	no Client.info.Time & (Ktgs + Ks)
}

fact identityProven {
	all r : Reply | 
		//some ((Ka + Kas + Kat) & (Global.encryption[r.inf].Information 
		//	+ Global.encryption[r.inf][Key])) implies 
		A in r.from.info.(r.pre)//Global.encryption[r.inf][r.from.info.(r.pre)]
}

pred canAccess {
	(S + Kas) in UserA.info.last
	Kas in Service.info.last
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
