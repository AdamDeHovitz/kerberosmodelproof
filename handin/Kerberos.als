
open util/ordering[Time] as to

sig Time {}

abstract sig Information {}
sig Key extends Information {}
sig Encrypted extends Information {}
abstract sig Name extends Information {}

one sig Global{
	// Representation of encrypted data. encryption[encrypted value][encryption key] = value.
	encryption: Encrypted -> Key -> Information,
	// Default information held by Actors, used to maintain stateless behaviour (see Readme)
	initial: Actor -> set Information

}

abstract sig Actor{
	// The information known by each actor at a given time, important as Client can learn information
	info: Information -> Time	
}

// Key Distribution Center
one sig KDC extends Actor {}
// Ticket Granting Service
one sig TGS extends Actor {}
// Arbitrary service that user wants to access
one sig Service extends Actor {}

// Representation of a User
one sig Client extends Actor {}

// Client's Identity
one sig A extends Name{}
// Service's Identity
one sig S extends Name{}
// Key based on user password
one sig Ka extends Key{}
// TGS secret key
one sig Ktgs extends Key{}
// Service secret key
one sig Ks extends Key{}
// Session key between client and TGS
one sig Kat extends Key{}
// Session key between client and service
one sig Kas extends Key{}

// Sets up initial known keys, initializes Global.initial
pred init [t: Time] {
	Client.info.t = A + Ka
	KDC.info.t = Ka + Ktgs + Kat
	TGS.info.t = Ktgs + Ks + Kas
	Service.info.t = Ks + S
	// Service doesn't initially know Kas, but will retain it if learned
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
	//Encrypted object can only point to one unencrypted object, 
	// and had to have been encrypted by an Encrypt Event
	all enc: Encrypted | (one Global.encryption[enc] and  some en : Encrypt | en.e = enc)
}

// No actors except those in set a can change over this time step
pred actorChange[a : Actor, t : Time, t' : Time] {
	all ac : (Actor - a) |
		ac.info.t = ac.info.t'
}

sig Message extends Event {
	from: Client,
	to: Actor,
	inf: set Information
} {
	// The message only needs to include at most two things, so this is enforced to reduce solving time
	(#inf = 1) or (#inf = 2)
	inf in from.info.pre
	inf not in to.info.pre
	// Decryption is done automatically. The information learned by the recipient is the encrypted information,
	// along with two levels of decryption. This is to cover the case where one piece of decryptable info contains
	// the key to decrypt the other. This doesn't need to be recursive as there are at most two pieces of data.
	to.info.post = to.info.pre + inf + Global.encryption[inf][to.info.pre] + 
		Global.encryption[inf][Global.encryption[inf][to.info.pre]]
	actorChange[to, pre, post]
}

sig Reply extends Event {
	from: Actor,
	to: Client,
	inf: set Information,
	// The message that this is replying to
	message: one Message
} {
	// The message only needs to include at most two things, so this is enforced to reduce solving time
	(#inf = 1) or (#inf = 2)
	inf in from.info.pre
	inf not in to.info.pre
	// Decryption is done automatically. The information learned by the recipient is the encrypted information,
	// along with two levels of decryption. This is to cover the case where one piece of decryptable info contains
	// the key to decrypt the other. This doesn't need to be recursive as there are at most two pieces of data.
	to.info.post = to.info.pre + inf + Global.encryption[inf][to.info.pre] + 
		Global.encryption[inf][Global.encryption[inf][to.info.pre]]
	// Replying actor forgets its learned values, except for Service, which can learn Kas (as it uses &)
	from.info.post = from.info.pre & Global.initial[from]
	actorChange[(to + from), pre, post]
}

// Requires that no Message/Reply events interrupt an ongoing Message/Reply pair. Encrypt events can occur
// between Message and Reply, though.
fact noInterruption {
	all m : Message | one r : Reply | {
		gt[r.pre, m.pre]
		m.to = r.from
		r.to = m.from
		r.message = m
		// no interrupting Message, don't need to specify that there aren't interrupting Reply events, because 
		// an interrupting Reply would imply a previous interrupting Message
		no m2 : (Message - m) | {
			gt[m2.pre, m.pre]
			lt[m2.pre, r.pre]
		}
	}
}

// Every reply has a message that it is paired with.
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
	k in a.info.pre
	a.info.post = a.info.pre + e
	(e -> k -> i) in Global.encryption
	actorChange[a, pre, post]
	// KDC is the only Actor that can encrypt with Ka
	// This is because Ka is based on the user password, and shouldn't be used for
	// session authentication. Kat should be used instead.
	(k = Ka) implies (a = KDC)
	// Client is the only one who should be creating identification information for themselves
	(i = A) implies (a = Client)
}

fact noUnencrypted{ 
	// All messages are encrypted, except that the Client needs to be able to send
	// an initial identification message prior to receiving any shared keys.
	all m : Message |  {
		(m.from = Client and m.to = KDC) implies m.inf in (Encrypted + A)
		(m.from not = Client or m.to not = KDC) implies m.inf in Encrypted
	}
	// All replies are encrypted.
	all r : Reply | r.inf in Encrypted
}

// Clients should never get access to server-specific secret keys (Ktgs, Ks)
fact noSecretKeysShared {
	no Client.info.Time & (Ktgs + Ks)
}

// In order to reply to a Message, the sender needs to know the identity of the recipient (A).
fact identityProven {
	all r : Reply | 
		A in r.from.info.(r.pre)
}

// Desired end result. Client has communicated with Service (has S),
// and they can communicate in the future using Kas.
pred canAccess {
	(S + Kas) in Client.info.last
	Kas in Service.info.last
}

// Doesn't find a solution for fewer events/time steps. NOTE: For us, this takes 15-30 minutes to run.
run {canAccess} for 13 Event, 14 Time, 14 Information

// Grading reccomendation: To check a model output, we recommend projecting over Time and seeing which
// Event is ocurring at a given time (indicated by $pre). Then, use the Evaluator to determine what occurred during
// that Event. That can be compared with the diagram we provided. Also, keep in mind that decrypting is implied, and
// you can check what Client knows at a given time with Client.info.time. 
