open util/ordering[Time] as to

abstract sig Information {}
sig Key extends Information {}
sig Encrypted extends Information{}
abstract sig Name extends extends Information

one sig Global{
	encryption: Encrypted -> Key -> Information
	//encryption[encrypted][key] to get value
}

abstract sig Actor{
	info: Information -> Time	
}

one sig KDC extends Actor {}
one sig TGS extends Actor {}
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
	Client.info.t = UserName + Ka
	KDC.info.t = Ka + Ktgs + Kat
	TGS.info.t = Ktgs + Ks
	Service.info.t = Ks + S
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
	all e: Encypted |  lone Global.encypted[e]
}

sig Message extends Event {
	from: Actor
	to: Actor
	info: set INformation
} {
}



