open util/ordering[Time] as to

abstract sig Information {}
sig Key extends Information {}
sig Encrypted extends Information{}

one sig Global{
	encryption: Encrypted -> Key -> Key
	//encryption[encrypted][key] to get value
}

abstract sig Actor{
	info: Information -> Time	
}

one sig KDC extends Actor {}
one sig TGS extends Actor {}
//one sig Service
abstract sig Client extends Actor {}
one sig User extends Client {}
//one sig Malicious extends Client{}

