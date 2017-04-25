open util/ordering[State]

sig Key {}
sig Information {}

abstract sig Actor{
}

one sig KDC extends Actor {}
one sig TGS extends Actor {}
one sig Service
abstract sig Client extends Actor {}
one sig User extends Client {}
//one sig Malicious extends Client{}

sig State {
    	entity: Actor
	keys: set Key
	info: set Information
}

abstract sig Event {
    pre, post : State
}


/* For every state, there is one event to get from it to the next */
fact transitions {
    all s: State - last |
        let s' = s.next |
            one e: Event | e.pre = s and e.post = s'
}


/*
A message is an event
*/
sig Message extends Event {
	from: Actor
 }
{
	pre.keys in post.keys
	pre.information in post.information

}


/
