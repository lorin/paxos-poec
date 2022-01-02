module impl

open util/natural
open util/relation

// values
sig Val {}

abstract sig Role {
	events: set Transition,
	eor: Transition->set Transition

} {
	some events
	events = role.this
	eor = events <: eo :> events

	all e: events |
		(no e.pre and no predd[e, eor]) or predd[e, eor].post = e.pre

	// any two calls must always have a return between them
	all disj e1, e2: events & CallTransition |
		some e3: events | {
			e1->e3 in eor
			e3->e2 in eor
			some e3.rval
		}
}


sig Proposer extends Role {
	n: Natural
} {
	// We disallow zero so that we can initialize the acceptors to zero
	no n & natural/Zero
}

fact "all proposers use different proposal numbers" {
	no disj p1,p2: Proposer | p1.n = p2.n
}

sig Acceptor extends Role {}

// We'll assume one learner for simplicitly
one sig Learner extends Role {}

sig Proposal {
	n: Natural,
	v: Val
}

abstract sig Message {}

sig Prepare extends Message {
	pid: Proposer,
	n: Natural
}

sig Promise extends Message {
	aid: Acceptor,
	ppid: Proposer,
	p: lone Proposal
}

sig Accept extends Message {
	ids: set Acceptor,
	p: Proposal
}

sig Accepted extends Message {
	aid: Acceptor,
	p: Proposal
}

abstract sig Op {}
sig Write extends Op {
	val: Val
}

one sig Read extends Op {}

abstract sig State {}

sig ProposerState extends State {
	proposer: Proposer,
	value: lone Val,
	responses: set Acceptor
}

sig AcceptorState extends State {
	acceptor: Acceptor,
	accepted: lone Proposal,
	promised: Natural
}

sig LearnerState extends State {
	votes: Acceptor -> Val
}

abstract sig Transition {
	pre: lone State,
	post: State,
	sent: set Message,
	eo: set Transition,
	role: Role,
	del: set Transition,
	next: lone Transition,
	nextr: lone Transition,
	rval: lone Val+OK
} {
	next = { e: Transition | this->e in @eo and no ep: Transition | {
		this->ep in @eo
		ep->e in @eo
	}}
	nextr = {e : role.events | this->e in @eo and no ep: role.events | {
		this->ep in @eo
		ep->e in @eo
	}}}


// p87
fact "eo is an enumeration" {
	// an enumeration is a natural total ordering
	// but we acutally don't want total, since we don't want reflexive
	all disj e1,e2: Transition | (e1->e2) in eo or (e2->e1) in eo
	relation/acyclic[eo, Transition]

}

fact "delivery properties" {
	// del is a binary, injective relation
	relation/injective[del, Transition]
	// that satisfies the following property:
	all s, r : Transition | (s->r in del) => {
		s->r in next
		some r.msg
		r.msg in s.sent
	}

}


abstract sig CallTransition extends Transition{
	op: Op
}

sig WriteTransition extends CallTransition {
} {
	role in Proposer
	op in Write
	pre+post in ProposerState
	post.proposer = pre.proposer
	post.value in op.val
	sent = {s : Prepare | s.pid=pre.proposer and s.n=pre.proposer.n}
	one sent
	no rval
}

// compare the majority required given a total number of somethings
fun majority[n: Int] : Int {
	next[div[n, 2]]
}

sig ReadTransition extends CallTransition {} {
	no sent
	role in Learner
	op in Read
	some pre & LearnerState
	post = pre
	rval = {v: Val | gte[#pre.votes.v, majority[#Acceptor]]}
}


abstract sig ReceiveTransition extends Transition {
	msg: Message
}

fact "All messages that exist must have been sent" {
	Message in Transition.sent
}

sig PromiseTransition extends ReceiveTransition {} {
	role in Proposer
	msg in Promise
	some pre & ProposerState
	some post & ProposerState
	post.proposer = pre.proposer
	let promise = Promise <: msg | {
		promise.ppid=pre.proposer
		post.responses = pre.responses + promise.aid

		// If the acceptor has already accepted a proposal, use the value of that proposal
		let proposal = promise.p | {
			some proposal implies {
				post.value = proposal.v
			} else {
			post.value = pre.value
			}
		}

		gte[#post.responses, majority[#Acceptor]] implies {
			rval = OK
			one sent
			some s : Accept <: sent | {
				s.ids = post.responses
				s.p.n = role.n
				s.p.v = post.value
			}
		} else {
			no sent
			no rval
		}
	}
}

sig PrepareTransition extends ReceiveTransition {} {
	role in Acceptor
	msg in Prepare
	pre in AcceptorState
	post in AcceptorState
	post.acceptor = pre.acceptor
	post.promised = natural/max[pre.promised + (Prepare <: msg).n]
	post.accepted = pre.accepted
	no rval

	// We only send if msg.n was greater than what we previously promised
	natural/gt[msg.n, pre.promised] implies {
		one sent
		some snt : Promise <: sent | {
			snt.aid = pre.acceptor
			snt.ppid = msg.pid
			snt.p = pre.accepted
		}
	} else no sent
}

one sig OK {}

sig AcceptTransition extends ReceiveTransition {} {
	role in Acceptor
	no rval
	let accept = Accept <: msg |  {
		some accept
		pre+post in AcceptorState
		post.acceptor = pre.acceptor
		(pre.acceptor in accept.ids and natural/gte[accept.p.n, pre.promised]) implies {
				post.accepted = accept.p
				some accepted : Accepted | {
					sent = accepted
					accepted.aid = pre.acceptor
					accepted.p = accept.p
			}
		} else {
			no sent
		}
	}
}

sig AcceptedTransition extends ReceiveTransition {} {
	role in Learner
	no sent
	no rval
	some pre & LearnerState
	some post & LearnerState
	let accepted = Accepted <: msg | {
		some accepted
		post.votes = pre.votes ++ accepted.aid->accepted.p.v
	}

}


abstract sig InitTransition extends Transition {} {
	no pre
	no sent
	no rval
}

sig ProposerInitTransition extends InitTransition {} {
	role in Proposer
	post.proposer = role
	no post.value
	no post.responses
}

fact "every proposer init transition is associated with a different proposer" {
	no disj p1, p2: ProposerInitTransition | p1.post.proposer = p2.post.proposer
}


sig AcceptorInitTransition extends InitTransition {} {
	role in Acceptor
	post.acceptor = role
	post.promised = natural/Zero
	no post.accepted
}

sig LearnerInitTransition extends InitTransition {} {
	role in Learner
	no post.votes
}

// Predecesor. We can't use "pred" because that means "predicate"
fun predd[t: Transition, r: Transition->Transition] : lone Transition {
	{e : Transition-t | {
		e->t in r
		no f : Transition-(e+t) | {
			e->f in r
			f->t in r
		}
	}
	}
}

// Transport guarantees
fact dontforge {
	all e: ReceiveTransition | some ep : Transition | ep->e in del
}

assert readsAlwaysReturnSameValue {
	all disj r1, r2: ReadTransition | r1.rval = r2.rval

}

// check readsAlwaysReturnSameValue for 11 but 1 Proposer, 1 Acceptor, 2 ReadTransition


run {
	#Acceptor=3
	#Proposer=2
	#WriteTransition=2
	#Write=2
	all disj t1, t2: WriteTransition | no t1.op&t2.op
	all disj w1,w2: Write | no w1.val & w2.val
	some ReadTransition.rval
	// some ProposerInitTransition
	// some AcceptorInitTransition
	// some LearnerInitTransition
	// some WriteTransition
	// some PrepareTransition

	// some Promise
	// some PromiseTransition

	//some Promise
	//some ReadTransition
	// some ProposerState.responses
	// some PromiseTransition
	// some LearnerState.votes
	// some Accept
}  for 17 but 3 Acceptor, 2 Proposer, 1 ReadTransition, 2 WriteTransition, 2 Write
// for 9 but 1 Acceptor, 1 Proposer, 1 ReadTransition, 1 WriteTransition
//for 9 but 1 Acceptor, 1 Proposer, 1 ReadTransition

/*
run {
	some Transition.sent
	some ReceiveTransition
	// some ReadTransition.rval
	// some Proposer
	// some Acceptor
	// all r: Role | some r.events
	// some ReadTransition
	// some WriteTransition
} for 5 // for 9 but 1 Acceptor
*/

