open util/natural
open util/relation

// values
sig Val {}

abstract sig Role {
	events: set Transition,
	eor: Transition->set Transition

} {
	events = role.this
	eor = events <: eo :> events

	all e: events |
		(no e.pre and no predd[e, eor]) or predd[e, eor].post = e.pre
}


sig Proposer extends Role {
	n: Natural
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
	promised: lone Natural
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
	del: set Transition
}

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
		s->r in eo
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
}

fun majority[n: Int] : Int {
	next[div[n, 2]]
}

sig ReadTransition extends CallTransition {
	rval: lone Val
} {
	no sent
	role in Learner
	op in Read
	some pre & LearnerState
	post = pre
	rval = {v: Val | gte[#pre.votes.v, next[div[#Acceptor, 2]]] }
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

		let proposal = promise.p | {
			some proposal => (ProposerState <: post).value = proposal.v
		}
	}
}

sig PrepareTransition extends ReceiveTransition {} {
	role in Acceptor
	msg in Prepare
	pre+post in AcceptorState
	post.acceptor = pre.acceptor
	post.promised = natural/max[pre.promised + (Prepare <: msg).n]
	post.accepted = pre.accepted
	// We only send if msg.n was greater than what we promised
	natural/gt[msg.n, pre.promised] implies {
		one sent
		some snt : Promise <: sent | {
			snt.aid = pre.acceptor
			snt.ppid = msg.pid
			snt.p = pre.accepted
		}
	} else no sent
}

sig AcceptTransition extends ReceiveTransition {} {
	role in Acceptor
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
		} else no sent
	}
}

sig AcceptedTransition extends ReceiveTransition {} {
	role in Learner
	no sent
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
}

sig ProposerInitTransition extends InitTransition {} {
	role in Proposer
	no value
	no responses
}

fact "every proposer init transition is associated with a different proposer" {
	no disj p1, p2: ProposerInitTransition | p1.post.proposer = p2.post.proposer
}


sig AcceptorInitTransition extends InitTransition {} {
	role in Acceptor
	no accepted
	no promised
}

sig LearnerInitTransition extends InitTransition {} {
	role in Learner
	no votes
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
	some LearnerState.votes
	//some ReadTransition.rval
} for 9 but 1 Acceptor, 1 Proposer, 1 ReadTransition

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

