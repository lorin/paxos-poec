open util/natural
open util/relation

// values
sig Val {}

abstract sig Role {
	events: set Transition,
	eor: Transition->Transition

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
	// We don't have to worry about the natural part because everything's finite
	relation/totalOrder[eo, Transition]
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
	/*
	role in Proposer
	op in Write
	pre+post in ProposerState
	post.proposer = pre.proposer
	(ProposerState <: post).value = op.val

	let s = (sent <: Prepare) | {
		one s
		s.pid = pre.proposer
		s.n = pre.proposer.n
	}
	*/
}

sig ReadTransition extends CallTransition {
	rval: lone Val
} {
	role in Learner
	op in Read
	some pre & LearnerState
	post = pre
	rval = {v: Val | gte[#pre.votes.v, next[div[#Acceptor, 2]]] }
}


abstract sig ReceiveTransition extends Transition {
	msg: Message
}

sig PromiseTransition extends ReceiveTransition {} {
	role in Proposer
	msg in Promise
	pre+post in ProposerState
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
	natural/gt[msg.n, pre.promised] => {
		let snt = Promise <: sent | {
			one snt
			snt.aid = pre.acceptor
			snt.ppid = msg.pid
			some v => {
				one Proposal <: snt.p
				snt.p.n = pre.promised
			}
		}
	}
}

sig AcceptTransition extends ReceiveTransition {} {
	role in Acceptor
	let accept = Accept <: msg |  {
		some accept
		pre+post in AcceptorState
		post.acceptor = pre.acceptor
		pre.acceptor in accept.ids => {
			natural/gte[accept.p.n, pre.promised] => {
				post.accepted = accept.p
				some accepted : Accepted | {
					sent = accepted
					accepted.aid = pre.acceptor
					accepted.p = accept.p
				}
			}
		}
	}
}

sig AcceptedTransition extends ReceiveTransition {} {
	role in Learner
	let accepted = Accepted <: msg | {
		some accepted
		some pre & LearnerState
		some post & LearnerState
		post.votes = pre.votes ++ accepted.aid->accepted.p.v
	}

}


abstract sig InitTransition extends Transition {} {
	no pre
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


run {
some WriteTransition
}

/*
run {
	// some Proposer
	// some Acceptor
	// all r: Role | some r.events
	//some ReadTransition
	some WriteTransition
} for 7 but 1 Acceptor, 1 Proposer, 1 ProposerInitTransition, 1 LearnerInitTransition, 1 AcceptorInitTransition, 1 ReadTransition, 1 WriteTransition, 1 Val, 1 Proposal, 1 Prepare, 1 Promise, 1 Accept, 1 Accepted
*/
