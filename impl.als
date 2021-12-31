open util/natural

// values
sig Val {}

abstract sig Role {}

// We're not going to explicitly model the ids,
// because we can use the objects themselves
sig Proposer extends Role {
	n: Natural
}

fact "all proposers use different proposal numbers" {
	no disj p1,p2: Proposer | p1.n = p2.n
}

sig Acceptor extends Role {}

// We'll assume one learner for simplicitly
one sig Learner {}

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

sig Read extends Op {}

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
}

abstract sig CallTransition extends Transition{
	op: Op
}

sig WriteTransition extends CallTransition {
} {
	op in Write
	pre+post in ProposerState
	post.proposer = pre.proposer
	(ProposerState <: post).value = op.val

	let s = (sent <: Prepare) | {
		one s
		s.pid = pre.proposer
		s.n = pre.proposer.n
	}
}

sig ReadTransition extends CallTransition {
	rval: lone Val
} {
	op in Read
	some pre & LearnerState
	post = pre
	rval = {v: Val | gte[#pre.votes.v, next[div[#Acceptor, 2]]] }
}


abstract sig ReceiveTransition extends Transition {
	msg: Message
}

sig PromiseTransition extends ReceiveTransition {} {
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
	no value
	no responses
}

fact "every proposer init transition is associated with a different proposer" {
	no disj p1, p2: ProposerInitTransition | p1.post.proposer = p2.post.proposer
}


sig AcceptorInitTransition extends InitTransition {


}

sig LearnerInitTransition extends InitTransition {}


// Transport guarantees




run { some ReadTransition }
