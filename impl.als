open util/natural

// values
sig Val {}

abstract sig Role {}

// We're not going to explicitly model the ids,
// because we can use the objects themselves
sig Proposer extends Role {
	n: Natural
} {
	// Nobody has proposal number zero
	no n & natural/Zero
}

fact "all proposers use different proposal numbers" {
	no disj p1,p2: Proposer | p1.n = p2.n
}


sig Acceptor extends Role {}

// We'll assume one learner for simplicitly
one sig Learner {
	votes: Acceptor -> Val
}

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
	num: Natural,
	value: Val,
	responses: set Acceptor
}

sig AcceptorState extends State {
	acceptor: Acceptor,
	accepted: lone Proposal,
	promised: Natural
}

sig LearnerState extends State {
	acceptors: Natural->set Acceptor,
	value: Val
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
	post.num = pre.proposer.n
	(ProposerState <: post).value = op.val

	let s = (sent <: Prepare) | {
		one s
		s.pid = pre.proposer
		s.n = post.num
	}
}

sig ReadTransition extends CallTransition {
	rval: Val
} {
	op in Read
	pre+post in LearnerState
	pre=post
	rval=(LearnerState <: pre).value
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
			some proposal => (Proposer <: post).value = proposal.v
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

sig AcceptTransition extends ReceiveTransition {}
sig AcceptedTransition extends ReceiveTransition {}


// Transport guarantees




run { some ReadTransition }
