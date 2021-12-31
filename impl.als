open util/ordering[Nat]

// Natural numbers
sig Nat {}

sig Zero extends Nat {}

fact "zero is the first natural number" {
	first = Zero
}


// values
sig Val {}

// Undef is a special value
one sig Undef extends Val {}

abstract sig Role {}

// We're not going to explicitly model the ids,
// because we can use the objects themselves
sig Proposer extends Role {
	n: Nat
}

sig Acceptor extends Role {}

// We'll assume one learner for simplicitly
one sig Learner {}

sig Proposal {
	n: Nat,
	v: Val
}

abstract sig Message {}

sig Prepare extends Message {
	pid: Proposer,
	n: Nat
}

sig Promise extends Message {
	aid: Acceptor,
	ppid: Proposer,
	p: Proposal
}

sig Accept extends Message {
	ids: set Acceptor,
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
	num: Nat,
	value: Val,
	responses: set Acceptor
}

sig AcceptorState extends State {
	promised: Nat,
	v: Val
}

sig LearnerState extends State {
	acceptors: Nat->set Acceptor,
	value: Val
}

abstract sig Transition {
	pre: State,
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
			post.num = ((proposal.n = Zero) implies pre.num else proposal.n)
			(Proposer <: post).value = ((proposal.n = Zero) implies (Proposer <: pre).value else proposal.v)
		}
	}
}

sig PrepareTransition extends ReceiveTransition {}
sig AcceptTransition extends ReceiveTransition {}
sig AcceptedTransition extends ReceiveTransition {}




run { some ReadTransition }
