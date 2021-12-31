open util/ordering[Nat]

// Natural numbers
sig Nat {}

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
	pid: Proposer,
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

abstract sig CallTransition {
	op: Op,
	pre: State,
	sent: set Message,
	post: State
}

sig WriteTransition extends CallTransition {} {
	Write in op
	pre in ProposerState
	post in ProposerState

}