open impl
open util/relation

// return transition for an event
fun ret[e: Event] : Transition {
	let trs = Transition & e.op.(*nextr) |
	{t: trs | some t.rval and no tp: trs | (some tp.rval and t in tp.^nextr)}
}

abstract sig Event {
	op: disj impl/CallTransition,
	rval: lone Val+OK,
	rb: set Event,
	ss: set Event,
	vis: set Event,
	ar: set Event

} {
		rval = ret[this].@rval
}

sig Write extends Event {
	arg: Val
} {
	some WriteTransition & op
	arg = op.op.val
}

sig Read extends Event {
	result: lone Val
} {
	some ReadTransition & op
	result = op.rval
}

fact "returns before relation" {
	all e, ep: Event |
		e->ep in rb <=> {
			some ret[e]
			ret[e]->ep.op in eo
		}
}

fact "same session relation" {
	all e1,e2: Event |
		e1->e2 in ss <=> e1.op.role = e2.op.role
}

fact "visibility relation" {
	acyclic[vis, Event]
}

pred total[r: Event->Event] {
	all disj x,y: Event | x->y in r or y->x in r
}

fact "arbitration relation" {
	totalorder[ar]
}

pred totalorder[r: Event->Event] {
	partialorder[r]
	total[r]
}

pred partialorder[r: Event->Event] {
	relation/irreflexive[r]
	relation/transitive[r]
}

fact "all call transitions are associated with an event" {
	all t: impl/CallTransition | some e : Event | e.op = t
}

run {
	#Acceptor=3
	#Proposer=2
	#WriteTransition=2
	#impl/Write=2
	all disj t1, t2: WriteTransition | no t1.op&t2.op
	all disj w1,w2: impl/Write | no w1.val & w2.val
	some ReadTransition.rval
} for 17 but 3 Acceptor, 2 Proposer, 1 ReadTransition, 2 WriteTransition, 2 impl/Write

