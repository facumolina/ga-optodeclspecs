module linkedListRepOk

open util/integer

one sig Null {}

abstract sig Node {}

one sig N0 extends Node {}

one sig N1 extends Node {}

one sig N2 extends Node {}

abstract sig List {}

one sig L0 extends List {}

abstract sig boolean {}

one sig true extends boolean {}

one sig false extends boolean {}

one sig QF {
	current_0: one Node + Null, 
	current_1: one Node + Null, 
	current_2: one Node + Null, 
	current_3: one Node + Null,
	current_4: one Node + Null, 	 	
	nodesToVisit_0: one Int, 
	nodesToVisit_1: one Int, 
	nodesToVisit_2: one Int, 
	nodesToVisit_3: one Int,
	nodesToVisit_4: one Int
}

fact {
	QF.current_0=Null and
	QF.nodesToVisit_0=0 
}

pred catalog [
	thiz: List, 
	head: List ->one (Node + Null), 
	size: List ->one Int, 
	next: Node ->one (Node + Null), 
	element: Node ->one Int
] {
	
	(all n: thiz.head.*next | not (n in n.^next)) and	
	(all n: thiz.head.*next | n in n.^next) and	
	(all n: thiz.head.*next - Null | n.next != Null) and
	(some n: thiz.head.*next | n.next = thiz.head) and
	(some (thiz.head & Node)) and
	(gte[thiz.size, 0]) and
	(gte[thiz.size, 1]) and
	(lte[thiz.size, 0]) and
	(lte[thiz.size, 1]) and
	(eq[thiz.size, #(thiz.head.*next - Null)]) and
	(eq[thiz.size, #(thiz.head.*next)]) and
	(eq[thiz.size, add[#(thiz.head.*next - Null),1]]) and
	(eq[thiz.size, sub[#(thiz.head.*next - Null),1]]) and
	(all n: thiz.head.*next | not (n.next = Null) implies lte[n.element,n.next.element] ) and
	(all n: thiz.head.*next | not (n.next = Null) implies gte[n.element,n.next.element] ) and
	(all n: thiz.head.*next | not (n.next = Null) implies gt[n.element,n.next.element] ) and
	(all n: thiz.head.*next | not (n.next = Null) implies lt[n.element,n.next.element] ) and
	(all n: thiz.head.*next | not (n.next = Null) implies eq[n.element,n.next.element] ) and
	(all n: thiz.head.*next-Null |gt[n.element,0] ) and
	(all n: thiz.head.*next-Null |gte[n.element,0] ) and
	(all n: thiz.head.*next-Null |lt[n.element,0] ) and
	(all n: thiz.head.*next-Null |lte[n.element,0] ) and 
	(all n: thiz.head.*next-Null |rem[n.element,2]=0 )
}

-- Symmetry Breaking predicate
pred symmetryBreaking[header_0: List ->one (Node + Null), next_0: Node ->one (Node + Null),element: Node ->one Int] {
	(header_0 in ((L0->Null)+(L0->N0))) and
	(next_0 in (N0->Null)+(N0->N0)+(N0->N1)+(N1->Null)+(N1->N0)+(N1->N1)+(N1->N2)+(N2->Null)+(N2->N0)+(N2->N1)+(N2->N2)) and
	(all n: Node - List.header_0.*next_0 | n.next_0 = Null and n.element=0)
}

-- Operational invariant after the semantics preserving translation
pred sourceRepOK [thiz: List, header_0: List ->one (Node + Null), size_0: List ->one Int, next_0: Node ->one (Node + Null),element: Node ->one Int, result_0, result_1: boolean] {
	(QF.nodesToVisit_1 = thiz.size_0 and QF.current_1 = thiz.header_0 and 
		(
			(lt[thiz.size_0, 0] and result_1 = false and QF.current_1 = QF.current_4 and QF.current_2 = QF.current_1 and QF.current_3 = QF.current_1 and 
					QF.nodesToVisit_1 = QF.nodesToVisit_4 and QF.nodesToVisit_1 = QF.nodesToVisit_2 and QF.nodesToVisit_1 = QF.nodesToVisit_3) 
			or 
			(not lt[thiz.size_0, 0] and 
				(
					(QF.current_1 = QF.current_4 and QF.current_2 = QF.current_1 and QF.current_3 = QF.current_1 and
					QF.nodesToVisit_1 = QF.nodesToVisit_4 and QF.nodesToVisit_1 = QF.nodesToVisit_2 and QF.nodesToVisit_1 = QF.nodesToVisit_3) 
					or 
					(gt[QF.nodesToVisit_1, 0] and QF.current_1 != Null and QF.nodesToVisit_2 = sub[QF.nodesToVisit_1, 1] and 
					QF.current_2 = QF.current_1.next_0 and (
						(QF.current_2 = QF.current_4 and QF.current_2 = QF.current_3 and QF.nodesToVisit_2 = QF.nodesToVisit_4 and QF.nodesToVisit_2 = QF.nodesToVisit_3) 
						or 
							(gt[QF.nodesToVisit_2, 0] and QF.current_2 != Null and QF.nodesToVisit_3 = sub[QF.nodesToVisit_2, 1] and QF.current_3 = QF.current_2.next_0 and ((QF.current_3 = QF.current_4 and QF.nodesToVisit_3 = QF.nodesToVisit_4 ) or (gt[QF.nodesToVisit_3, 0] and QF.current_3 != Null and QF.nodesToVisit_4 = sub[QF.nodesToVisit_3, 1] and QF.current_4 = QF.current_3.next_0 ) ) ) ) ) ) and not (gt[QF.nodesToVisit_4, 0] and QF.current_4 != Null ) and ((eq[QF.nodesToVisit_4, 0] and QF.current_4 = Null and result_1 = true ) or (not (eq[QF.nodesToVisit_4, 0] and QF.current_4 = Null ) and result_1 = false ) ) ) ) )
}

-- Invariant to be learned
pred repOK[thiz: List, head: List ->one (Node + Null), size: List ->one Int, next: Node ->one (Node + Null),element: Node ->one Int] {
--repOKBody
}

-- Negative counterexamples predicate
pred NegativeCounterExample[thiz: List, header_0: List ->one (Node + Null), size_0: List ->one Int, next_0: Node ->one (Node + Null),element: Node ->one Int] {
	symmetryBreaking[header_0, next_0,element] and repOK[thiz, header_0, size_0, next_0,element] and some result_0, result_1: boolean | sourceRepOK [thiz, header_0, size_0, next_0, element,result_0, result_1] and result_1 = false and result_0=false
}

-- Positive counterexamples predicate
pred PositiveCounterExample[thiz: List, header_0: List ->one (Node + Null), size_0: List ->one Int, next_0: Node ->one (Node + Null),element: Node ->one Int] {
	symmetryBreaking[header_0, next_0,element] and not catalog[thiz, header_0, size_0, next_0,element] and some result_0, result_1: boolean | sourceRepOK [thiz, header_0, size_0, next_0, element,result_0, result_1] and result_1 = true and result_0=false
}

run NegativeCounterExample for 3 but 3 int
run PositiveCounterExample for 3 but 3 int
