module unknown

open util/integer

one sig Null {}

abstract sig Node {}

one sig N0 extends Node {}

one sig N1 extends Node {}

one sig N2 extends Node {}

abstract sig BinaryHeap {}

one sig T0 extends BinaryHeap {}

abstract sig boolean {}

one sig true extends boolean {}

one sig false extends boolean {}
 

 
/* action pick*/ 
pred pick [s, s': set Node, e, e': Node] {
(some s and e' in s and s' = s - e' ) 
}

-- sourceRepOK: Invariant translated from an operational specification
pred sourceRepOK [thiz_0: BinaryHeap, root_0: BinaryHeap ->one (Node + Null), left_0: Node ->one (Node + Null), right_0: Node ->one (Node + Null), size_0: BinaryHeap ->one Int, element_0: Node ->one Int, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8: boolean] {
some 	current_0, current_1, current_2, current_3: one Node + Null, 	visited_1, visited_2, visited_3, visited_4, visited_5, visited_6, visited_7: set Node, 	workset_1, workset_2, workset_3, workset_4, workset_5, workset_6, workset_7, workset_8, workset_9, workset_10: set Node | { 
(workset_1 = thiz_0.root_0 and visited_1 = thiz_0.root_0 and ((thiz_0.root_0 = Null and ((thiz_0.size_0 = 0 and result_1 = true ) or (not thiz_0.size_0 = 0 and result_1 = false ) ) and result_1 = result_8 and current_0 = current_3 and visited_1 = visited_7 and workset_1 = workset_10 ) or (not thiz_0.root_0 = Null and result_1 = true and ((result_1 = result_7 and current_0 = current_3 and visited_1 = visited_7 and workset_1 = workset_10 ) or (result_1 = true and some workset_1 and pick[workset_1, workset_2, current_0, current_1] and (((current_1.left_0) != Null and ((current_1.left_0 in visited_1 and result_2 = false and visited_1 = visited_2 and workset_2 = workset_3 ) or (not current_1.left_0 in visited_1 and ((lt[current_1.element_0, (current_1.left_0).element_0] and result_2 = false and visited_1 = visited_2 and workset_2 = workset_3 ) or (not lt[current_1.element_0, (current_1.left_0).element_0] and visited_2 = visited_1 + current_1.left_0 and workset_3 = workset_2 + current_1.left_0 and result_1 = result_2 ) ) ) ) ) or (not (current_1.left_0) != Null and result_1 = result_2 and visited_1 = visited_2 and workset_2 = workset_3 ) ) and ((result_2 = true and (current_1.right_0) != Null and ((current_1.right_0 in visited_2 and result_3 = false and visited_2 = visited_3 and workset_3 = workset_4 ) or (not current_1.right_0 in visited_2 and ((lt[current_1.element_0, (current_1.right_0).element_0] and result_3 = false and visited_2 = visited_3 and workset_3 = workset_4 ) or (not lt[current_1.element_0, (current_1.right_0).element_0] and visited_3 = visited_2 + current_1.right_0 and workset_4 = workset_3 + current_1.right_0 and result_2 = result_3 ) ) ) ) ) or (not (result_2 = true and (current_1.right_0) != Null ) and result_2 = result_3 and visited_2 = visited_3 and workset_3 = workset_4 ) ) and ((result_3 = result_7 and current_1 = current_3 and visited_3 = visited_7 and workset_4 = workset_10 ) or (result_3 = true and some workset_4 and pick[workset_4, workset_5, current_1, current_2] and (((current_2.left_0) != Null and ((current_2.left_0 in visited_3 and result_4 = false and visited_3 = visited_4 and workset_5 = workset_6 ) or (not current_2.left_0 in visited_3 and ((lt[current_2.element_0, (current_2.left_0).element_0] and result_4 = false and visited_3 = visited_4 and workset_5 = workset_6 ) or (not lt[current_2.element_0, (current_2.left_0).element_0] and visited_4 = visited_3 + current_2.left_0 and workset_6 = workset_5 + current_2.left_0 and result_3 = result_4 ) ) ) ) ) or (not (current_2.left_0) != Null and result_3 = result_4 and visited_3 = visited_4 and workset_5 = workset_6 ) ) and ((result_4 = true and (current_2.right_0) != Null and ((current_2.right_0 in visited_4 and result_5 = false and visited_4 = visited_5 and workset_6 = workset_7 ) or (not current_2.right_0 in visited_4 and ((lt[current_2.element_0, (current_2.right_0).element_0] and result_5 = false and visited_4 = visited_5 and workset_6 = workset_7 ) or (not lt[current_2.element_0, (current_2.right_0).element_0] and visited_5 = visited_4 + current_2.right_0 and workset_7 = workset_6 + current_2.right_0 and result_4 = result_5 ) ) ) ) ) or (not (result_4 = true and (current_2.right_0) != Null ) and result_4 = result_5 and visited_4 = visited_5 and workset_6 = workset_7 ) ) and ((result_5 = result_7 and current_2 = current_3 and visited_5 = visited_7 and workset_7 = workset_10 ) or (result_5 = true and some workset_7 and pick[workset_7, workset_8, current_2, current_3] and (((current_3.left_0) != Null and ((current_3.left_0 in visited_5 and result_6 = false and visited_5 = visited_6 and workset_8 = workset_9 ) or (not current_3.left_0 in visited_5 and ((lt[current_3.element_0, (current_3.left_0).element_0] and result_6 = false and visited_5 = visited_6 and workset_8 = workset_9 ) or (not lt[current_3.element_0, (current_3.left_0).element_0] and visited_6 = visited_5 + current_3.left_0 and workset_9 = workset_8 + current_3.left_0 and result_5 = result_6 ) ) ) ) ) or (not (current_3.left_0) != Null and result_5 = result_6 and visited_5 = visited_6 and workset_8 = workset_9 ) ) and ((result_6 = true and (current_3.right_0) != Null and ((current_3.right_0 in visited_6 and result_7 = false and visited_6 = visited_7 and workset_9 = workset_10 ) or (not current_3.right_0 in visited_6 and ((lt[current_3.element_0, (current_3.right_0).element_0] and result_7 = false and visited_6 = visited_7 and workset_9 = workset_10 ) or (not lt[current_3.element_0, (current_3.right_0).element_0] and visited_7 = visited_6 + current_3.right_0 and workset_10 = workset_9 + current_3.right_0 and result_6 = result_7 ) ) ) ) ) or (not (result_6 = true and (current_3.right_0) != Null ) and result_6 = result_7 and visited_6 = visited_7 and workset_9 = workset_10 ) ) ) ) ) ) ) ) and not (result_7 = true and some workset_10 ) and ((result_7 = true and (#(visited_7)) != (thiz_0.size_0) and result_8 = false ) or (not (result_7 = true and (#(visited_7)) != (thiz_0.size_0) ) and result_7 = result_8 ) ) ) ) )}
 
}

-- Catalog
pred catalog [thiz: BinaryHeap, root: BinaryHeap ->one (Node + Null), left: Node ->one (Node + Null), right: Node ->one (Node + Null), size: BinaryHeap ->one Int, element: Node ->one Int] {
	/* Acyclic*/
	(all n: thiz.root.*(left + right) - Null | not (n in n.^(left + right))) and
	/* Cyclic*/
	(all n: thiz.root.*(left + right) - Null | n in n.^(left + right)) and
	/* Intersection in null*/	
	(all n: thiz.root.*(left + right) - Null | ( n.left.*(left+right) & n.right.*(left + right)) in Null) and 
	/* Intersection not null*/	
	(all n: thiz.root.*(left + right) - Null | ( n.left.*(left+right) & n.right.*(left + right)) not in Null) and
	/* Left height - Right height <= 1*/
	(all n: thiz.root.*(left + right) - Null | #(n.left.*(left+right)) - #(n.right.*(left+right)) <= 1) and
	/* Left height - Right height >= -1*/	
	(all n: thiz.root.*(left + right) - Null | #(n.left.*(left+right)) - #(n.right.*(left+right)) >= -1) and
	/* Left height - Right height == 0*/	
	(all n: thiz.root.*(left + right) - Null | eq[#(n.left.*(left+right)) - #(n.right.*(left+right)),0]) and
	/* At least one child*/
	(all n: thiz.root.*(left + right) - Null | n.left != Null or n.right != Null) and
	/* Doubly */
	(all n: thiz.root.*(left+right) - Null | n = n.left.right)
	/* Root not null*/
	(thiz.root != Null) and
	/* Right not null => Left not null */
	(all n: thiz.root.*(left+ right) - Null | n.right != Null => n.left != Null) and
	/* Left not null => Right not null */
	(all n: thiz.root.*(left+ right) - Null | n.left != Null => n.right != Null) and
	/* Size1*/
	(eq[thiz.size,#(thiz.root.*(left + right) - Null)]) and
	/* Size2*/
	(eq[thiz.size,#(thiz.root.*(left + right) )]) and
	/* Size2*/
	(eq[thiz.size,sub[#(thiz.root.*(left + right) - Null),1]]) and
	/* Keys order1*/
	(all n:thiz.root.*(left+right) | ((n.left!=Null) => gte[n.element,n.left.element]) and ((n.right!=Null) => gte[n.element,n.right.element])) and
	/* Keys order2*/
	(all n:thiz.root.*(left+right) | ((n.left!=Null) => lte[n.element,n.left.element]) and ((n.right!=Null) => lte[n.element,n.right.element])) and 
	/* Keys order3*/
	(all n:thiz.root.*(left+right) | ((n.left!=Null) => eq[n.element,n.left.element]) and ((n.right!=Null) => eq[n.element,n.right.element])) and
	/* Keys order4*/
	(all n:thiz.root.*(left+right) | ((n.left!=Null) => gte[n.left.element,n.element]) and ((n.right!=Null) => lt[n.right.element,n.element])) and
	/* Keys order5*/
	(all n:thiz.root.*(left+right) | ((n.left!=Null) => lt[n.left.element,n.element]) and ((n.right!=Null) => gte[n.right.element,n.element])) and 
	/* Keys order6*/
	(all n:thiz.root.*(left+right) | ((n.left!=Null) => lte[n.left.element,n.element]) and ((n.right!=Null) => gt[n.right.element,n.element])) and 
    /* Keys order7*/
	(all n: thiz.root.*(left+right) | 
	(all x: n.left.*(left+right) - Null| lt[x.element,n.element]) -- LeftOrder
		and
	(all x: n.right.*(left+right) - Null| gte[x.element,n.element])) and -- RigthOrder
	 /* Keys order8*/
	(all n: thiz.root.*(left+right) | 
	(all x: n.left.*(left+right) - Null| gt[x.element,n.element]) -- LeftOrder
		and
	(all x: n.right.*(left+right) - Null| lte[x.element,n.element])) and -- RigthOrder 
	/* Elem1 */
	(all n:thiz.root.*(left+right)-Null | gt[n.element,0]) and
	/* Elem2 */
	(all n:thiz.root.*(left+right)-Null | gte[n.element,0]) and
	/* Elem1 */
	(all n:thiz.root.*(left+right)-Null | lt[n.element,0]) and
	/* Elem1 */
	(all n:thiz.root.*(left+right)-Null | lte[n.element,0]) 
}
-- repOK: Invariant to be learned
pred repOK [thiz: BinaryHeap, root: BinaryHeap ->one (Node + Null), left: Node ->one (Node + Null), right: Node ->one (Node + Null), size: BinaryHeap ->one Int, element: Node ->one Int] {
(all n : one((((thiz) . (root)) . (*((left) + (right)))) - (Null)) | !((n) in ((n) . (^((left) + (right)))))) and (all n : one((((thiz) . (root)) . (*((left) + (right)))) - (Null)) | ((((n) . (left)) . (*((left) + (right)))) & (((n) . (right)) . (*((left) + (right))))) in (Null)) and (eq[(thiz) . (size),#((((thiz) . (root)) . (*((left) + (right)))) - (Null))]) and (all n : one(((thiz) . (root)) . (*((left) + (right)))) | ((((n) . (left)) != (Null)) => (gte[(n) . (element),((n) . (left)) . (element)])) and ((((n) . (right)) != (Null)) => (gte[(n) . (element),((n) . (right)) . (element)])))
}

-- SymmetryBreaking: Symmetry breaking predicate to reduce the number of instances
pred SimmetryBreaking [thiz: BinaryHeap, root: BinaryHeap ->one (Node + Null), left: Node ->one (Node + Null), right: Node ->one (Node + Null), element: Node ->one Int] {
(
(root in T0 -> Null + T0 -> N0) and 
(left in N0 -> Null + N0 -> N0 + N0 -> N1 + N1 -> Null + N1 -> N1 + N1 -> N0 + N1 -> N2 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2) and 
(right in N0 -> Null + N0 -> N0 + N0 -> N1 + N0 -> N2 + N1 -> Null + N1 -> N0 + N1 -> N1 + N1 -> N2 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2) and 
(all n: Node - (thiz.root).* (left + right) | { (n.left = Null and n.right = Null)})
 ) 
}


-- NegativeCounterExample: Predicate that allow us to get negative counterexamples, that is cases
-- of the data structure that safisfies the repOK being learned but does not satisfies the sourceRepOK.
pred NegativeCounterExample [thiz_0: BinaryHeap, root_0: BinaryHeap ->one (Node + Null), left_0: Node ->one (Node + Null), right_0: Node ->one (Node + Null), size_0: BinaryHeap ->one Int, element_0: Node ->one Int] {
(SimmetryBreaking[thiz_0, root_0, left_0, right_0, element_0] and repOK[thiz_0, root_0, left_0, right_0, size_0, element_0] and  (sourceRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0, QFNegativeCounterExample.result_0, QFNegativeCounterExample.result_1, QFNegativeCounterExample.result_2, QFNegativeCounterExample.result_3, QFNegativeCounterExample.result_4, QFNegativeCounterExample.result_5, QFNegativeCounterExample.result_6, QFNegativeCounterExample.result_7, QFNegativeCounterExample.result_8] and QFNegativeCounterExample.result_8= false )
 ) 
}
 
one sig QFNegativeCounterExample{
	result_0 : one boolean, 
	result_1 : one boolean, 
	result_2 : one boolean, 
	result_3 : one boolean, 
	result_4 : one boolean, 
	result_5 : one boolean, 
	result_6 : one boolean, 
	result_7 : one boolean, 
	result_8 : one boolean
}

-- PositiveCounterExample: Predicate that allow us to get positive counterexamples, that is cases
-- of the data structure that does not satisfies the repOK being learned but satisfies the sourceRepOK.
pred PositiveCounterExample [thiz_0: BinaryHeap, root_0: BinaryHeap ->one (Node + Null), left_0: Node ->one (Node + Null), right_0: Node ->one (Node + Null), size_0: BinaryHeap ->one Int, element_0: Node ->one Int] {
(SimmetryBreaking[thiz_0, root_0, left_0, right_0, element_0] and not catalog [thiz_0, root_0, left_0, right_0, size_0, element_0] and some 	result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8: one boolean | { 
(sourceRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8] and result_8 = true )}
 ) 
}
 
run NegativeCounterExample for 3 but 3 int
run PositiveCounterExample for 3 but 3 int

