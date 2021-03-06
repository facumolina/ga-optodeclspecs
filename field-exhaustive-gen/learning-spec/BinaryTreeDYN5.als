module unknown

open util/integer

one sig Null {}

abstract sig TreeNode {}

one sig N0 extends TreeNode {}

one sig N1 extends TreeNode {}

one sig N2 extends TreeNode {}

one sig N3 extends TreeNode {}

one sig N4 extends TreeNode {}

abstract sig BinaryTree {}

one sig T0 extends BinaryTree {}

abstract sig boolean {}

one sig true extends boolean {}

one sig false extends boolean {}

pred catalog [
	thiz: BinaryTree, 
	root: BinaryTree ->one (TreeNode + Null), 
	left: TreeNode ->one (TreeNode + Null), 
	right: TreeNode ->one (TreeNode + Null), 
	size: BinaryTree ->one Int, 
	element: TreeNode ->one Int] {
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

pred repOK [
	thiz: BinaryTree, 
	root: BinaryTree ->one (TreeNode + Null), 
	left: TreeNode ->one (TreeNode + Null), 
	right: TreeNode ->one (TreeNode + Null), 
	size: BinaryTree ->one Int, 
	element: TreeNode ->one Int] {
(all n : one((((thiz) . (root)) . (*((left) + (right)))) - (Null)) | !((n) in ((n) . (^((left) + (right)))))) and (all n : one((((thiz) . (root)) . (*((left) + (right)))) - (Null)) | ((((n) . (left)) . (*((left) + (right)))) & (((n) . (right)) . (*((left) + (right))))) in (Null)) and (!(all n : one((((thiz) . (root)) . (*((left) + (right)))) - (Null)) | gt[(n) . (element),0]))
}
 
pred SimmetryBreaking [thiz: BinaryTree, root: BinaryTree ->one (TreeNode + Null), left: TreeNode ->one (TreeNode + Null), right: TreeNode ->one (TreeNode + Null),element: TreeNode ->one Int] {
(root in T0 -> Null + T0 -> N0 and left in N0 -> Null + N0 -> N0 + N0 -> N1 + N1 -> Null + N1 -> N1 + N1 -> N0 + N1 -> N2 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2 + N2 -> N3 + N2 -> N4 + N3 -> Null + N3 -> N0 + N3 -> N1 + N3 -> N2 + N3 -> N3 + N3 -> N4 + N4 -> Null + N4 -> N0 + N4 -> N1 + N4 -> N2 + N4 -> N3 + N4 -> N4 and right in N0 -> Null + N0 -> N0 + N0 -> N1 + N0 -> N2 + N1 -> Null + N1 -> N0 + N1 -> N1 + N1 -> N2 + N1 -> N3 + N1 -> N4 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2 + N2 -> N3 + N2 -> N4 + N3 -> Null + N3 -> N0 + N3 -> N1 + N3 -> N2 + N3 -> N3 + N3 -> N4 + N4 -> Null + N4 -> N0 + N4 -> N1 + N4 -> N2 + N4 -> N3 + N4 -> N4 and 
(all n: TreeNode - (thiz.root).* (left + right) | { (n.left = Null and n.right = Null )})
and (all n: TreeNode | eq[n.element,0])
 ) 
}
 
/* action pick*/ 
pred pick [s, s': set TreeNode, e, e': TreeNode] {
(some s and e' in s and s' = s - e' ) 
}
 
pred sourceRepOK [thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11, result_12: boolean] {
--some 	current_0, current_1, current_2, current_3, current_4, current_5: one TreeNode + Null, 	visited_1, visited_2, visited_3, visited_4, visited_5, visited_6, visited_7, visited_8, visited_9, visited_10, visited_11: set TreeNode, 	workset_1, workset_2, workset_3, workset_4, workset_5, workset_6, workset_7, workset_8, workset_9, workset_10, workset_11, workset_12, workset_13, workset_14, workset_15, workset_16: set TreeNode | { 
--(workset_1 = thiz_0.root_0 and visited_1 = thiz_0.root_0 and ((thiz_0.root_0 = Null and ((thiz_0.size_0 = 0 and result_1 = true ) or (not thiz_0.size_0 = 0 and result_1 = false ) ) and result_1 = result_12 and current_0 = current_5 and visited_1 = visited_11 and workset_1 = workset_16 ) or (not thiz_0.root_0 = Null and result_1 = true and ((result_1 = result_11 and current_0 = current_5 and visited_1 = visited_11 and workset_1 = workset_16 ) or (result_1 = true and some workset_1 and pick[workset_1, workset_2, current_0, current_1] and (((current_1.left_0) != Null and ((current_1.left_0 in visited_1 and result_2 = false and visited_1 = visited_2 and workset_2 = workset_3 ) or (not current_1.left_0 in visited_1 and visited_2 = visited_1 + current_1.left_0 and workset_3 = workset_2 + current_1.left_0 and result_1 = result_2 ) ) ) or (not (current_1.left_0) != Null and result_1 = result_2 and visited_1 = visited_2 and workset_2 = workset_3 ) ) and ((result_2 = true and (current_1.right_0) != Null and ((current_1.right_0 in visited_2 and result_3 = false and visited_2 = visited_3 and workset_3 = workset_4 ) or (not current_1.right_0 in visited_2 and visited_3 = visited_2 + current_1.right_0 and workset_4 = workset_3 + current_1.right_0 and result_2 = result_3 ) ) ) or (not (result_2 = true and (current_1.right_0) != Null ) and result_2 = result_3 and visited_2 = visited_3 and workset_3 = workset_4 ) ) and ((result_3 = result_11 and current_1 = current_5 and visited_3 = visited_11 and workset_4 = workset_16 ) or (result_3 = true and some workset_4 and pick[workset_4, workset_5, current_1, current_2] and (((current_2.left_0) != Null and ((current_2.left_0 in visited_3 and result_4 = false and visited_3 = visited_4 and workset_5 = workset_6 ) or (not current_2.left_0 in visited_3 and visited_4 = visited_3 + current_2.left_0 and workset_6 = workset_5 + current_2.left_0 and result_3 = result_4 ) ) ) or (not (current_2.left_0) != Null and result_3 = result_4 and visited_3 = visited_4 and workset_5 = workset_6 ) ) and ((result_4 = true and (current_2.right_0) != Null and ((current_2.right_0 in visited_4 and result_5 = false and visited_4 = visited_5 and workset_6 = workset_7 ) or (not current_2.right_0 in visited_4 and visited_5 = visited_4 + current_2.right_0 and workset_7 = workset_6 + current_2.right_0 and result_4 = result_5 ) ) ) or (not (result_4 = true and (current_2.right_0) != Null ) and result_4 = result_5 and visited_4 = visited_5 and workset_6 = workset_7 ) ) and ((result_5 = result_11 and current_2 = current_5 and visited_5 = visited_11 and workset_7 = workset_16 ) or (result_5 = true and some workset_7 and pick[workset_7, workset_8, current_2, current_3] and (((current_3.left_0) != Null and ((current_3.left_0 in visited_5 and result_6 = false and visited_5 = visited_6 and workset_8 = workset_9 ) or (not current_3.left_0 in visited_5 and visited_6 = visited_5 + current_3.left_0 and workset_9 = workset_8 + current_3.left_0 and result_5 = result_6 ) ) ) or (not (current_3.left_0) != Null and result_5 = result_6 and visited_5 = visited_6 and workset_8 = workset_9 ) ) and ((result_6 = true and (current_3.right_0) != Null and ((current_3.right_0 in visited_6 and result_7 = false and visited_6 = visited_7 and workset_9 = workset_10 ) or (not current_3.right_0 in visited_6 and visited_7 = visited_6 + current_3.right_0 and workset_10 = workset_9 + current_3.right_0 and result_6 = result_7 ) ) ) or (not (result_6 = true and (current_3.right_0) != Null ) and result_6 = result_7 and visited_6 = visited_7 and workset_9 = workset_10 ) ) and ((result_7 = result_11 and current_3 = current_5 and visited_7 = visited_11 and workset_10 = workset_16 ) or (result_7 = true and some workset_10 and pick[workset_10, workset_11, current_3, current_4] and (((current_4.left_0) != Null and ((current_4.left_0 in visited_7 and result_8 = false and visited_7 = visited_8 and workset_11 = workset_12 ) or (not current_4.left_0 in visited_7 and visited_8 = visited_7 + current_4.left_0 and workset_12 = workset_11 + current_4.left_0 and result_7 = result_8 ) ) ) or (not (current_4.left_0) != Null and result_7 = result_8 and visited_7 = visited_8 and workset_11 = workset_12 ) ) and ((result_8 = true and (current_4.right_0) != Null and ((current_4.right_0 in visited_8 and result_9 = false and visited_8 = visited_9 and workset_12 = workset_13 ) or (not current_4.right_0 in visited_8 and visited_9 = visited_8 + current_4.right_0 and workset_13 = workset_12 + current_4.right_0 and result_8 = result_9 ) ) ) or (not (result_8 = true and (current_4.right_0) != Null ) and result_8 = result_9 and visited_8 = visited_9 and workset_12 = workset_13 ) ) and ((result_9 = result_11 and current_4 = --current_5 and visited_9 = visited_11 and workset_13 = workset_16 ) or (result_9 = true and some workset_13 and pick[workset_13, workset_14, current_4, current_5] and (((current_5.left_0) != Null and ((current_5.left_0 in visited_9 and result_10 = false and visited_9 = visited_10 and workset_14 = workset_15 ) or (not current_5.left_0 in visited_9 and visited_10 = visited_9 + current_5.left_0 and workset_15 = workset_14 + current_5.left_0 and result_9 = result_10 ) ) ) or (not (current_5.left_0) != Null and result_9 = result_10 and visited_9 = visited_10 and workset_14 = workset_15 ) ) and ((result_10 = true and (current_5.right_0) != Null and ((current_5.right_0 in visited_10 and result_11 = false and visited_10 = visited_11 and workset_15 = workset_16 ) or (not current_5.right_0 in visited_10 and visited_11 = visited_10 + current_5.right_0 and workset_16 = workset_15 + current_5.right_0 and result_10 = result_11 ) ) ) or (not (result_10 = true and (current_5.right_0) != Null ) and result_10 = result_11 and visited_10 = visited_11 and workset_15 = workset_16 ) ) ) ) ) ) ) ) ) ) ) ) and not (result_11 = true and some workset_16 ) and ((result_11 = true and (#visited_11) != (thiz_0.size_0) and result_12 = false ) or (not (result_11 = true and (#visited_11) != (thiz_0.size_0) ) and result_11 = result_12 ) ) ) ) )}
some 	current_0, current_1, current_2, current_3, current_4, current_5: one TreeNode + Null, 	visited_1, visited_2, visited_3, visited_4, visited_5, visited_6, visited_7, visited_8, visited_9, visited_10, visited_11: set TreeNode, 	workset_1, workset_2, workset_3, workset_4, workset_5, workset_6, workset_7, workset_8, workset_9, workset_10, workset_11, workset_12, workset_13, workset_14, workset_15, workset_16: set TreeNode | { 
(workset_1 = thiz_0.root_0 and visited_1 = thiz_0.root_0 and ((thiz_0.root_0 = Null and ((thiz_0.size_0 = 0 and result_1 = true ) or (not thiz_0.size_0 = 0 and result_1 = false ) ) and 
	result_1 = result_12 and result_1 = result_11 and result_1 = result_10 and result_1 = result_9
	and result_1 = result_8 and result_1 = result_7 and result_1 = result_6 and result_1 = result_5
	and result_1 = result_4 and result_1 = result_3 and result_1 = result_2
	and current_0 = current_5 and current_0 = current_4 and current_0 = current_3 and current_0 = current_2 and current_0 = current_1
	and visited_1 = visited_11 and visited_1 = visited_10 and visited_1 = visited_9 and visited_1 = visited_8
	and visited_1 = visited_7 and visited_1 = visited_6 and visited_1 = visited_5 and visited_1 = visited_4
	and visited_1 = visited_3 and visited_1 = visited_2
	and workset_1 = workset_16 and workset_1 = workset_15 and workset_1 = workset_14 and workset_1 = workset_13
	and workset_1 = workset_12 and workset_1 = workset_11 and workset_1 = workset_10 and workset_1 = workset_9
	and workset_1 = workset_8 and workset_1 = workset_7 and workset_1 = workset_6 and workset_1 = workset_5
	and workset_1 = workset_4 and workset_1 = workset_3 and workset_1 = workset_2
) or (not thiz_0.root_0 = Null and result_1 = true and ((
	result_1 = result_11 and result_1 = result_10 and result_1 = result_9 and result_1 = result_8
	and result_1 = result_7 and result_1 = result_6 and result_1 = result_5 and result_1 = result_4
	and result_1 = result_3 and result_1 = result_2 
	and current_0 = current_5 and current_0 = current_4 and current_0 = current_3 and current_0 = current_2 and current_0 = current_1 
	and visited_1 = visited_11 and visited_1 = visited_10 and visited_1 = visited_9 and visited_1 = visited_8
	and visited_1 = visited_7 and visited_1 = visited_6 and visited_1 = visited_5 and visited_1 = visited_4
	and visited_1 = visited_3 and visited_1 = visited_2
	and workset_1 = workset_16 and workset_1 = workset_15 and workset_1 = workset_14 and workset_1 = workset_13
	and workset_1 = workset_12 and workset_1 = workset_11 and workset_1 = workset_10 and workset_1 = workset_9
	and workset_1 = workset_8 and workset_1 = workset_7 and workset_1 = workset_6 and workset_1 = workset_5
	and workset_1 = workset_4 and workset_1 = workset_3 and workset_1 = workset_2 
) or (result_1 = true and some workset_1 and pick[workset_1, workset_2, current_0, current_1] and (((current_1.left_0) != Null and ((current_1.left_0 in visited_1 and result_2 = false and visited_1 = visited_2 and workset_2 = workset_3 ) or (not current_1.left_0 in visited_1 and visited_2 = visited_1 + current_1.left_0 and workset_3 = workset_2 + current_1.left_0 and result_1 = result_2 ) ) ) or (not (current_1.left_0) != Null and result_1 = result_2 and visited_1 = visited_2 and workset_2 = workset_3 ) ) and ((result_2 = true and (current_1.right_0) != Null and ((current_1.right_0 in visited_2 and result_3 = false and visited_2 = visited_3 and workset_3 = workset_4 ) or (not current_1.right_0 in visited_2 and visited_3 = visited_2 + current_1.right_0 and workset_4 = workset_3 + current_1.right_0 and result_2 = result_3 ) ) ) or (not (result_2 = true and (current_1.right_0) != Null ) and result_2 = result_3 and visited_2 = visited_3 and workset_3 = workset_4 ) ) and ((result_3 = result_11 and current_1 = current_5 and visited_3 = visited_11 and workset_4 = workset_16 ) or (result_3 = true and some workset_4 and pick[workset_4, workset_5, current_1, current_2] and (((current_2.left_0) != Null and ((current_2.left_0 in visited_3 and result_4 = false and visited_3 = visited_4 and workset_5 = workset_6 ) or (not current_2.left_0 in visited_3 and visited_4 = visited_3 + current_2.left_0 and workset_6 = workset_5 + current_2.left_0 and result_3 = result_4 ) ) ) or (not (current_2.left_0) != Null and result_3 = result_4 and visited_3 = visited_4 and workset_5 = workset_6 ) ) and ((result_4 = true and (current_2.right_0) != Null and ((current_2.right_0 in visited_4 and result_5 = false and visited_4 = visited_5 and workset_6 = workset_7 ) or (not current_2.right_0 in visited_4 and visited_5 = visited_4 + current_2.right_0 and workset_7 = workset_6 + current_2.right_0 and result_4 = result_5 ) ) ) or (not (result_4 = true and (current_2.right_0) != Null ) and result_4 = result_5 and visited_4 = visited_5 and workset_6 = workset_7 ) ) and ((result_5 = result_11 and current_2 = current_5 and visited_5 = visited_11 and workset_7 = workset_16 ) or (result_5 = true and some workset_7 and pick[workset_7, workset_8, current_2, current_3] and (((current_3.left_0) != Null and ((current_3.left_0 in visited_5 and result_6 = false and visited_5 = visited_6 and workset_8 = workset_9 ) or (not current_3.left_0 in visited_5 and visited_6 = visited_5 + current_3.left_0 and workset_9 = workset_8 + current_3.left_0 and result_5 = result_6 ) ) ) or (not (current_3.left_0) != Null and result_5 = result_6 and visited_5 = visited_6 and workset_8 = workset_9 ) ) and ((result_6 = true and (current_3.right_0) != Null and ((current_3.right_0 in visited_6 and result_7 = false and visited_6 = visited_7 and workset_9 = workset_10 ) or (not current_3.right_0 in visited_6 and visited_7 = visited_6 + current_3.right_0 and workset_10 = workset_9 + current_3.right_0 and result_6 = result_7 ) ) ) or (not (result_6 = true and (current_3.right_0) != Null ) and result_6 = result_7 and visited_6 = visited_7 and workset_9 = workset_10 ) ) and ((result_7 = result_11 and current_3 = current_5 and visited_7 = visited_11 and workset_10 = workset_16 ) or (result_7 = true and some workset_10 and pick[workset_10, workset_11, current_3, current_4] and (((current_4.left_0) != Null and ((current_4.left_0 in visited_7 and result_8 = false and visited_7 = visited_8 and workset_11 = workset_12 ) or (not current_4.left_0 in visited_7 and visited_8 = visited_7 + current_4.left_0 and workset_12 = workset_11 + current_4.left_0 and result_7 = result_8 ) ) ) or (not (current_4.left_0) != Null and result_7 = result_8 and visited_7 = visited_8 and workset_11 = workset_12 ) ) and ((result_8 = true and (current_4.right_0) != Null and ((current_4.right_0 in visited_8 and result_9 = false and visited_8 = visited_9 and workset_12 = workset_13 ) or (not current_4.right_0 in visited_8 and visited_9 = visited_8 + current_4.right_0 and workset_13 = workset_12 + current_4.right_0 and result_8 = result_9 ) ) ) or (not (result_8 = true and (current_4.right_0) != Null ) and result_8 = result_9 and visited_8 = visited_9 and workset_12 = workset_13 ) ) and ((result_9 = result_11 and current_4 = current_5 and visited_9 = visited_11 and workset_13 = workset_16 ) or (result_9 = true and some workset_13 and pick[workset_13, workset_14, current_4, current_5] and (((current_5.left_0) != Null and ((current_5.left_0 in visited_9 and result_10 = false and visited_9 = visited_10 and workset_14 = workset_15 ) or (not current_5.left_0 in visited_9 and visited_10 = visited_9 + current_5.left_0 and workset_15 = workset_14 + current_5.left_0 and result_9 = result_10 ) ) ) or (not (current_5.left_0) != Null and result_9 = result_10 and visited_9 = visited_10 and workset_14 = workset_15 ) ) and ((result_10 = true and (current_5.right_0) != Null and ((current_5.right_0 in visited_10 and result_11 = false and visited_10 = visited_11 and workset_15 = workset_16 ) or (not current_5.right_0 in visited_10 and visited_11 = visited_10 + current_5.right_0 and workset_16 = workset_15 + current_5.right_0 and result_10 = result_11 ) ) ) or (not (result_10 = true and (current_5.right_0) != Null ) and result_10 = result_11 and visited_10 = visited_11 and workset_15 = workset_16 ) ) ) ) ) ) ) ) ) ) ) ) and not (result_11 = true and some workset_16 ) and ((result_11 = true and (#visited_11) != (thiz_0.size_0) and result_12 = false ) or (not (result_11 = true and (#visited_11) != (thiz_0.size_0) ) and result_11 = result_12 ) ) ) ) )
}
  
}
 
--pred sourceRepOK_TRUEDYN3 [thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11, result_12: boolean] {
--(SimmetryBreaking[thiz_0, root_0, left_0, right_0,element_0] and sourceRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11, result_12] and result_12 = true and thiz_0.size_0 = 5 ) 
--}
 
--run sourceRepOK_TRUEDYN3 for 5 but 5 int
-- Negative counterexamples
pred NegativeCounterExample[thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int] {
	SimmetryBreaking[thiz_0, root_0, left_0, right_0,element_0] and 
	repOK[thiz_0, root_0, left_0, right_0, size_0, element_0] and 
	(some result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12: boolean |  
	sourceRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12] and result_12=false)
}


-- Positive counterexamples
pred PositiveCounterExample[thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int] {
	SimmetryBreaking[thiz_0, root_0, left_0, right_0,element_0] and
 	not catalog[thiz_0, root_0, left_0, right_0, size_0, element_0] and 
	(some result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12: boolean | sourceRepOK [thiz_0, root_0, left_0, right_0, size_0, element_0, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12] and result_12=true)
}

--run sourceRepOK_TRUEDYN3 for 5 but 4 int
run NegativeCounterExample for 5 but 4 int
run PositiveCounterExample for 5 but 4 int
