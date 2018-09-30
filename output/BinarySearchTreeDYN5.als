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
(all n : one((((thiz) . (root)) . (*((left) + (right)))) - (Null)) | !((n) in ((n) . (^((left) + (right)))))) and (eq[(thiz) . (size),#((((thiz) . (root)) . (*((left) + (right)))) - (Null))]) and (all n : one(((thiz) . (root)) . (*((left) + (right)))) | (all x : one((((n) . (left)) . (*((left) + (right)))) - (Null)) | lt[(x) . (element),(n) . (element)]) and (all x : one((((n) . (right)) . (*((left) + (right)))) - (Null)) | gte[(x) . (element),(n) . (element)]))
}
 
--(all n: thiz.root.*(left+right) | (n.left.*(left+ right)) & (n.right.*(left+right)) in Null) and
--(all n : thiz.root.*(left + right) | n !in n .^(left+right))  and
--(eq[thiz.size,#(thiz.root.*(left+right) - Null)]) and
--(all n: thiz.root.*(left+right) | 
--		(all x: n.left.*(left+right) - Null| lt[x.element,n.element]) -- LeftOrder
--		and
--		(all x: n.right.*(left+right) - Null| gte[x.element,n.element])-- RigthOrder
--	)

pred SimmetryBreaking [thiz: BinaryTree, root: BinaryTree ->one (TreeNode + Null), left: TreeNode ->one (TreeNode + Null), right: TreeNode ->one (TreeNode + Null)] {
(root in T0 -> Null + T0 -> N0 and left in N0 -> Null + N0 -> N0 + N0 -> N1 + N1 -> Null + N1 -> N1 + N1 -> N0 + N1 -> N2 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2 + N2 -> N3 + N2 -> N4 + N3 -> Null + N3 -> N0 + N3 -> N1 + N3 -> N2 + N3 -> N3 + N3 -> N4 + N4 -> Null + N4 -> N0 + N4 -> N1 + N4 -> N2 + N4 -> N3 + N4 -> N4 and right in N0 -> Null + N0 -> N0 + N0 -> N1 + N0 -> N2 + N1 -> Null + N1 -> N0 + N1 -> N1 + N1 -> N2 + N1 -> N3 + N1 -> N4 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2 + N2 -> N3 + N2 -> N4 + N3 -> Null + N3 -> N0 + N3 -> N1 + N3 -> N2 + N3 -> N3 + N3 -> N4 + N4 -> Null + N4 -> N0 + N4 -> N1 + N4 -> N2 + N4 -> N3 + N4 -> N4 and 
(all n: TreeNode - (thiz.root).* (left + right) | { (n.left = Null and n.right = Null )})
 ) 
}
  
pred sourceRepOK [thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int] {
	(all n: thiz_0.root_0.*(left_0+right_0) | (n.left_0.*(left_0+ right_0)) & (n.right_0.*(left_0+right_0)) in Null) and
	(eq[thiz_0.size_0,#(thiz_0.root_0.*(left_0+right_0) - Null)]) and
	(all n: thiz_0.root_0.*(left_0+right_0) | 
		(all x: n.left_0.*(left_0+right_0) - Null| lt[x.element_0,n.element_0]) -- LeftOrder
		and
		(all x: n.right_0.*(left_0+right_0) - Null| gte[x.element_0,n.element_0])-- RigthOrder
 	) and
	(all n : thiz_0.root_0.*(left_0 + right_0) | n !in n .^(left_0+right_0)) 
	--and thiz_0.size_0=5
}
 
 
--run sourceRepOK_TRUEDYN3 for 5 but 5 int
-- Negative counterexamples
pred NegativeCounterExample[thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int] {
	SimmetryBreaking[thiz_0, root_0, left_0, right_0] and 
	repOK[thiz_0, root_0, left_0, right_0, size_0, element_0] and 
	--(some result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12: boolean |  
	--sourceRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12] and result_12=false)
	not sourceRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0]
}


-- Positive counterexamples
pred PositiveCounterExample[thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int] {
	SimmetryBreaking[thiz_0, root_0, left_0, right_0] and
 	not catalog[thiz_0, root_0, left_0, right_0, size_0, element_0] and 
	--(some result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12: boolean | sourceRepOK [thiz_0, root_0, left_0, right_0, size_0, element_0, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11,result_12] and result_12=true)
	sourceRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0]
}

--run sourceRepOK for 5 but 4 int
run NegativeCounterExample for 5 but 4 int
run PositiveCounterExample for 5 but 4 int
