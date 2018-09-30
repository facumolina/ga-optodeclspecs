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

pred repOK [
	thiz: BinaryTree, 
	root: BinaryTree ->one (TreeNode + Null), 
	left: TreeNode ->one (TreeNode + Null), 
	right: TreeNode ->one (TreeNode + Null), 
	size: BinaryTree ->one Int, 
	element: TreeNode ->one Int] {
(all n : thiz.root.*(left+right) | (n.left.*(left + right)) & (n.right.*(left + right)) in Null) and 
(eq[thiz.size,#(thiz.root.*(left + right) - Null)]) and 
(all n : thiz.root.*(left + right) | n !in n.^(left+right))
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


-- Positive counterexamples
pred PositiveCounterExample[thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int] {
	SimmetryBreaking[thiz_0, root_0, left_0, right_0,element_0] and
	repOK[thiz_0, root_0, left_0, right_0, size_0,element_0]
}

--run sourceRepOK_TRUEDYN3 for 5 but 4 int
run PositiveCounterExample for 5 but 4 int
