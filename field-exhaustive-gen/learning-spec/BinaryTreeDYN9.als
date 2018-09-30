module unknown

open util/integer

sig Null {}

abstract sig TreeNode {}

sig N0 {}

sig N1 {}

sig N2 {}

sig N3 {}

sig N4 {}

sig N5 {}

sig N6 {}

sig N7 {}

sig N8 {}

abstract sig BinaryTree {}

sig T0 {}

abstract sig boolean {}

sig true {}

sig false {}

pred repOK [thiz: BinaryTree, root: BinaryTree ->one (TreeNode + Null), left: TreeNode ->one (TreeNode + Null), right: TreeNode ->one (TreeNode + Null), size: BinaryTree ->one Int, element: TreeNode ->one Int] {
(all 	n: one (thiz.root).* left + right | { 
(n.left).* left + right & (n.right).* left + right in Null}
 and eq[thiz.size, #(thiz.root).* left + right - Null] and all 	n: one (thiz.root).* left + right | { 
n !in (n.^ left + right)}
 ) 
}
 
pred symmetryBreaking [thiz: BinaryTree, root: BinaryTree ->one (TreeNode + Null), left: TreeNode ->one (TreeNode + Null), right: TreeNode ->one (TreeNode + Null)] {
(root in T0 -> Null + T0 -> N0 and left in N0 -> Null + N0 -> N0 + N0 -> N1 + N1 -> Null + N1 -> N0 + N1 -> N1 + N1 -> N2 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2 + N2 -> N3 + N2 -> N4 + N3 -> Null + N3 -> N0 + N3 -> N1 + N3 -> N2 + N3 -> N3 + N3 -> N4 + N3 -> N5 + N4 -> Null + N4 -> N0 + N4 -> N1 + N4 -> N2 + N4 -> N3 + N4 -> N4 + N4 -> N5 + N5 -> Null + N5 -> N0 + N5 -> N1 + N5 -> N2 + N5 -> N3 + N5 -> N4 + N5 -> N5 + N5 -> N6 + N5 -> N7 + N6 -> Null + N6 -> N0 + N6 -> N1 + N6 -> N2 + N6 -> N3 + N6 -> N4 + N6 -> N5 + N6 -> N6 + N6 -> N7 + N7 -> Null + N7 -> N0 + N7 -> N1 + N7 -> N2 + N7 -> N3 + N7 -> N4 + N7 -> N5 + N7 -> N6 + N7 -> N7 + N7 -> N8 + N8 -> Null + N8 -> N0 + N8 -> N1 + N8 -> N2 + N8 -> N3 + N8 -> N4 + N8 -> N5 + N8 -> N6 + N8 -> N7 + N8 -> N8 and right in N0 -> Null + N0 -> N0 + N0 -> N1 + N0 -> N2 + N1 -> Null + N1 -> N0 + N1 -> N1 + N1 -> N2 + N1 -> N3 + N1 -> N4 + N2 -> Null + N2 -> N0 + N2 -> N1 + N2 -> N2 + N2 -> N3 + N2 -> N4 + N2 -> N5 + N3 -> Null + N3 -> N0 + N3 -> N1 + N3 -> N2 + N3 -> N3 + N3 -> N4 + N3 -> N5 + N3 -> N6 + N4 -> Null + N4 -> N0 + N4 -> N1 + N4 -> N2 + N4 -> N3 + N4 -> N4 + N4 -> N5 + N4 -> N6 + N4 -> N7 + N5 -> Null + N5 -> N0 + N5 -> N1 + N5 -> N2 + N5 -> N3 + N5 -> N4 + N5 -> N5 + N5 -> N6 + N5 -> N7 + N6 -> Null + N6 -> N0 + N6 -> N1 + N6 -> N2 + N6 -> N3 + N6 -> N4 + N6 -> N5 + N6 -> N6 + N6 -> N7 + N6 -> N8 + N7 -> Null + N7 -> N0 + N7 -> N1 + N7 -> N2 + N7 -> N3 + N7 -> N4 + N7 -> N5 + N7 -> N6 + N7 -> N7 + N7 -> N8 + N8 -> Null + N8 -> N0 + N8 -> N1 + N8 -> N2 + N8 -> N3 + N8 -> N4 + N8 -> N5 + N8 -> N6 + N8 -> N7 + N8 -> N8 and all 	n: one TreeNode - (thiz.root).* left + right | { 
(n.left = Null and n.right = Null )}
 ) 
}
 
pred preRepOK [thiz: BinaryTree, root: BinaryTree ->one (TreeNode + Null), left: TreeNode ->one (TreeNode + Null), right: TreeNode ->one (TreeNode + Null), size: BinaryTree ->one Int, element: TreeNode ->one Int] {
(repOK[thiz, root, left, right, size, element] and symmetryBreaking[thiz, root, left, right] ) 
}
 
pred postPredicate [res: boolean] {
res = true 
}
 
pred testPredicate [res: boolean] {
res = true 
}
 
/* action pick*/ 
pred pick [s, s': set TreeNode, e, e': TreeNode] {
(some s and e' in s and s' = s - e' ) 
}
 
pred insert$DYN8 [thiz_0: BinaryTree, root_0, root_1: BinaryTree ->one (TreeNode + Null), left_0, left_1: TreeNode ->one (TreeNode + Null), right_0, right_1: TreeNode ->one (TreeNode + Null), size_0, size_1: BinaryTree ->one Int, element_0: TreeNode ->one Int, newNode_0: one TreeNode] {
some 	current_0, current_1, current_2, current_3, current_4, current_5, current_6, current_7, current_8, current_9, current_10: one TreeNode + Null, 	leaveReached_0, leaveReached_1, leaveReached_2, leaveReached_3, leaveReached_4, leaveReached_5, leaveReached_6, leaveReached_7, leaveReached_8, leaveReached_9, leaveReached_10: one boolean | { 
(newNode_0 !in ((thiz_0.root_0).* left_0 + right_0) and leaveReached_1 = false and current_1 = thiz_0.root_0 and ((eq[thiz_0.size_0, 0] and root_1 = thiz_0 -> newNode_0 and left_1 = left_0 ++ newNode_0 -> Null and right_1 = right_0 ++ newNode_0 -> Null and current_1 = current_10 and leaveReached_1 = leaveReached_10 ) or (not eq[thiz_0.size_0, 0] and ((current_1 = current_10 and leaveReached_1 = leaveReached_10 ) or (leaveReached_1 = false and (((current_1.left_0 = Null or current_1.right_0 = Null ) and leaveReached_2 = true and current_1 = current_2 ) or (not (current_1.left_0 = Null or current_1.right_0 = Null ) and ((lte[#(current_1.left_0).* left_0 + right_0, #(current_1.right_0).* left_0 + right_0] and current_2 = current_1.left_0 ) or (not lte[#(current_1.left_0).* left_0 + right_0, #(current_1.right_0).* left_0 + right_0] and current_2 = current_1.right_0 ) ) and leaveReached_1 = leaveReached_2 ) ) and ((current_2 = current_10 and leaveReached_2 = leaveReached_10 ) or (leaveReached_2 = false and (((current_2.left_0 = Null or current_2.right_0 = Null ) and leaveReached_3 = true and current_2 = current_3 ) or (not (current_2.left_0 = Null or current_2.right_0 = Null ) and ((lte[#(current_2.left_0).* left_0 + right_0, #(current_2.right_0).* left_0 + right_0] and current_3 = current_2.left_0 ) or (not lte[#(current_2.left_0).* left_0 + right_0, #(current_2.right_0).* left_0 + right_0] and current_3 = current_2.right_0 ) ) and leaveReached_2 = leaveReached_3 ) ) and ((current_3 = current_10 and leaveReached_3 = leaveReached_10 ) or (leaveReached_3 = false and (((current_3.left_0 = Null or current_3.right_0 = Null ) and leaveReached_4 = true and current_3 = current_4 ) or (not (current_3.left_0 = Null or current_3.right_0 = Null ) and ((lte[#(current_3.left_0).* left_0 + right_0, #(current_3.right_0).* left_0 + right_0] and current_4 = current_3.left_0 ) or (not lte[#(current_3.left_0).* left_0 + right_0, #(current_3.right_0).* left_0 + right_0] and current_4 = current_3.right_0 ) ) and leaveReached_3 = leaveReached_4 ) ) and ((current_4 = current_10 and leaveReached_4 = leaveReached_10 ) or (leaveReached_4 = false and (((current_4.left_0 = Null or current_4.right_0 = Null ) and leaveReached_5 = true and current_4 = current_5 ) or (not (current_4.left_0 = Null or current_4.right_0 = Null ) and ((lte[#(current_4.left_0).* left_0 + right_0, #(current_4.right_0).* left_0 + right_0] and current_5 = current_4.left_0 ) or (not lte[#(current_4.left_0).* left_0 + right_0, #(current_4.right_0).* left_0 + right_0] and current_5 = current_4.right_0 ) ) and leaveReached_4 = leaveReached_5 ) ) and ((current_5 = current_10 and leaveReached_5 = leaveReached_10 ) or (leaveReached_5 = false and (((current_5.left_0 = Null or current_5.right_0 = Null ) and leaveReached_6 = true and current_5 = current_6 ) or (not (current_5.left_0 = Null or current_5.right_0 = Null ) and ((lte[#(current_5.left_0).* left_0 + right_0, #(current_5.right_0).* left_0 + right_0] and current_6 = current_5.left_0 ) or (not lte[#(current_5.left_0).* left_0 + right_0, #(current_5.right_0).* left_0 + right_0] and current_6 = current_5.right_0 ) ) and leaveReached_5 = leaveReached_6 ) ) and ((current_6 = current_10 and leaveReached_6 = leaveReached_10 ) or (leaveReached_6 = false and (((current_6.left_0 = Null or current_6.right_0 = Null ) and leaveReached_7 = true and current_6 = current_7 ) or (not (current_6.left_0 = Null or current_6.right_0 = Null ) and ((lte[#(current_6.left_0).* left_0 + right_0, #(current_6.right_0).* left_0 + right_0] and current_7 = current_6.left_0 ) or (not lte[#(current_6.left_0).* left_0 + right_0, #(current_6.right_0).* left_0 + right_0] and current_7 = current_6.right_0 ) ) and leaveReached_6 = leaveReached_7 ) ) and ((current_7 = current_10 and leaveReached_7 = leaveReached_10 ) or (leaveReached_7 = false and (((current_7.left_0 = Null or current_7.right_0 = Null ) and leaveReached_8 = true and current_7 = current_8 ) or (not (current_7.left_0 = Null or current_7.right_0 = Null ) and ((lte[#(current_7.left_0).* left_0 + right_0, #(current_7.right_0).* left_0 + right_0] and current_8 = current_7.left_0 ) or (not lte[#(current_7.left_0).* left_0 + right_0, #(current_7.right_0).* left_0 + right_0] and current_8 = current_7.right_0 ) ) and leaveReached_7 = leaveReached_8 ) ) and ((current_8 = current_10 and leaveReached_8 = leaveReached_10 ) or (leaveReached_8 = false and (((current_8.left_0 = Null or current_8.right_0 = Null ) and leaveReached_9 = true and current_8 = current_9 ) or (not (current_8.left_0 = Null or current_8.right_0 = Null ) and ((lte[#(current_8.left_0).* left_0 + right_0, #(current_8.right_0).* left_0 + right_0] and current_9 = current_8.left_0 ) or (not lte[#(current_8.left_0).* left_0 + right_0, #(current_8.right_0).* left_0 + right_0] and current_9 = current_8.right_0 ) ) and leaveReached_8 = leaveReached_9 ) ) and ((current_9 = current_10 and leaveReached_9 = leaveReached_10 ) or (leaveReached_9 = false and (((current_9.left_0 = Null or current_9.right_0 = Null ) and leaveReached_10 = true and current_9 = current_10 ) or (not (current_9.left_0 = Null or current_9.right_0 = Null ) and ((lte[#(current_9.left_0).* left_0 + right_0, #(current_9.right_0).* left_0 + right_0] and current_10 = current_9.left_0 ) or (not lte[#(current_9.left_0).* left_0 + right_0, #(current_9.right_0).* left_0 + right_0] and current_10 = current_9.right_0 ) ) and leaveReached_9 = leaveReached_10 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) and not leaveReached_10 = false and ((current_10.left_0 = Null and left_1 = left_0 ++ (current_10 -> newNode_0 + newNode_0 -> Null) and right_1 = right_0 ++ newNode_0 -> Null ) or (not current_10.left_0 = Null and left_1 = left_0 ++ newNode_0 -> Null and right_1 = right_0 ++ (current_10 -> newNode_0 + newNode_0 -> Null) ) ) and root_0 = root_1 ) ) and size_1 = thiz_0 -> add[thiz_0.size_0, 1] )}
 
}
 
pred insert$DYN9 [thiz_0: BinaryTree, root_0, root_1: BinaryTree ->one (TreeNode + Null), left_0, left_1: TreeNode ->one (TreeNode + Null), right_0, right_1: TreeNode ->one (TreeNode + Null), size_0, size_1: BinaryTree ->one Int, element_0: TreeNode ->one Int, newNode_0: one TreeNode] {
some 	current_0, current_1, current_2, current_3, current_4, current_5, current_6, current_7, current_8, current_9, current_10: one TreeNode + Null, 	leaveReached_0, leaveReached_1, leaveReached_2, leaveReached_3, leaveReached_4, leaveReached_5, leaveReached_6, leaveReached_7, leaveReached_8, leaveReached_9, leaveReached_10: one boolean | { 
(newNode_0 !in ((thiz_0.root_0).* left_0 + right_0) and leaveReached_1 = false and current_1 = thiz_0.root_0 and ((eq[thiz_0.size_0, 0] and root_1 = thiz_0 -> newNode_0 and left_1 = left_0 ++ newNode_0 -> Null and right_1 = right_0 ++ newNode_0 -> Null and current_1 = current_10 and leaveReached_1 = leaveReached_10 ) or (not eq[thiz_0.size_0, 0] and ((current_1 = current_10 and leaveReached_1 = leaveReached_10 ) or (leaveReached_1 = false and (((current_1.left_0 = Null or current_1.right_0 = Null ) and leaveReached_2 = true and current_1 = current_2 ) or (not (current_1.left_0 = Null or current_1.right_0 = Null ) and ((lte[#(current_1.left_0).* left_0 + right_0, #(current_1.right_0).* left_0 + right_0] and current_2 = current_1.left_0 ) or (not lte[#(current_1.left_0).* left_0 + right_0, #(current_1.right_0).* left_0 + right_0] and current_2 = current_1.right_0 ) ) and leaveReached_1 = leaveReached_2 ) ) and ((current_2 = current_10 and leaveReached_2 = leaveReached_10 ) or (leaveReached_2 = false and (((current_2.left_0 = Null or current_2.right_0 = Null ) and leaveReached_3 = true and current_2 = current_3 ) or (not (current_2.left_0 = Null or current_2.right_0 = Null ) and ((lte[#(current_2.left_0).* left_0 + right_0, #(current_2.right_0).* left_0 + right_0] and current_3 = current_2.left_0 ) or (not lte[#(current_2.left_0).* left_0 + right_0, #(current_2.right_0).* left_0 + right_0] and current_3 = current_2.right_0 ) ) and leaveReached_2 = leaveReached_3 ) ) and ((current_3 = current_10 and leaveReached_3 = leaveReached_10 ) or (leaveReached_3 = false and (((current_3.left_0 = Null or current_3.right_0 = Null ) and leaveReached_4 = true and current_3 = current_4 ) or (not (current_3.left_0 = Null or current_3.right_0 = Null ) and ((lte[#(current_3.left_0).* left_0 + right_0, #(current_3.right_0).* left_0 + right_0] and current_4 = current_3.left_0 ) or (not lte[#(current_3.left_0).* left_0 + right_0, #(current_3.right_0).* left_0 + right_0] and current_4 = current_3.right_0 ) ) and leaveReached_3 = leaveReached_4 ) ) and ((current_4 = current_10 and leaveReached_4 = leaveReached_10 ) or (leaveReached_4 = false and (((current_4.left_0 = Null or current_4.right_0 = Null ) and leaveReached_5 = true and current_4 = current_5 ) or (not (current_4.left_0 = Null or current_4.right_0 = Null ) and ((lte[#(current_4.left_0).* left_0 + right_0, #(current_4.right_0).* left_0 + right_0] and current_5 = current_4.left_0 ) or (not lte[#(current_4.left_0).* left_0 + right_0, #(current_4.right_0).* left_0 + right_0] and current_5 = current_4.right_0 ) ) and leaveReached_4 = leaveReached_5 ) ) and ((current_5 = current_10 and leaveReached_5 = leaveReached_10 ) or (leaveReached_5 = false and (((current_5.left_0 = Null or current_5.right_0 = Null ) and leaveReached_6 = true and current_5 = current_6 ) or (not (current_5.left_0 = Null or current_5.right_0 = Null ) and ((lte[#(current_5.left_0).* left_0 + right_0, #(current_5.right_0).* left_0 + right_0] and current_6 = current_5.left_0 ) or (not lte[#(current_5.left_0).* left_0 + right_0, #(current_5.right_0).* left_0 + right_0] and current_6 = current_5.right_0 ) ) and leaveReached_5 = leaveReached_6 ) ) and ((current_6 = current_10 and leaveReached_6 = leaveReached_10 ) or (leaveReached_6 = false and (((current_6.left_0 = Null or current_6.right_0 = Null ) and leaveReached_7 = true and current_6 = current_7 ) or (not (current_6.left_0 = Null or current_6.right_0 = Null ) and ((lte[#(current_6.left_0).* left_0 + right_0, #(current_6.right_0).* left_0 + right_0] and current_7 = current_6.left_0 ) or (not lte[#(current_6.left_0).* left_0 + right_0, #(current_6.right_0).* left_0 + right_0] and current_7 = current_6.right_0 ) ) and leaveReached_6 = leaveReached_7 ) ) and ((current_7 = current_10 and leaveReached_7 = leaveReached_10 ) or (leaveReached_7 = false and (((current_7.left_0 = Null or current_7.right_0 = Null ) and leaveReached_8 = true and current_7 = current_8 ) or (not (current_7.left_0 = Null or current_7.right_0 = Null ) and ((lte[#(current_7.left_0).* left_0 + right_0, #(current_7.right_0).* left_0 + right_0] and current_8 = current_7.left_0 ) or (not lte[#(current_7.left_0).* left_0 + right_0, #(current_7.right_0).* left_0 + right_0] and current_8 = current_7.right_0 ) ) and leaveReached_7 = leaveReached_8 ) ) and ((current_8 = current_10 and leaveReached_8 = leaveReached_10 ) or (leaveReached_8 = false and (((current_8.left_0 = Null or current_8.right_0 = Null ) and leaveReached_9 = true and current_8 = current_9 ) or (not (current_8.left_0 = Null or current_8.right_0 = Null ) and ((lte[#(current_8.left_0).* left_0 + right_0, #(current_8.right_0).* left_0 + right_0] and current_9 = current_8.left_0 ) or (not lte[#(current_8.left_0).* left_0 + right_0, #(current_8.right_0).* left_0 + right_0] and current_9 = current_8.right_0 ) ) and leaveReached_8 = leaveReached_9 ) ) and ((current_9 = current_10 and leaveReached_9 = leaveReached_10 ) or (leaveReached_9 = false and (((current_9.left_0 = Null or current_9.right_0 = Null ) and leaveReached_10 = true and current_9 = current_10 ) or (not (current_9.left_0 = Null or current_9.right_0 = Null ) and ((lte[#(current_9.left_0).* left_0 + right_0, #(current_9.right_0).* left_0 + right_0] and current_10 = current_9.left_0 ) or (not lte[#(current_9.left_0).* left_0 + right_0, #(current_9.right_0).* left_0 + right_0] and current_10 = current_9.right_0 ) ) and leaveReached_9 = leaveReached_10 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) and not leaveReached_10 = false and ((current_10.left_0 = Null and left_1 = left_0 ++ (current_10 -> newNode_0 + newNode_0 -> Null) and right_1 = right_0 ++ newNode_0 -> Null ) or (not current_10.left_0 = Null and left_1 = left_0 ++ newNode_0 -> Null and right_1 = right_0 ++ (current_10 -> newNode_0 + newNode_0 -> Null) ) ) and root_0 = root_1 ) ) and size_1 = thiz_0 -> add[thiz_0.size_0, 1] )}
 
}
 
pred repOKOK$DYN10 [thiz_0: BinaryTree, root_0: BinaryTree ->one (TreeNode + Null), left_0: TreeNode ->one (TreeNode + Null), right_0: TreeNode ->one (TreeNode + Null), size_0: BinaryTree ->one Int, element_0: TreeNode ->one Int, result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11, result_12, result_13, result_14, result_15, result_16, result_17, result_18, result_19, result_20: boolean] {
some 	current_0, current_1, current_2, current_3, current_4, current_5, current_6, current_7, current_8, current_9: one TreeNode + Null, 	visited_0, visited_1, visited_2, visited_3, visited_4, visited_5, visited_6, visited_7, visited_8, visited_9, visited_10, visited_11, visited_12, visited_13, visited_14, visited_15, visited_16, visited_17, visited_18, visited_19: set TreeNode, 	workset_0, workset_1, workset_2, workset_3, workset_4, workset_5, workset_6, workset_7, workset_8, workset_9, workset_10, workset_11, workset_12, workset_13, workset_14, workset_15, workset_16, workset_17, workset_18, workset_19, workset_20, workset_21, workset_22, workset_23, workset_24, workset_25, workset_26, workset_27, workset_28: set TreeNode | { 
(workset_1 = thiz_0.root_0 and visited_1 = thiz_0.root_0 and ((thiz_0.root_0 = Null and ((thiz_0.size_0 = 0 and result_1 = true ) or (not thiz_0.size_0 = 0 and result_1 = false ) ) and result_1 = result_20 and current_0 = current_9 and visited_1 = visited_19 and workset_1 = workset_28 ) or (not thiz_0.root_0 = Null and result_1 = true and ((result_1 = result_19 and current_0 = current_9 and visited_1 = visited_19 and workset_1 = workset_28 ) or (result_1 = true and some workset_1 and pick[workset_1, workset_2, current_0, current_1] and (((current_1.left_0) != Null and ((current_1.left_0 in visited_1 and result_2 = false and visited_1 = visited_2 and workset_2 = workset_3 ) or (not current_1.left_0 in visited_1 and visited_2 = visited_1 + current_1.left_0 and workset_3 = workset_2 + current_1.left_0 and result_1 = result_2 ) ) ) or (not (current_1.left_0) != Null and result_1 = result_2 and visited_1 = visited_2 and workset_2 = workset_3 ) ) and ((result_2 = true and (current_1.right_0) != Null and ((current_1.right_0 in visited_2 and result_3 = false and visited_2 = visited_3 and workset_3 = workset_4 ) or (not current_1.right_0 in visited_2 and visited_3 = visited_2 + current_1.right_0 and workset_4 = workset_3 + current_1.right_0 and result_2 = result_3 ) ) ) or (not (result_2 = true and (current_1.right_0) != Null ) and result_2 = result_3 and visited_2 = visited_3 and workset_3 = workset_4 ) ) and ((result_3 = result_19 and current_1 = current_9 and visited_3 = visited_19 and workset_4 = workset_28 ) or (result_3 = true and some workset_4 and pick[workset_4, workset_5, current_1, current_2] and (((current_2.left_0) != Null and ((current_2.left_0 in visited_3 and result_4 = false and visited_3 = visited_4 and workset_5 = workset_6 ) or (not current_2.left_0 in visited_3 and visited_4 = visited_3 + current_2.left_0 and workset_6 = workset_5 + current_2.left_0 and result_3 = result_4 ) ) ) or (not (current_2.left_0) != Null and result_3 = result_4 and visited_3 = visited_4 and workset_5 = workset_6 ) ) and ((result_4 = true and (current_2.right_0) != Null and ((current_2.right_0 in visited_4 and result_5 = false and visited_4 = visited_5 and workset_6 = workset_7 ) or (not current_2.right_0 in visited_4 and visited_5 = visited_4 + current_2.right_0 and workset_7 = workset_6 + current_2.right_0 and result_4 = result_5 ) ) ) or (not (result_4 = true and (current_2.right_0) != Null ) and result_4 = result_5 and visited_4 = visited_5 and workset_6 = workset_7 ) ) and ((result_5 = result_19 and current_2 = current_9 and visited_5 = visited_19 and workset_7 = workset_28 ) or (result_5 = true and some workset_7 and pick[workset_7, workset_8, current_2, current_3] and (((current_3.left_0) != Null and ((current_3.left_0 in visited_5 and result_6 = false and visited_5 = visited_6 and workset_8 = workset_9 ) or (not current_3.left_0 in visited_5 and visited_6 = visited_5 + current_3.left_0 and workset_9 = workset_8 + current_3.left_0 and result_5 = result_6 ) ) ) or (not (current_3.left_0) != Null and result_5 = result_6 and visited_5 = visited_6 and workset_8 = workset_9 ) ) and ((result_6 = true and (current_3.right_0) != Null and ((current_3.right_0 in visited_6 and result_7 = false and visited_6 = visited_7 and workset_9 = workset_10 ) or (not current_3.right_0 in visited_6 and visited_7 = visited_6 + current_3.right_0 and workset_10 = workset_9 + current_3.right_0 and result_6 = result_7 ) ) ) or (not (result_6 = true and (current_3.right_0) != Null ) and result_6 = result_7 and visited_6 = visited_7 and workset_9 = workset_10 ) ) and ((result_7 = result_19 and current_3 = current_9 and visited_7 = visited_19 and workset_10 = workset_28 ) or (result_7 = true and some workset_10 and pick[workset_10, workset_11, current_3, current_4] and (((current_4.left_0) != Null and ((current_4.left_0 in visited_7 and result_8 = false and visited_7 = visited_8 and workset_11 = workset_12 ) or (not current_4.left_0 in visited_7 and visited_8 = visited_7 + current_4.left_0 and workset_12 = workset_11 + current_4.left_0 and result_7 = result_8 ) ) ) or (not (current_4.left_0) != Null and result_7 = result_8 and visited_7 = visited_8 and workset_11 = workset_12 ) ) and ((result_8 = true and (current_4.right_0) != Null and ((current_4.right_0 in visited_8 and result_9 = false and visited_8 = visited_9 and workset_12 = workset_13 ) or (not current_4.right_0 in visited_8 and visited_9 = visited_8 + current_4.right_0 and workset_13 = workset_12 + current_4.right_0 and result_8 = result_9 ) ) ) or (not (result_8 = true and (current_4.right_0) != Null ) and result_8 = result_9 and visited_8 = visited_9 and workset_12 = workset_13 ) ) and ((result_9 = result_19 and current_4 = current_9 and visited_9 = visited_19 and workset_13 = workset_28 ) or (result_9 = true and some workset_13 and pick[workset_13, workset_14, current_4, current_5] and (((current_5.left_0) != Null and ((current_5.left_0 in visited_9 and result_10 = false and visited_9 = visited_10 and workset_14 = workset_15 ) or (not current_5.left_0 in visited_9 and visited_10 = visited_9 + current_5.left_0 and workset_15 = workset_14 + current_5.left_0 and result_9 = result_10 ) ) ) or (not (current_5.left_0) != Null and result_9 = result_10 and visited_9 = visited_10 and workset_14 = workset_15 ) ) and ((result_10 = true and (current_5.right_0) != Null and ((current_5.right_0 in visited_10 and result_11 = false and visited_10 = visited_11 and workset_15 = workset_16 ) or (not current_5.right_0 in visited_10 and visited_11 = visited_10 + current_5.right_0 and workset_16 = workset_15 + current_5.right_0 and result_10 = result_11 ) ) ) or (not (result_10 = true and (current_5.right_0) != Null ) and result_10 = result_11 and visited_10 = visited_11 and workset_15 = workset_16 ) ) and ((result_11 = result_19 and current_5 = current_9 and visited_11 = visited_19 and workset_16 = workset_28 ) or (result_11 = true and some workset_16 and pick[workset_16, workset_17, current_5, current_6] and (((current_6.left_0) != Null and ((current_6.left_0 in visited_11 and result_12 = false and visited_11 = visited_12 and workset_17 = workset_18 ) or (not current_6.left_0 in visited_11 and visited_12 = visited_11 + current_6.left_0 and workset_18 = workset_17 + current_6.left_0 and result_11 = result_12 ) ) ) or (not (current_6.left_0) != Null and result_11 = result_12 and visited_11 = visited_12 and workset_17 = workset_18 ) ) and ((result_12 = true and (current_6.right_0) != Null and ((current_6.right_0 in visited_12 and result_13 = false and visited_12 = visited_13 and workset_18 = workset_19 ) or (not current_6.right_0 in visited_12 and visited_13 = visited_12 + current_6.right_0 and workset_19 = workset_18 + current_6.right_0 and result_12 = result_13 ) ) ) or (not (result_12 = true and (current_6.right_0) != Null ) and result_12 = result_13 and visited_12 = visited_13 and workset_18 = workset_19 ) ) and ((result_13 = result_19 and current_6 = current_9 and visited_13 = visited_19 and workset_19 = workset_28 ) or (result_13 = true and some workset_19 and pick[workset_19, workset_20, current_6, current_7] and (((current_7.left_0) != Null and ((current_7.left_0 in visited_13 and result_14 = false and visited_13 = visited_14 and workset_20 = workset_21 ) or (not current_7.left_0 in visited_13 and visited_14 = visited_13 + current_7.left_0 and workset_21 = workset_20 + current_7.left_0 and result_13 = result_14 ) ) ) or (not (current_7.left_0) != Null and result_13 = result_14 and visited_13 = visited_14 and workset_20 = workset_21 ) ) and ((result_14 = true and (current_7.right_0) != Null and ((current_7.right_0 in visited_14 and result_15 = false and visited_14 = visited_15 and workset_21 = workset_22 ) or (not current_7.right_0 in visited_14 and visited_15 = visited_14 + current_7.right_0 and workset_22 = workset_21 + current_7.right_0 and result_14 = result_15 ) ) ) or (not (result_14 = true and (current_7.right_0) != Null ) and result_14 = result_15 and visited_14 = visited_15 and workset_21 = workset_22 ) ) and ((result_15 = result_19 and current_7 = current_9 and visited_15 = visited_19 and workset_22 = workset_28 ) or (result_15 = true and some workset_22 and pick[workset_22, workset_23, current_7, current_8] and (((current_8.left_0) != Null and ((current_8.left_0 in visited_15 and result_16 = false and visited_15 = visited_16 and workset_23 = workset_24 ) or (not current_8.left_0 in visited_15 and visited_16 = visited_15 + current_8.left_0 and workset_24 = workset_23 + current_8.left_0 and result_15 = result_16 ) ) ) or (not (current_8.left_0) != Null and result_15 = result_16 and visited_15 = visited_16 and workset_23 = workset_24 ) ) and ((result_16 = true and (current_8.right_0) != Null and ((current_8.right_0 in visited_16 and result_17 = false and visited_16 = visited_17 and workset_24 = workset_25 ) or (not current_8.right_0 in visited_16 and visited_17 = visited_16 + current_8.right_0 and workset_25 = workset_24 + current_8.right_0 and result_16 = result_17 ) ) ) or (not (result_16 = true and (current_8.right_0) != Null ) and result_16 = result_17 and visited_16 = visited_17 and workset_24 = workset_25 ) ) and ((result_17 = result_19 and current_8 = current_9 and visited_17 = visited_19 and workset_25 = workset_28 ) or (result_17 = true and some workset_25 and pick[workset_25, workset_26, current_8, current_9] and (((current_9.left_0) != Null and ((current_9.left_0 in visited_17 and result_18 = false and visited_17 = visited_18 and workset_26 = workset_27 ) or (not current_9.left_0 in visited_17 and visited_18 = visited_17 + current_9.left_0 and workset_27 = workset_26 + current_9.left_0 and result_17 = result_18 ) ) ) or (not (current_9.left_0) != Null and result_17 = result_18 and visited_17 = visited_18 and workset_26 = workset_27 ) ) and ((result_18 = true and (current_9.right_0) != Null and ((current_9.right_0 in visited_18 and result_19 = false and visited_18 = visited_19 and workset_27 = workset_28 ) or (not current_9.right_0 in visited_18 and visited_19 = visited_18 + current_9.right_0 and workset_28 = workset_27 + current_9.right_0 and result_18 = result_19 ) ) ) or (not (result_18 = true and (current_9.right_0) != Null ) and result_18 = result_19 and visited_18 = visited_19 and workset_27 = workset_28 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) and not (result_19 = true and some workset_28 ) and ((result_19 = true and (#visited_19) != (thiz_0.size_0) and result_20 = false ) or (not (result_19 = true and (#visited_19) != (thiz_0.size_0) ) and result_19 = result_20 ) ) ) ) )}
 
}
 
pred insertOKOK$DYN$DYN11 [thiz_0: BinaryTree, root_0, root_1: BinaryTree ->one (TreeNode + Null), left_0, left_1: TreeNode ->one (TreeNode + Null), right_0, right_1: TreeNode ->one (TreeNode + Null), size_0, size_1: BinaryTree ->one Int, element_0: TreeNode ->one Int, newNode_0: one TreeNode, res_0, res_1, res_2, res_3, res_4, res_5, res_6, res_7, res_8, res_9, res_10, res_11, res_12, res_13, res_14, res_15, res_16, res_17, res_18, res_19, res_20, res_21, res_22, res_23, res_24, res_25, res_26, res_27, res_28, res_29, res_30, res_31, res_32, res_33, res_34, res_35, res_36, res_37, res_38, res_39, res_40: boolean] {
(repOKOK$DYN10[thiz_0, root_0, left_0, right_0, size_0, element_0, res_0, res_1, res_2, res_3, res_4, res_5, res_6, res_7, res_8, res_9, res_10, res_11, res_12, res_13, res_14, res_15, res_16, res_17, res_18, res_19, res_20] and testPredicate[res_20] and insert$DYN9[thiz_0, root_0, root_1, left_0, left_1, right_0, right_1, size_0, size_1, element_0, newNode_0] and repOKOK$DYN10[thiz_0, root_1, left_1, right_1, size_1, element_0, res_20, res_21, res_22, res_23, res_24, res_25, res_26, res_27, res_28, res_29, res_30, res_31, res_32, res_33, res_34, res_35, res_36, res_37, res_38, res_39, res_40] ) 
}
 
assert insertOK$DYN0{
all 	thiz_0: one BinaryTree, 	root_0, root_1: BinaryTree ->one (TreeNode + Null), 	left_0, left_1: TreeNode ->one (TreeNode + Null), 	right_1, right_0: TreeNode ->one (TreeNode + Null), 	size_1, size_0: BinaryTree ->one Int, 	element_0: TreeNode ->one Int, 	newNode_0: one TreeNode | { 
(preRepOK[thiz_0, root_0, left_0, right_0, size_0, element_0] and insert$DYN8[thiz_0, root_0, root_1, left_0, left_1, right_0, right_1, size_0, size_1, element_0, newNode_0] ) => repOK[thiz_0, root_1, left_1, right_1, size_1, element_0]}

}

assert insertOKOK$DYN1{
all 	thiz_0: one BinaryTree, 	root_0, root_1: BinaryTree ->one (TreeNode + Null), 	left_0, left_1: TreeNode ->one (TreeNode + Null), 	right_1, right_0: TreeNode ->one (TreeNode + Null), 	size_1, size_0: BinaryTree ->one Int, 	element_0: TreeNode ->one Int, 	newNode_0: one TreeNode, 	res_28, res_27, res_29, res_24, res_23, res_26, res_25, res_31, res_30, res_11, res_33, res_10, res_32, res_5, res_6, res_3, res_4, res_1, res_2, res_0, res_17, res_39, res_16, res_38, res_19, res_18, res_9, res_13, res_35, res_12, res_34, res_7, res_15, res_37, res_8, res_14, res_36, res_20, res_22, res_21, res_40: one boolean | { 
(symmetryBreaking[thiz_0, root_0, left_0, right_0] and insertOKOK$DYN$DYN11[thiz_0, root_0, root_1, left_0, left_1, right_0, right_1, size_0, size_1, element_0, newNode_0, res_0, res_1, res_2, res_3, res_4, res_5, res_6, res_7, res_8, res_9, res_10, res_11, res_12, res_13, res_14, res_15, res_16, res_17, res_18, res_19, res_20, res_21, res_22, res_23, res_24, res_25, res_26, res_27, res_28, res_29, res_30, res_31, res_32, res_33, res_34, res_35, res_36, res_37, res_38, res_39, res_40] ) => postPredicate[res_40]}

}

check insertOK$DYN0 for 9 but 5 int
check insertOKOK$DYN1 for 9 but 5 int