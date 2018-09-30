module bstreeintvar

open Integer5
open util/integer

one sig BSTreeIntVar{}

abstract sig BSTreeIntVarNode{}

one sig null {}

one sig QF {
	thiz_0 : one BSTreeIntVar,
	root_0 : BSTreeIntVar -> one (BSTreeIntVarNode + null),

	fleft_0 : BSTreeIntVarNode -> lone (BSTreeIntVarNode + null),
	bleft_0 : BSTreeIntVarNode -> lone (BSTreeIntVarNode),

	fright_0 : BSTreeIntVarNode -> lone (BSTreeIntVarNode + null),
	bright_0 : BSTreeIntVarNode -> lone (BSTreeIntVarNode),

	key_0 : BSTreeIntVarNode -> one (JavaPrimitiveIntegerValue+null),
  size_0:  BSTreeIntVar -> one JavaPrimitiveIntegerValue    

}



pred repOK [] {
  let thiz  = QF.thiz_0,
      root  = QF.root_0,
      left  = QF.fleft_0 + QF.bleft_0,
      right = QF.fright_0 + QF.bright_0,
      size  = QF.size_0,
      key   = QF.key_0  
      | {
      some result_0, result_1, result_2, result_3, result_4, result_5, result_6, result_7, result_8, result_9, result_10, result_11, result_12, result_13, result_14, result_15, result_16, result_17, result_18, result_19, result_20: boolean | some  current_0, current_1, current_2, current_3, current_4, current_5, current_6, current_7, current_8, current_9: one BSTreeIntVarNode + null,  visited_0, visited_1, visited_2, visited_3, visited_4, visited_5, visited_6, visited_7, visited_8, visited_9, visited_10, visited_11, visited_12, visited_13, visited_14, visited_15, visited_16, visited_17, visited_18, visited_19: set BSTreeIntVarNode,   workset_0, workset_1, workset_2, workset_3, workset_4, workset_5, workset_6, workset_7, workset_8, workset_9, workset_10, workset_11, workset_12, workset_13, workset_14, workset_15, workset_16, workset_17, workset_18, workset_19, workset_20, workset_21, workset_22, workset_23, workset_24, workset_25, workset_26, workset_27, workset_28: set BSTreeIntVarNode | { 
(workset_1 = thiz.root and visited_1 = thiz.root and ((thiz.root = null and ((thiz.size = 0 and result_1 = true ) or (not thiz.size = 0 and result_1 = false ) ) and result_1 = result_20 and current_0 = current_9 and visited_1 = visited_19 and workset_1 = workset_28 ) or (not thiz.root = null and result_1 = true and ((result_1 = result_19 and current_0 = current_9 and visited_1 = visited_19 and workset_1 = workset_28 ) or (result_1 = true and some workset_1 and pick[workset_1, workset_2, current_0, current_1] and (((current_1.left) != null and ((current_1.left in visited_1 and result_2 = false and visited_1 = visited_2 and workset_2 = workset_3 ) or (not current_1.left in visited_1 and visited_2 = visited_1 + current_1.left and workset_3 = workset_2 + current_1.left and result_1 = result_2 ) ) ) or (not (current_1.left) != null and result_1 = result_2 and visited_1 = visited_2 and workset_2 = workset_3 ) ) and ((result_2 = true and (current_1.right) != null and ((current_1.right in visited_2 and result_3 = false and visited_2 = visited_3 and workset_3 = workset_4 ) or (not current_1.right in visited_2 and visited_3 = visited_2 + current_1.right and workset_4 = workset_3 + current_1.right and result_2 = result_3 ) ) ) or (not (result_2 = true and (current_1.right) != null ) and result_2 = result_3 and visited_2 = visited_3 and workset_3 = workset_4 ) ) and ((result_3 = result_19 and current_1 = current_9 and visited_3 = visited_19 and workset_4 = workset_28 ) or (result_3 = true and some workset_4 and pick[workset_4, workset_5, current_1, current_2] and (((current_2.left) != null and ((current_2.left in visited_3 and result_4 = false and visited_3 = visited_4 and workset_5 = workset_6 ) or (not current_2.left in visited_3 and visited_4 = visited_3 + current_2.left and workset_6 = workset_5 + current_2.left and result_3 = result_4 ) ) ) or (not (current_2.left) != null and result_3 = result_4 and visited_3 = visited_4 and workset_5 = workset_6 ) ) and ((result_4 = true and (current_2.right) != null and ((current_2.right in visited_4 and result_5 = false and visited_4 = visited_5 and workset_6 = workset_7 ) or (not current_2.right in visited_4 and visited_5 = visited_4 + current_2.right and workset_7 = workset_6 + current_2.right and result_4 = result_5 ) ) ) or (not (result_4 = true and (current_2.right) != null ) and result_4 = result_5 and visited_4 = visited_5 and workset_6 = workset_7 ) ) and ((result_5 = result_19 and current_2 = current_9 and visited_5 = visited_19 and workset_7 = workset_28 ) or (result_5 = true and some workset_7 and pick[workset_7, workset_8, current_2, current_3] and (((current_3.left) != null and ((current_3.left in visited_5 and result_6 = false and visited_5 = visited_6 and workset_8 = workset_9 ) or (not current_3.left in visited_5 and visited_6 = visited_5 + current_3.left and workset_9 = workset_8 + current_3.left and result_5 = result_6 ) ) ) or (not (current_3.left) != null and result_5 = result_6 and visited_5 = visited_6 and workset_8 = workset_9 ) ) and ((result_6 = true and (current_3.right) != null and ((current_3.right in visited_6 and result_7 = false and visited_6 = visited_7 and workset_9 = workset_10 ) or (not current_3.right in visited_6 and visited_7 = visited_6 + current_3.right and workset_10 = workset_9 + current_3.right and result_6 = result_7 ) ) ) or (not (result_6 = true and (current_3.right) != null ) and result_6 = result_7 and visited_6 = visited_7 and workset_9 = workset_10 ) ) and ((result_7 = result_19 and current_3 = current_9 and visited_7 = visited_19 and workset_10 = workset_28 ) or (result_7 = true and some workset_10 and pick[workset_10, workset_11, current_3, current_4] and (((current_4.left) != null and ((current_4.left in visited_7 and result_8 = false and visited_7 = visited_8 and workset_11 = workset_12 ) or (not current_4.left in visited_7 and visited_8 = visited_7 + current_4.left and workset_12 = workset_11 + current_4.left and result_7 = result_8 ) ) ) or (not (current_4.left) != null and result_7 = result_8 and visited_7 = visited_8 and workset_11 = workset_12 ) ) and ((result_8 = true and (current_4.right) != null and ((current_4.right in visited_8 and result_9 = false and visited_8 = visited_9 and workset_12 = workset_13 ) or (not current_4.right in visited_8 and visited_9 = visited_8 + current_4.right and workset_13 = workset_12 + current_4.right and result_8 = result_9 ) ) ) or (not (result_8 = true and (current_4.right) != null ) and result_8 = result_9 and visited_8 = visited_9 and workset_12 = workset_13 ) ) and ((result_9 = result_19 and current_4 = current_9 and visited_9 = visited_19 and workset_13 = workset_28 ) or (result_9 = true and some workset_13 and pick[workset_13, workset_14, current_4, current_5] and (((current_5.left) != null and ((current_5.left in visited_9 and result_10 = false and visited_9 = visited_10 and workset_14 = workset_15 ) or (not current_5.left in visited_9 and visited_10 = visited_9 + current_5.left and workset_15 = workset_14 + current_5.left and result_9 = result_10 ) ) ) or (not (current_5.left) != null and result_9 = result_10 and visited_9 = visited_10 and workset_14 = workset_15 ) ) and ((result_10 = true and (current_5.right) != null and ((current_5.right in visited_10 and result_11 = false and visited_10 = visited_11 and workset_15 = workset_16 ) or (not current_5.right in visited_10 and visited_11 = visited_10 + current_5.right and workset_16 = workset_15 + current_5.right and result_10 = result_11 ) ) ) or (not (result_10 = true and (current_5.right) != null ) and result_10 = result_11 and visited_10 = visited_11 and workset_15 = workset_16 ) ) and ((result_11 = result_19 and current_5 = current_9 and visited_11 = visited_19 and workset_16 = workset_28 ) or (result_11 = true and some workset_16 and pick[workset_16, workset_17, current_5, current_6] and (((current_6.left) != null and ((current_6.left in visited_11 and result_12 = false and visited_11 = visited_12 and workset_17 = workset_18 ) or (not current_6.left in visited_11 and visited_12 = visited_11 + current_6.left and workset_18 = workset_17 + current_6.left and result_11 = result_12 ) ) ) or (not (current_6.left) != null and result_11 = result_12 and visited_11 = visited_12 and workset_17 = workset_18 ) ) and ((result_12 = true and (current_6.right) != null and ((current_6.right in visited_12 and result_13 = false and visited_12 = visited_13 and workset_18 = workset_19 ) or (not current_6.right in visited_12 and visited_13 = visited_12 + current_6.right and workset_19 = workset_18 + current_6.right and result_12 = result_13 ) ) ) or (not (result_12 = true and (current_6.right) != null ) and result_12 = result_13 and visited_12 = visited_13 and workset_18 = workset_19 ) ) and ((result_13 = result_19 and current_6 = current_9 and visited_13 = visited_19 and workset_19 = workset_28 ) or (result_13 = true and some workset_19 and pick[workset_19, workset_20, current_6, current_7] and (((current_7.left) != null and ((current_7.left in visited_13 and result_14 = false and visited_13 = visited_14 and workset_20 = workset_21 ) or (not current_7.left in visited_13 and visited_14 = visited_13 + current_7.left and workset_21 = workset_20 + current_7.left and result_13 = result_14 ) ) ) or (not (current_7.left) != null and result_13 = result_14 and visited_13 = visited_14 and workset_20 = workset_21 ) ) and ((result_14 = true and (current_7.right) != null and ((current_7.right in visited_14 and result_15 = false and visited_14 = visited_15 and workset_21 = workset_22 ) or (not current_7.right in visited_14 and visited_15 = visited_14 + current_7.right and workset_22 = workset_21 + current_7.right and result_14 = result_15 ) ) ) or (not (result_14 = true and (current_7.right) != null ) and result_14 = result_15 and visited_14 = visited_15 and workset_21 = workset_22 ) ) and ((result_15 = result_19 and current_7 = current_9 and visited_15 = visited_19 and workset_22 = workset_28 ) or (result_15 = true and some workset_22 and pick[workset_22, workset_23, current_7, current_8] and (((current_8.left) != null and ((current_8.left in visited_15 and result_16 = false and visited_15 = visited_16 and workset_23 = workset_24 ) or (not current_8.left in visited_15 and visited_16 = visited_15 + current_8.left and workset_24 = workset_23 + current_8.left and result_15 = result_16 ) ) ) or (not (current_8.left) != null and result_15 = result_16 and visited_15 = visited_16 and workset_23 = workset_24 ) ) and ((result_16 = true and (current_8.right) != null and ((current_8.right in visited_16 and result_17 = false and visited_16 = visited_17 and workset_24 = workset_25 ) or (not current_8.right in visited_16 and visited_17 = visited_16 + current_8.right and workset_25 = workset_24 + current_8.right and result_16 = result_17 ) ) ) or (not (result_16 = true and (current_8.right) != null ) and result_16 = result_17 and visited_16 = visited_17 and workset_24 = workset_25 ) ) and ((result_17 = result_19 and current_8 = current_9 and visited_17 = visited_19 and workset_25 = workset_28 ) or (result_17 = true and some workset_25 and pick[workset_25, workset_26, current_8, current_9] and (((current_9.left) != null and ((current_9.left in visited_17 and result_18 = false and visited_17 = visited_18 and workset_26 = workset_27 ) or (not current_9.left in visited_17 and visited_18 = visited_17 + current_9.left and workset_27 = workset_26 + current_9.left and result_17 = result_18 ) ) ) or (not (current_9.left) != null and result_17 = result_18 and visited_17 = visited_18 and workset_26 = workset_27 ) ) and ((result_18 = true and (current_9.right) != null and ((current_9.right in visited_18 and result_19 = false and visited_18 = visited_19 and workset_27 = workset_28 ) or (not current_9.right in visited_18 and visited_19 = visited_18 + current_9.right and workset_28 = workset_27 + current_9.right and result_18 = result_19 ) ) ) or (not (result_18 = true and (current_9.right) != null ) and result_18 = result_19 and visited_18 = visited_19 and workset_27 = workset_28 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) and not (result_19 = true and some workset_28 ) and ((result_19 = true and (#visited_19) != (thiz.size) and result_20 = false ) or (not (result_19 = true and (#visited_19) != (thiz.size) ) and result_19 = result_20 ) ) ) ) )}
    }
}

/* action pick*/ 
pred pick [s, s': set BSTreeIntVarNode, e, e': BSTreeIntVarNode] {
(some s and e' in s and s' = s - e' ) 
}

fact {
  repOK[]
}


fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
}

fact { 
let entry=(QF.thiz_0).(QF.root_0),ff1=QF.fleft_0,ff2=QF.fright_0,bf1=QF.bleft_0,bf2=QF.bright_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   N0+N1+N2+N3+N4+N5+N6+N7+N8 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8 = ff2.univ + bf2.univ   

  --forwardIsIndeedForward 
  entry in N0+null and 
  (all n : entry.*(ff1 + ff2) - null | ( 
   node_min[(ff1).n] in node_prevs[n]) and ( 
    node_min[(ff2).n] in node_prevs[n])) and 
  (all disj n1, n2 : entry.*((ff1) + (ff2)) - null | ( 
        (    some ((ff1).n1 + (ff2).n1) and 
            some ((ff1).n2 + (ff2).n2) and 
                node_min[(ff1).n1 + (ff2).n1] in node_prevs[node_min[(ff1).n2 + (ff2).n2]] 
             ) implies n1 in node_prevs[n2] 
   ) 
   and 
     let a = node_min[(ff1).n1 + (ff2).n1] | 
     let b = node_min[(ff1).n2 + (ff2).n2] | 
     (some ((ff1).n1 + (ff2).n1) and a = b and a.(ff1) = n1 and a.(ff2) = n2) implies n2 = n1.node_next[] 
   ) 

  --backwardsIsIndeedBackwards 
   (bf1 in node_relprevs) && (bf2 in node_relprevs) 

  --prefixReachableForward 
    all x : entry.*(ff1 +ff2) -null | node_prevs[x] in entry.*(ff1 + ff2) 

} 
} 


fact fixNonReachable { all n : BSTreeIntVarNode | n !in (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0) implies 
	(
		n.(QF.key_0) = i320 and
		n.(QF.fleft_0) = null and
		n.(QF.fright_0) = null and
		no n.(QF.bleft_0) and
		no n.(QF.bright_0)
	)
}


fun FReach[] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8) {
    (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0) - null
}

one sig N0,N1,N2,N3,N4,N5,N6,N7,N8 extends BSTreeIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true in b00
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false in b02
}



fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->null+N5->N6+N5->N7+N5->N8+N5->null+N6->N7+N6->N8+N6->null+N7->N8+N7->null+N8->null }
fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->null+N5->N6+N5->N7+N5->N8+N5->null+N6->N7+N6->N8+N6->null+N7->N8+N7->null+N8->null }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8 }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->null
}


fact {
	(QF.size_0) in BSTreeIntVar->i320+BSTreeIntVar->i321+BSTreeIntVar->i322+BSTreeIntVar->i323+BSTreeIntVar->i324+BSTreeIntVar->i325+BSTreeIntVar->i326+BSTreeIntVar->i327+BSTreeIntVar->i328+BSTreeIntVar->i329
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8) {
 es - es.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
   +
   N5->(N0+N1+N2+N3+N4)
   +
   N6->(N0+N1+N2+N3+N4+N5)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7)
 )
}


fact {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (no m and size = i320) or 
	  (m = N0 and size = i321) or
	  (m = N1 and size = i322) or
	  (m = N2 and size = i323) or
	  (m = N3 and size = i324) or
	  (m = N4 and size = i325) or
	  (m = N5 and size = i326) or
	  (m = N6 and size = i327) or
	  (m = N7 and size = i328) or
	  (m = N8 and size = i329)
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 BSTreeIntVar, exactly 9 BSTreeIntVarNode, 1 int, exactly 10 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8) {
 N0->N1
 +
 N1->N2
 +
 N2->N3
 +
 N3->N4
 +
 N4->N5
 +
 N5->N6
 +
 N6->N7
 +
 N7->N8
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8) {
 e.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
   +
   N5->(N0+N1+N2+N3+N4)
   +
   N6->(N0+N1+N2+N3+N4+N5)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8) {
 e.(
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
   +
   N5->(N0+N1+N2+N3+N4+N5)
   +
   N6->(N0+N1+N2+N3+N4+N5+N6)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8) {
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
   +
   N5->(N0+N1+N2+N3+N4+N5)
   +
   N6->(N0+N1+N2+N3+N4+N5+N6)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8)
   +
   N2->(N3+N4+N5+N6+N7+N8)
   +
   N3->(N4+N5+N6+N7+N8)
   +
   N4->(N5+N6+N7+N8)
   +
   N5->(N6+N7+N8)
   +
   N6->(N7+N8)
   +
   N7->(N8)
 )
}




