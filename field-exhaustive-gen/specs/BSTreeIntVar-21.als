module bstreeintvar

open Integer6

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
      key   = QF.key_0  
      | {
      ( all n : BSTreeIntVarNode | n in thiz.root.*(left + right) implies
          (
              n.key != null && 
              ( no ( ( (n.left).*(left+right) & (n.right).*(left+right) ) - null ) )
              and
              (n !in n.^(left + right)) -- acyclic
              and
              (all m : BSTreeIntVarNode | m in n.left.*(left + right) implies pred_java_primitive_integer_value_gt[n.key, m.key]) -- left sorted
              and
              (all m : BSTreeIntVarNode | m in n.right.*(left + right) implies pred_java_primitive_integer_value_gt[m.key, n.key]) -- right sorted
           ) 
       ) 
    }
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
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20 = ff2.univ + bf2.univ   

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


fun FReach[] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) {
    (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0) - null
}

one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19,N20 extends BSTreeIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329,i3210,i3211,i3212,i3213,i3214,i3215,i3216,i3217,i3218,i3219,i3220,i3221 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false+i3221->false
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false+i3221->false in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false+i3221->true
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false+i3221->true in b00
	b05 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false in b05
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true+i3221->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true+i3221->true in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false+i3221->false in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true+i3221->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true+i3221->true in b02
}



fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->null+N17->N18+N17->N19+N17->N20+N17->null+N18->N19+N18->N20+N18->null+N19->N20+N19->null+N20->null }
fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->N20+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->N20+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->N20+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->N20+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->N20+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->N20+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->N20+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->N20+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->N20+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->N20+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->N20+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->N20+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->N20+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->N20+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->N20+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->N20+N15->null+N16->N17+N16->N18+N16->N19+N16->N20+N16->null+N17->N18+N17->N19+N17->N20+N17->null+N18->N19+N18->N20+N18->null+N19->N20+N19->null+N20->null }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20 }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19+N20->N0+N20->N1+N20->N2+N20->N3+N20->N4+N20->N5+N20->N6+N20->N7+N20->N8+N20->N9+N20->N10+N20->N11+N20->N12+N20->N13+N20->N14+N20->N15+N20->N16+N20->N17+N20->N18+N20->N19+N20->N20 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->i3219+N0->i3220+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->i3219+N1->i3220+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->i3219+N2->i3220+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->i3219+N3->i3220+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->i3219+N4->i3220+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->i3219+N5->i3220+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->i3219+N6->i3220+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->i3219+N7->i3220+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->i3219+N8->i3220+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->i3219+N9->i3220+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->i3219+N10->i3220+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->i3219+N11->i3220+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->i3219+N12->i3220+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->i3219+N13->i3220+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->i3219+N14->i3220+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->i3219+N15->i3220+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->i3219+N16->i3220+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->i3219+N17->i3220+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->i3219+N18->i3220+N18->null+N19->i320+N19->i321+N19->i322+N19->i323+N19->i324+N19->i325+N19->i326+N19->i327+N19->i328+N19->i329+N19->i3210+N19->i3211+N19->i3212+N19->i3213+N19->i3214+N19->i3215+N19->i3216+N19->i3217+N19->i3218+N19->i3219+N19->i3220+N19->null+N20->i320+N20->i321+N20->i322+N20->i323+N20->i324+N20->i325+N20->i326+N20->i327+N20->i328+N20->i329+N20->i3210+N20->i3211+N20->i3212+N20->i3213+N20->i3214+N20->i3215+N20->i3216+N20->i3217+N20->i3218+N20->i3219+N20->i3220+N20->null
}


fact {
	(QF.size_0) in BSTreeIntVar->i320+BSTreeIntVar->i321+BSTreeIntVar->i322+BSTreeIntVar->i323+BSTreeIntVar->i324+BSTreeIntVar->i325+BSTreeIntVar->i326+BSTreeIntVar->i327+BSTreeIntVar->i328+BSTreeIntVar->i329+BSTreeIntVar->i3210+BSTreeIntVar->i3211+BSTreeIntVar->i3212+BSTreeIntVar->i3213+BSTreeIntVar->i3214+BSTreeIntVar->i3215+BSTreeIntVar->i3216+BSTreeIntVar->i3217+BSTreeIntVar->i3218+BSTreeIntVar->i3219+BSTreeIntVar->i3220+BSTreeIntVar->i3221
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) {
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
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
   +
   N19->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N20->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
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
	  (m = N8 and size = i329) or
	  (m = N9 and size = i3210) or
	  (m = N10 and size = i3211) or
	  (m = N11 and size = i3212) or
	  (m = N12 and size = i3213) or
	  (m = N13 and size = i3214) or
	  (m = N14 and size = i3215) or
	  (m = N15 and size = i3216) or
	  (m = N16 and size = i3217) or
	  (m = N17 and size = i3218) or
	  (m = N18 and size = i3219) or
	  (m = N19 and size = i3220) or
	  (m = N20 and size = i3221)
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 BSTreeIntVar, exactly 21 BSTreeIntVarNode, 1 int, exactly 22 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) {
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
 +
 N8->N9
 +
 N9->N10
 +
 N10->N11
 +
 N11->N12
 +
 N12->N13
 +
 N13->N14
 +
 N14->N15
 +
 N15->N16
 +
 N16->N17
 +
 N17->N18
 +
 N18->N19
 +
 N19->N20
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) {
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
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
   +
   N19->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N20->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) {
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
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N19->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N20->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) {
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
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N19->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N20->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N6->(N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N7->(N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N8->(N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N9->(N10+N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N10->(N11+N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N11->(N12+N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N12->(N13+N14+N15+N16+N17+N18+N19+N20)
   +
   N13->(N14+N15+N16+N17+N18+N19+N20)
   +
   N14->(N15+N16+N17+N18+N19+N20)
   +
   N15->(N16+N17+N18+N19+N20)
   +
   N16->(N17+N18+N19+N20)
   +
   N17->(N18+N19+N20)
   +
   N18->(N19+N20)
   +
   N19->(N20)
 )
}




