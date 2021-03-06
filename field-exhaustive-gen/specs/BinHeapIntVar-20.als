module binheapintvar

open Integer6

one sig null {}

one sig BinHeapIntVar {}

abstract sig BinHeapIntVarNode {}


one sig QF {
    thiz_0:        one BinHeapIntVar,
    head_0:        BinHeapIntVar -> one (BinHeapIntVarNode+null),
    size_0:        BinHeapIntVar -> one JavaPrimitiveIntegerValue,
    element_0:     BinHeapIntVarNode -> one (JavaPrimitiveIntegerValue+null),
    degree_0:      BinHeapIntVarNode -> one JavaPrimitiveIntegerValue,

    fsibling_0:     BinHeapIntVarNode -> lone (BinHeapIntVarNode+null),
    bsibling_0:     BinHeapIntVarNode -> lone (BinHeapIntVarNode+null),
    fchild_0:       BinHeapIntVarNode -> lone (BinHeapIntVarNode+null),
    bchild_0:       BinHeapIntVarNode -> lone (BinHeapIntVarNode+null),
    fparent_0:      BinHeapIntVarNode -> lone (BinHeapIntVarNode+null),
    bparent_0:      BinHeapIntVarNode -> lone (BinHeapIntVarNode+null)

}

fact repOk {
let thiz    = QF.thiz_0, 
    head    = QF.head_0,
    element = QF.element_0,
    degree  = QF.degree_0,
    sibling = QF.fsibling_0+QF.bsibling_0,
    child   = QF.fchild_0+QF.bchild_0,
    parent  = QF.fparent_0+QF.bparent_0
{

  ( all n: BinHeapIntVarNode | ( n in thiz.head.*(sibling+child)-null => (
    ( n.element!=null ) &&   
    ( n.parent!=null  => pred_java_primitive_integer_value_gte[n.element, n.parent.element] ) &&   
    ( n.child!=null   => n !in n.child.*(sibling+child)-null ) && 
    ( n.sibling!=null => n !in n.sibling.*(sibling+child)-null ) && 
    ( ( n.child !=null && n.sibling!=null ) => (no m: BinHeapIntVarNode | ( m in n.child.*(child+sibling)-null && m in n.sibling.*(child+sibling)-null )) ) && 
    ( pred_java_primitive_integer_value_gte[n.degree, i320] ) && 
    ( n.child=null => n.degree = i320 ) && 
/*    ( n.child!=null => mysize1[(n.child.*sibling-null), n.degree] )  && 
    ( some i,j: JavaPrimitiveIntegerValue | mysize2[( ( n.child + n.child.child.*(child+sibling) ) - null ),i] && mysize3[( ( n.child + n.child.sibling.*(child+sibling)) - null ),j] && i=j  ) && */
    ( n.child!=null => ( all m: BinHeapIntVarNode | ( m in n.child.*sibling-null =>  m.parent = n  ) ) ) && 
    ( ( n.sibling!=null && n.parent!=null ) => ( pred_java_primitive_integer_value_gt[n.degree, n.sibling.degree] ) )
  )))                                                              && 

  ( all n: BinHeapIntVarNode | n in thiz.head.*sibling-null => ( 
    ( n.sibling!=null => pred_java_primitive_integer_value_lt[n.degree, n.sibling.degree] ) && 
    ( n.parent=null )                               )
  )
}                             
}


fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
}


// **** Symmetry breaking predicate

fun globalMin[s : set (BinHeapIntVarNode + BinHeapIntVar)] : lone (BinHeapIntVarNode + BinHeapIntVar) {
	s - s.^(BinHeapIntVar->N0 + node_next[])
}

fun minP[n : BinHeapIntVarNode] : BinHeapIntVarNode {
	globalMin[(QF.fsibling_0 + QF.fchild_0 + QF.fparent_0 + QF.head_0).n ]
}



fun FReachSB[] : set univ {
	(QF.thiz_0).(QF.head_0).*(QF.fsibling_0 + QF.fchild_0 + QF.fparent_0) - null
}

fact { 
let 	
  fsibling = QF.fsibling_0,
  bsibling = QF.bsibling_0,
  fchild  = QF.fchild_0,
  bchild  = QF.bchild_0,
  fparent = QF.fparent_0,
  bparent = QF.bparent_0 | {
		
  no ((fsibling.univ) & (bsibling.univ))  
  BinHeapIntVarNode = fsibling.univ + bsibling.univ 

  no ((fchild.univ) & (bchild.univ))  
  BinHeapIntVarNode = fchild.univ + bchild.univ 

  no ((fparent.univ) & (bparent.univ))   
  BinHeapIntVarNode = fparent.univ + bparent.univ
				
}}

fact orderBinHeapIntVarNodeCondition_c{
( all disj o1, o2, o3 : BinHeapIntVarNode |
  let a = minP[o1] | let b = minP[o2] | let c = minP[o3] |
  ( o1+o2+o3 in FReachSB[] and
    some a and some b and some c and a = b and b=c and a in BinHeapIntVarNode and
    o1 = a.(QF.fsibling_0) and
    o2 = a.(QF.fchild_0) and
    o3 = a.(QF.fparent_0)
  ) implies  (o2 = o1.node_next[] and o3 = o2.node_next[])
)
&&
( all disj o1, o2 : BinHeapIntVarNode |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReachSB[] 
		and	some a and some b and a = b and a in BinHeapIntVarNode
		and (no o3 : BinHeapIntVarNode | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and	o1 = a.(QF.fsibling_0)
	) implies o2 = o1.node_next[]
)
&&
( all disj o1, o2 : BinHeapIntVarNode |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReachSB[] 
		and	some a and some b and a = b and a in BinHeapIntVarNode
		and (no o3 : BinHeapIntVarNode | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and o1 != a.(QF.fsibling_0) and o2 != a.(QF.fsibling_0) and o1 = a.(QF.fchild_0)
	) implies o2 = o1.node_next[]
)
}

fact orderBinHeapIntVarNodeCondition_d { 
  all disj o1, o2 : BinHeapIntVarNode | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReachSB[] and some a and some b and 
        a!=b and a+b in BinHeapIntVarNode and a in node_prevs[b]) 
           implies o1 in node_prevs[o2]
} 

fact orderBinHeapIntVarNodeCondition_e {
  all disj o1, o2 : BinHeapIntVarNode | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReachSB[] and some a and some b and 
        a in BinHeapIntVar and b in BinHeapIntVarNode) 
           implies o1 in node_prevs[o2]
}

fact compactBinHeapIntVarNode { all o : BinHeapIntVarNode | o in FReachSB[] 
    implies node_prevs[o] in FReachSB[]
} 


fact fixNonReachable { all n : BinHeapIntVarNode | n !in (QF.thiz_0).(QF.head_0).*(QF.fsibling_0 + QF.fchild_0 + QF.fparent_0) implies 
	(
		n.(QF.element_0) = i320 and
		n.(QF.degree_0) = i320 and
		n.(QF.fsibling_0) = null and
		no n.(QF.bsibling_0) and
		n.(QF.fchild_0) = null and
		no n.(QF.bchild_0) and
		n.(QF.fparent_0) = null and
		no n.(QF.bparent_0)
	)
}


fun FReach[] : set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) {
	(QF.thiz_0).(QF.head_0).*(QF.fsibling_0 + QF.fchild_0) - null
}


one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19 extends BinHeapIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329,i3210,i3211,i3212,i3213,i3214,i3215,i3216,i3217,i3218,i3219,i3220 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true+i3215->true+i3216->false+i3217->false+i3218->true+i3219->true+i3220->false in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false+i3215->true+i3216->false+i3217->true+i3218->false+i3219->true+i3220->false in b00
	b05 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false in b05
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false+i3215->false+i3216->true+i3217->true+i3218->true+i3219->true+i3220->true in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->false in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true+i3215->true+i3216->false+i3217->false+i3218->false+i3219->false+i3220->true in b02
}



fact { QF.fsibling_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->null+N16->N17+N16->N18+N16->N19+N16->null+N17->N18+N17->N19+N17->null+N18->N19+N18->null+N19->null }
fact { QF.fchild_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->null+N16->N17+N16->N18+N16->N19+N16->null+N17->N18+N17->N19+N17->null+N18->N19+N18->null+N19->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->N19+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->N19+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->N19+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->N19+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->N19+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->N19+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->N19+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->N19+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->N19+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->N19+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->N19+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->N19+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->N19+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->N19+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->N19+N14->null+N15->N16+N15->N17+N15->N18+N15->N19+N15->null+N16->N17+N16->N18+N16->N19+N16->null+N17->N18+N17->N19+N17->null+N18->N19+N18->null+N19->null }
fact { QF.bsibling_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19 }
fact { QF.bchild_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18+N19->N0+N19->N1+N19->N2+N19->N3+N19->N4+N19->N5+N19->N6+N19->N7+N19->N8+N19->N9+N19->N10+N19->N11+N19->N12+N19->N13+N19->N14+N19->N15+N19->N16+N19->N17+N19->N18+N19->N19 }


fact {
	(QF.element_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->i3219+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->i3219+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->i3219+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->i3219+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->i3219+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->i3219+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->i3219+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->i3219+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->i3219+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->i3219+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->i3219+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->i3219+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->i3219+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->i3219+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->i3219+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->i3219+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->i3219+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->i3219+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->i3219+N18->null+N19->i320+N19->i321+N19->i322+N19->i323+N19->i324+N19->i325+N19->i326+N19->i327+N19->i328+N19->i329+N19->i3210+N19->i3211+N19->i3212+N19->i3213+N19->i3214+N19->i3215+N19->i3216+N19->i3217+N19->i3218+N19->i3219+N19->null
}


fact {
	(QF.degree_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->i3219+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->i3219+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->i3219+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->i3219+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->i3219+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->i3219+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->i3219+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->i3219+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->i3219+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->i3219+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->i3219+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->i3219+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->i3219+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->i3219+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->i3219+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->i3219+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->i3219+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->i3219+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->i3219+N18->null+N19->i320+N19->i321+N19->i322+N19->i323+N19->i324+N19->i325+N19->i326+N19->i327+N19->i328+N19->i329+N19->i3210+N19->i3211+N19->i3212+N19->i3213+N19->i3214+N19->i3215+N19->i3216+N19->i3217+N19->i3218+N19->i3219+N19->null
}


fact {
	(QF.size_0) in BinHeapIntVar->i320+BinHeapIntVar->i321+BinHeapIntVar->i322+BinHeapIntVar->i323+BinHeapIntVar->i324+BinHeapIntVar->i325+BinHeapIntVar->i326+BinHeapIntVar->i327+BinHeapIntVar->i328+BinHeapIntVar->i329+BinHeapIntVar->i3210+BinHeapIntVar->i3211+BinHeapIntVar->i3212+BinHeapIntVar->i3213+BinHeapIntVar->i3214+BinHeapIntVar->i3215+BinHeapIntVar->i3216+BinHeapIntVar->i3217+BinHeapIntVar->i3218+BinHeapIntVar->i3219+BinHeapIntVar->i3220
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) {
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
	  (m = N19 and size = i3220)
}
fact {
let thiz    = QF.thiz_0, 
    head    = QF.head_0,
    degree  = QF.degree_0,
    sibling = QF.fsibling_0+QF.bsibling_0,
    child   = QF.fchild_0+QF.bchild_0
{

N0 in thiz.head.*(sibling+child)-null => ( ( N0.child!=null => mysize10[(N0.child.*sibling-null), N0.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize20[( ( N0.child + N0.child.child.*(child+sibling) ) - null ),i] && mysize30[( ( N0.child + N0.child.sibling.*(child+sibling)) - null ),i] ))

N1 in thiz.head.*(sibling+child)-null => ( ( N1.child!=null => mysize11[(N1.child.*sibling-null), N1.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize21[( ( N1.child + N1.child.child.*(child+sibling) ) - null ),i] && mysize31[( ( N1.child + N1.child.sibling.*(child+sibling)) - null ),i] ))

N2 in thiz.head.*(sibling+child)-null => ( ( N2.child!=null => mysize12[(N2.child.*sibling-null), N2.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize22[( ( N2.child + N2.child.child.*(child+sibling) ) - null ),i] && mysize32[( ( N2.child + N2.child.sibling.*(child+sibling)) - null ),i] ))

N3 in thiz.head.*(sibling+child)-null => ( ( N3.child!=null => mysize13[(N3.child.*sibling-null), N3.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize23[( ( N3.child + N3.child.child.*(child+sibling) ) - null ),i] && mysize33[( ( N3.child + N3.child.sibling.*(child+sibling)) - null ),i] ))

N4 in thiz.head.*(sibling+child)-null => ( ( N4.child!=null => mysize14[(N4.child.*sibling-null), N4.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize24[( ( N4.child + N4.child.child.*(child+sibling) ) - null ),i] && mysize34[( ( N4.child + N4.child.sibling.*(child+sibling)) - null ),i] ))

N5 in thiz.head.*(sibling+child)-null => ( ( N5.child!=null => mysize15[(N5.child.*sibling-null), N5.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize25[( ( N5.child + N5.child.child.*(child+sibling) ) - null ),i] && mysize35[( ( N5.child + N5.child.sibling.*(child+sibling)) - null ),i] ))

N6 in thiz.head.*(sibling+child)-null => ( ( N6.child!=null => mysize16[(N6.child.*sibling-null), N6.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize26[( ( N6.child + N6.child.child.*(child+sibling) ) - null ),i] && mysize36[( ( N6.child + N6.child.sibling.*(child+sibling)) - null ),i] ))

N7 in thiz.head.*(sibling+child)-null => ( ( N7.child!=null => mysize17[(N7.child.*sibling-null), N7.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize27[( ( N7.child + N7.child.child.*(child+sibling) ) - null ),i] && mysize37[( ( N7.child + N7.child.sibling.*(child+sibling)) - null ),i] ))

N8 in thiz.head.*(sibling+child)-null => ( ( N8.child!=null => mysize18[(N8.child.*sibling-null), N8.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize28[( ( N8.child + N8.child.child.*(child+sibling) ) - null ),i] && mysize38[( ( N8.child + N8.child.sibling.*(child+sibling)) - null ),i] ))

N9 in thiz.head.*(sibling+child)-null => ( ( N9.child!=null => mysize19[(N9.child.*sibling-null), N9.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize29[( ( N9.child + N9.child.child.*(child+sibling) ) - null ),i] && mysize39[( ( N9.child + N9.child.sibling.*(child+sibling)) - null ),i] ))

N10 in thiz.head.*(sibling+child)-null => ( ( N10.child!=null => mysize110[(N10.child.*sibling-null), N10.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize210[( ( N10.child + N10.child.child.*(child+sibling) ) - null ),i] && mysize310[( ( N10.child + N10.child.sibling.*(child+sibling)) - null ),i] ))

N11 in thiz.head.*(sibling+child)-null => ( ( N11.child!=null => mysize111[(N11.child.*sibling-null), N11.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize211[( ( N11.child + N11.child.child.*(child+sibling) ) - null ),i] && mysize311[( ( N11.child + N11.child.sibling.*(child+sibling)) - null ),i] ))

N12 in thiz.head.*(sibling+child)-null => ( ( N12.child!=null => mysize112[(N12.child.*sibling-null), N12.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize212[( ( N12.child + N12.child.child.*(child+sibling) ) - null ),i] && mysize312[( ( N12.child + N12.child.sibling.*(child+sibling)) - null ),i] ))

N13 in thiz.head.*(sibling+child)-null => ( ( N13.child!=null => mysize113[(N13.child.*sibling-null), N13.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize213[( ( N13.child + N13.child.child.*(child+sibling) ) - null ),i] && mysize313[( ( N13.child + N13.child.sibling.*(child+sibling)) - null ),i] ))

N14 in thiz.head.*(sibling+child)-null => ( ( N14.child!=null => mysize114[(N14.child.*sibling-null), N14.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize214[( ( N14.child + N14.child.child.*(child+sibling) ) - null ),i] && mysize314[( ( N14.child + N14.child.sibling.*(child+sibling)) - null ),i] ))

N15 in thiz.head.*(sibling+child)-null => ( ( N15.child!=null => mysize115[(N15.child.*sibling-null), N15.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize215[( ( N15.child + N15.child.child.*(child+sibling) ) - null ),i] && mysize315[( ( N15.child + N15.child.sibling.*(child+sibling)) - null ),i] ))

N16 in thiz.head.*(sibling+child)-null => ( ( N16.child!=null => mysize116[(N16.child.*sibling-null), N16.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize216[( ( N16.child + N16.child.child.*(child+sibling) ) - null ),i] && mysize316[( ( N16.child + N16.child.sibling.*(child+sibling)) - null ),i] ))

N17 in thiz.head.*(sibling+child)-null => ( ( N17.child!=null => mysize117[(N17.child.*sibling-null), N17.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize217[( ( N17.child + N17.child.child.*(child+sibling) ) - null ),i] && mysize317[( ( N17.child + N17.child.sibling.*(child+sibling)) - null ),i] ))

N18 in thiz.head.*(sibling+child)-null => ( ( N18.child!=null => mysize118[(N18.child.*sibling-null), N18.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize218[( ( N18.child + N18.child.child.*(child+sibling) ) - null ),i] && mysize318[( ( N18.child + N18.child.sibling.*(child+sibling)) - null ),i] ))

N19 in thiz.head.*(sibling+child)-null => ( ( N19.child!=null => mysize119[(N19.child.*sibling-null), N19.degree] )  && ( some i: JavaPrimitiveIntegerValue | mysize219[( ( N19.child + N19.child.child.*(child+sibling) ) - null ),i] && mysize319[( ( N19.child + N19.child.sibling.*(child+sibling)) - null ),i] ))

}
}
one sig QF10 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize10[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF10.x1 in s and ((res = i321 and no s-QF10.x1) or 
	 (QF10.x2 in s-QF10.x1 and ((res = i322 and no s-QF10.x1-QF10.x2) or 
	 (QF10.x3 in s-QF10.x1-QF10.x2 and ((res = i323 and no s-QF10.x1-QF10.x2-QF10.x3) or 
	 (QF10.x4 in s-QF10.x1-QF10.x2-QF10.x3 and ((res = i324 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4) or 
	 (QF10.x5 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4 and ((res = i325 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5) or 
	 (QF10.x6 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5 and ((res = i326 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6) or 
	 (QF10.x7 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6 and ((res = i327 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7) or 
	 (QF10.x8 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7 and ((res = i328 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8) or 
	 (QF10.x9 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8 and ((res = i329 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9) or 
	 (QF10.x10 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9 and ((res = i3210 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10) or 
	 (QF10.x11 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10 and ((res = i3211 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11) or 
	 (QF10.x12 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11 and ((res = i3212 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12) or 
	 (QF10.x13 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12 and ((res = i3213 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13) or 
	 (QF10.x14 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13 and ((res = i3214 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14) or 
	 (QF10.x15 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14 and ((res = i3215 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15) or 
	 (QF10.x16 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15 and ((res = i3216 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16) or 
	 (QF10.x17 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16 and ((res = i3217 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17) or 
	 (QF10.x18 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17 and ((res = i3218 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18) or 
	 (QF10.x19 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18 and ((res = i3219 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19) or 
	 (QF10.x20 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19 and ((res = i3220 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14-QF10.x15-QF10.x16-QF10.x17-QF10.x18-QF10.x19-QF10.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF20 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize20[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF20.x1 in s and ((res = i321 and no s-QF20.x1) or 
	 (QF20.x2 in s-QF20.x1 and ((res = i322 and no s-QF20.x1-QF20.x2) or 
	 (QF20.x3 in s-QF20.x1-QF20.x2 and ((res = i323 and no s-QF20.x1-QF20.x2-QF20.x3) or 
	 (QF20.x4 in s-QF20.x1-QF20.x2-QF20.x3 and ((res = i324 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4) or 
	 (QF20.x5 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4 and ((res = i325 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5) or 
	 (QF20.x6 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5 and ((res = i326 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6) or 
	 (QF20.x7 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6 and ((res = i327 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7) or 
	 (QF20.x8 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7 and ((res = i328 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8) or 
	 (QF20.x9 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8 and ((res = i329 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9) or 
	 (QF20.x10 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9 and ((res = i3210 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10) or 
	 (QF20.x11 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10 and ((res = i3211 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11) or 
	 (QF20.x12 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11 and ((res = i3212 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12) or 
	 (QF20.x13 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12 and ((res = i3213 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13) or 
	 (QF20.x14 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13 and ((res = i3214 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14) or 
	 (QF20.x15 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14 and ((res = i3215 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15) or 
	 (QF20.x16 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15 and ((res = i3216 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16) or 
	 (QF20.x17 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16 and ((res = i3217 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16-QF20.x17) or 
	 (QF20.x18 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16-QF20.x17 and ((res = i3218 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16-QF20.x17-QF20.x18) or 
	 (QF20.x19 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16-QF20.x17-QF20.x18 and ((res = i3219 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16-QF20.x17-QF20.x18-QF20.x19) or 
	 (QF20.x20 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16-QF20.x17-QF20.x18-QF20.x19 and ((res = i3220 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13-QF20.x14-QF20.x15-QF20.x16-QF20.x17-QF20.x18-QF20.x19-QF20.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF30 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize30[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF30.x1 in s and ((res = i321 and no s-QF30.x1) or 
	 (QF30.x2 in s-QF30.x1 and ((res = i322 and no s-QF30.x1-QF30.x2) or 
	 (QF30.x3 in s-QF30.x1-QF30.x2 and ((res = i323 and no s-QF30.x1-QF30.x2-QF30.x3) or 
	 (QF30.x4 in s-QF30.x1-QF30.x2-QF30.x3 and ((res = i324 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4) or 
	 (QF30.x5 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4 and ((res = i325 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5) or 
	 (QF30.x6 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5 and ((res = i326 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6) or 
	 (QF30.x7 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6 and ((res = i327 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7) or 
	 (QF30.x8 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7 and ((res = i328 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8) or 
	 (QF30.x9 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8 and ((res = i329 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9) or 
	 (QF30.x10 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9 and ((res = i3210 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10) or 
	 (QF30.x11 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10 and ((res = i3211 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11) or 
	 (QF30.x12 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11 and ((res = i3212 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12) or 
	 (QF30.x13 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12 and ((res = i3213 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13) or 
	 (QF30.x14 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13 and ((res = i3214 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14) or 
	 (QF30.x15 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14 and ((res = i3215 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15) or 
	 (QF30.x16 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15 and ((res = i3216 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16) or 
	 (QF30.x17 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16 and ((res = i3217 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16-QF30.x17) or 
	 (QF30.x18 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16-QF30.x17 and ((res = i3218 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16-QF30.x17-QF30.x18) or 
	 (QF30.x19 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16-QF30.x17-QF30.x18 and ((res = i3219 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16-QF30.x17-QF30.x18-QF30.x19) or 
	 (QF30.x20 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16-QF30.x17-QF30.x18-QF30.x19 and ((res = i3220 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13-QF30.x14-QF30.x15-QF30.x16-QF30.x17-QF30.x18-QF30.x19-QF30.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF11 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize11[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF11.x1 in s and ((res = i321 and no s-QF11.x1) or 
	 (QF11.x2 in s-QF11.x1 and ((res = i322 and no s-QF11.x1-QF11.x2) or 
	 (QF11.x3 in s-QF11.x1-QF11.x2 and ((res = i323 and no s-QF11.x1-QF11.x2-QF11.x3) or 
	 (QF11.x4 in s-QF11.x1-QF11.x2-QF11.x3 and ((res = i324 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4) or 
	 (QF11.x5 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4 and ((res = i325 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5) or 
	 (QF11.x6 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5 and ((res = i326 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6) or 
	 (QF11.x7 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6 and ((res = i327 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7) or 
	 (QF11.x8 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7 and ((res = i328 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8) or 
	 (QF11.x9 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8 and ((res = i329 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9) or 
	 (QF11.x10 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9 and ((res = i3210 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10) or 
	 (QF11.x11 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10 and ((res = i3211 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11) or 
	 (QF11.x12 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11 and ((res = i3212 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12) or 
	 (QF11.x13 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12 and ((res = i3213 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13) or 
	 (QF11.x14 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13 and ((res = i3214 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14) or 
	 (QF11.x15 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14 and ((res = i3215 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15) or 
	 (QF11.x16 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15 and ((res = i3216 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16) or 
	 (QF11.x17 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16 and ((res = i3217 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17) or 
	 (QF11.x18 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17 and ((res = i3218 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18) or 
	 (QF11.x19 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18 and ((res = i3219 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19) or 
	 (QF11.x20 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19 and ((res = i3220 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14-QF11.x15-QF11.x16-QF11.x17-QF11.x18-QF11.x19-QF11.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF21 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize21[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF21.x1 in s and ((res = i321 and no s-QF21.x1) or 
	 (QF21.x2 in s-QF21.x1 and ((res = i322 and no s-QF21.x1-QF21.x2) or 
	 (QF21.x3 in s-QF21.x1-QF21.x2 and ((res = i323 and no s-QF21.x1-QF21.x2-QF21.x3) or 
	 (QF21.x4 in s-QF21.x1-QF21.x2-QF21.x3 and ((res = i324 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4) or 
	 (QF21.x5 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4 and ((res = i325 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5) or 
	 (QF21.x6 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5 and ((res = i326 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6) or 
	 (QF21.x7 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6 and ((res = i327 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7) or 
	 (QF21.x8 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7 and ((res = i328 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8) or 
	 (QF21.x9 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8 and ((res = i329 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9) or 
	 (QF21.x10 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9 and ((res = i3210 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10) or 
	 (QF21.x11 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10 and ((res = i3211 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11) or 
	 (QF21.x12 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11 and ((res = i3212 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12) or 
	 (QF21.x13 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12 and ((res = i3213 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13) or 
	 (QF21.x14 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13 and ((res = i3214 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14) or 
	 (QF21.x15 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14 and ((res = i3215 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15) or 
	 (QF21.x16 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15 and ((res = i3216 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16) or 
	 (QF21.x17 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16 and ((res = i3217 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16-QF21.x17) or 
	 (QF21.x18 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16-QF21.x17 and ((res = i3218 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16-QF21.x17-QF21.x18) or 
	 (QF21.x19 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16-QF21.x17-QF21.x18 and ((res = i3219 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16-QF21.x17-QF21.x18-QF21.x19) or 
	 (QF21.x20 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16-QF21.x17-QF21.x18-QF21.x19 and ((res = i3220 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13-QF21.x14-QF21.x15-QF21.x16-QF21.x17-QF21.x18-QF21.x19-QF21.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF31 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize31[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF31.x1 in s and ((res = i321 and no s-QF31.x1) or 
	 (QF31.x2 in s-QF31.x1 and ((res = i322 and no s-QF31.x1-QF31.x2) or 
	 (QF31.x3 in s-QF31.x1-QF31.x2 and ((res = i323 and no s-QF31.x1-QF31.x2-QF31.x3) or 
	 (QF31.x4 in s-QF31.x1-QF31.x2-QF31.x3 and ((res = i324 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4) or 
	 (QF31.x5 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4 and ((res = i325 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5) or 
	 (QF31.x6 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5 and ((res = i326 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6) or 
	 (QF31.x7 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6 and ((res = i327 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7) or 
	 (QF31.x8 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7 and ((res = i328 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8) or 
	 (QF31.x9 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8 and ((res = i329 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9) or 
	 (QF31.x10 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9 and ((res = i3210 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10) or 
	 (QF31.x11 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10 and ((res = i3211 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11) or 
	 (QF31.x12 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11 and ((res = i3212 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12) or 
	 (QF31.x13 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12 and ((res = i3213 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13) or 
	 (QF31.x14 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13 and ((res = i3214 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14) or 
	 (QF31.x15 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14 and ((res = i3215 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15) or 
	 (QF31.x16 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15 and ((res = i3216 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16) or 
	 (QF31.x17 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16 and ((res = i3217 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16-QF31.x17) or 
	 (QF31.x18 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16-QF31.x17 and ((res = i3218 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16-QF31.x17-QF31.x18) or 
	 (QF31.x19 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16-QF31.x17-QF31.x18 and ((res = i3219 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16-QF31.x17-QF31.x18-QF31.x19) or 
	 (QF31.x20 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16-QF31.x17-QF31.x18-QF31.x19 and ((res = i3220 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13-QF31.x14-QF31.x15-QF31.x16-QF31.x17-QF31.x18-QF31.x19-QF31.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF12 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize12[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF12.x1 in s and ((res = i321 and no s-QF12.x1) or 
	 (QF12.x2 in s-QF12.x1 and ((res = i322 and no s-QF12.x1-QF12.x2) or 
	 (QF12.x3 in s-QF12.x1-QF12.x2 and ((res = i323 and no s-QF12.x1-QF12.x2-QF12.x3) or 
	 (QF12.x4 in s-QF12.x1-QF12.x2-QF12.x3 and ((res = i324 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4) or 
	 (QF12.x5 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4 and ((res = i325 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5) or 
	 (QF12.x6 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5 and ((res = i326 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6) or 
	 (QF12.x7 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6 and ((res = i327 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7) or 
	 (QF12.x8 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7 and ((res = i328 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8) or 
	 (QF12.x9 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8 and ((res = i329 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9) or 
	 (QF12.x10 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9 and ((res = i3210 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10) or 
	 (QF12.x11 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10 and ((res = i3211 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11) or 
	 (QF12.x12 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11 and ((res = i3212 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12) or 
	 (QF12.x13 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12 and ((res = i3213 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13) or 
	 (QF12.x14 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13 and ((res = i3214 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14) or 
	 (QF12.x15 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14 and ((res = i3215 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15) or 
	 (QF12.x16 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15 and ((res = i3216 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16) or 
	 (QF12.x17 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16 and ((res = i3217 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17) or 
	 (QF12.x18 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17 and ((res = i3218 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18) or 
	 (QF12.x19 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18 and ((res = i3219 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19) or 
	 (QF12.x20 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19 and ((res = i3220 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14-QF12.x15-QF12.x16-QF12.x17-QF12.x18-QF12.x19-QF12.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF22 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize22[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF22.x1 in s and ((res = i321 and no s-QF22.x1) or 
	 (QF22.x2 in s-QF22.x1 and ((res = i322 and no s-QF22.x1-QF22.x2) or 
	 (QF22.x3 in s-QF22.x1-QF22.x2 and ((res = i323 and no s-QF22.x1-QF22.x2-QF22.x3) or 
	 (QF22.x4 in s-QF22.x1-QF22.x2-QF22.x3 and ((res = i324 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4) or 
	 (QF22.x5 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4 and ((res = i325 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5) or 
	 (QF22.x6 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5 and ((res = i326 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6) or 
	 (QF22.x7 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6 and ((res = i327 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7) or 
	 (QF22.x8 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7 and ((res = i328 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8) or 
	 (QF22.x9 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8 and ((res = i329 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9) or 
	 (QF22.x10 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9 and ((res = i3210 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10) or 
	 (QF22.x11 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10 and ((res = i3211 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11) or 
	 (QF22.x12 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11 and ((res = i3212 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12) or 
	 (QF22.x13 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12 and ((res = i3213 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13) or 
	 (QF22.x14 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13 and ((res = i3214 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14) or 
	 (QF22.x15 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14 and ((res = i3215 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15) or 
	 (QF22.x16 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15 and ((res = i3216 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16) or 
	 (QF22.x17 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16 and ((res = i3217 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16-QF22.x17) or 
	 (QF22.x18 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16-QF22.x17 and ((res = i3218 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16-QF22.x17-QF22.x18) or 
	 (QF22.x19 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16-QF22.x17-QF22.x18 and ((res = i3219 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16-QF22.x17-QF22.x18-QF22.x19) or 
	 (QF22.x20 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16-QF22.x17-QF22.x18-QF22.x19 and ((res = i3220 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13-QF22.x14-QF22.x15-QF22.x16-QF22.x17-QF22.x18-QF22.x19-QF22.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF32 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize32[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF32.x1 in s and ((res = i321 and no s-QF32.x1) or 
	 (QF32.x2 in s-QF32.x1 and ((res = i322 and no s-QF32.x1-QF32.x2) or 
	 (QF32.x3 in s-QF32.x1-QF32.x2 and ((res = i323 and no s-QF32.x1-QF32.x2-QF32.x3) or 
	 (QF32.x4 in s-QF32.x1-QF32.x2-QF32.x3 and ((res = i324 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4) or 
	 (QF32.x5 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4 and ((res = i325 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5) or 
	 (QF32.x6 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5 and ((res = i326 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6) or 
	 (QF32.x7 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6 and ((res = i327 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7) or 
	 (QF32.x8 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7 and ((res = i328 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8) or 
	 (QF32.x9 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8 and ((res = i329 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9) or 
	 (QF32.x10 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9 and ((res = i3210 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10) or 
	 (QF32.x11 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10 and ((res = i3211 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11) or 
	 (QF32.x12 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11 and ((res = i3212 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12) or 
	 (QF32.x13 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12 and ((res = i3213 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13) or 
	 (QF32.x14 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13 and ((res = i3214 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14) or 
	 (QF32.x15 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14 and ((res = i3215 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15) or 
	 (QF32.x16 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15 and ((res = i3216 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16) or 
	 (QF32.x17 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16 and ((res = i3217 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16-QF32.x17) or 
	 (QF32.x18 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16-QF32.x17 and ((res = i3218 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16-QF32.x17-QF32.x18) or 
	 (QF32.x19 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16-QF32.x17-QF32.x18 and ((res = i3219 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16-QF32.x17-QF32.x18-QF32.x19) or 
	 (QF32.x20 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16-QF32.x17-QF32.x18-QF32.x19 and ((res = i3220 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13-QF32.x14-QF32.x15-QF32.x16-QF32.x17-QF32.x18-QF32.x19-QF32.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF13 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize13[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF13.x1 in s and ((res = i321 and no s-QF13.x1) or 
	 (QF13.x2 in s-QF13.x1 and ((res = i322 and no s-QF13.x1-QF13.x2) or 
	 (QF13.x3 in s-QF13.x1-QF13.x2 and ((res = i323 and no s-QF13.x1-QF13.x2-QF13.x3) or 
	 (QF13.x4 in s-QF13.x1-QF13.x2-QF13.x3 and ((res = i324 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4) or 
	 (QF13.x5 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4 and ((res = i325 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5) or 
	 (QF13.x6 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5 and ((res = i326 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6) or 
	 (QF13.x7 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6 and ((res = i327 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7) or 
	 (QF13.x8 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7 and ((res = i328 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8) or 
	 (QF13.x9 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8 and ((res = i329 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9) or 
	 (QF13.x10 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9 and ((res = i3210 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10) or 
	 (QF13.x11 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10 and ((res = i3211 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11) or 
	 (QF13.x12 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11 and ((res = i3212 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12) or 
	 (QF13.x13 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12 and ((res = i3213 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13) or 
	 (QF13.x14 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13 and ((res = i3214 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14) or 
	 (QF13.x15 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14 and ((res = i3215 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15) or 
	 (QF13.x16 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15 and ((res = i3216 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16) or 
	 (QF13.x17 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16 and ((res = i3217 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17) or 
	 (QF13.x18 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17 and ((res = i3218 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18) or 
	 (QF13.x19 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18 and ((res = i3219 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19) or 
	 (QF13.x20 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19 and ((res = i3220 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14-QF13.x15-QF13.x16-QF13.x17-QF13.x18-QF13.x19-QF13.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF23 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize23[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF23.x1 in s and ((res = i321 and no s-QF23.x1) or 
	 (QF23.x2 in s-QF23.x1 and ((res = i322 and no s-QF23.x1-QF23.x2) or 
	 (QF23.x3 in s-QF23.x1-QF23.x2 and ((res = i323 and no s-QF23.x1-QF23.x2-QF23.x3) or 
	 (QF23.x4 in s-QF23.x1-QF23.x2-QF23.x3 and ((res = i324 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4) or 
	 (QF23.x5 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4 and ((res = i325 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5) or 
	 (QF23.x6 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5 and ((res = i326 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6) or 
	 (QF23.x7 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6 and ((res = i327 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7) or 
	 (QF23.x8 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7 and ((res = i328 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8) or 
	 (QF23.x9 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8 and ((res = i329 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9) or 
	 (QF23.x10 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9 and ((res = i3210 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10) or 
	 (QF23.x11 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10 and ((res = i3211 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11) or 
	 (QF23.x12 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11 and ((res = i3212 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12) or 
	 (QF23.x13 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12 and ((res = i3213 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13) or 
	 (QF23.x14 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13 and ((res = i3214 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14) or 
	 (QF23.x15 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14 and ((res = i3215 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15) or 
	 (QF23.x16 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15 and ((res = i3216 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16) or 
	 (QF23.x17 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16 and ((res = i3217 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16-QF23.x17) or 
	 (QF23.x18 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16-QF23.x17 and ((res = i3218 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16-QF23.x17-QF23.x18) or 
	 (QF23.x19 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16-QF23.x17-QF23.x18 and ((res = i3219 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16-QF23.x17-QF23.x18-QF23.x19) or 
	 (QF23.x20 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16-QF23.x17-QF23.x18-QF23.x19 and ((res = i3220 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13-QF23.x14-QF23.x15-QF23.x16-QF23.x17-QF23.x18-QF23.x19-QF23.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF33 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize33[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF33.x1 in s and ((res = i321 and no s-QF33.x1) or 
	 (QF33.x2 in s-QF33.x1 and ((res = i322 and no s-QF33.x1-QF33.x2) or 
	 (QF33.x3 in s-QF33.x1-QF33.x2 and ((res = i323 and no s-QF33.x1-QF33.x2-QF33.x3) or 
	 (QF33.x4 in s-QF33.x1-QF33.x2-QF33.x3 and ((res = i324 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4) or 
	 (QF33.x5 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4 and ((res = i325 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5) or 
	 (QF33.x6 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5 and ((res = i326 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6) or 
	 (QF33.x7 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6 and ((res = i327 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7) or 
	 (QF33.x8 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7 and ((res = i328 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8) or 
	 (QF33.x9 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8 and ((res = i329 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9) or 
	 (QF33.x10 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9 and ((res = i3210 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10) or 
	 (QF33.x11 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10 and ((res = i3211 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11) or 
	 (QF33.x12 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11 and ((res = i3212 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12) or 
	 (QF33.x13 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12 and ((res = i3213 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13) or 
	 (QF33.x14 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13 and ((res = i3214 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14) or 
	 (QF33.x15 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14 and ((res = i3215 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15) or 
	 (QF33.x16 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15 and ((res = i3216 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16) or 
	 (QF33.x17 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16 and ((res = i3217 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16-QF33.x17) or 
	 (QF33.x18 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16-QF33.x17 and ((res = i3218 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16-QF33.x17-QF33.x18) or 
	 (QF33.x19 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16-QF33.x17-QF33.x18 and ((res = i3219 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16-QF33.x17-QF33.x18-QF33.x19) or 
	 (QF33.x20 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16-QF33.x17-QF33.x18-QF33.x19 and ((res = i3220 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13-QF33.x14-QF33.x15-QF33.x16-QF33.x17-QF33.x18-QF33.x19-QF33.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF14 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize14[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF14.x1 in s and ((res = i321 and no s-QF14.x1) or 
	 (QF14.x2 in s-QF14.x1 and ((res = i322 and no s-QF14.x1-QF14.x2) or 
	 (QF14.x3 in s-QF14.x1-QF14.x2 and ((res = i323 and no s-QF14.x1-QF14.x2-QF14.x3) or 
	 (QF14.x4 in s-QF14.x1-QF14.x2-QF14.x3 and ((res = i324 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4) or 
	 (QF14.x5 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4 and ((res = i325 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5) or 
	 (QF14.x6 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5 and ((res = i326 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6) or 
	 (QF14.x7 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6 and ((res = i327 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7) or 
	 (QF14.x8 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7 and ((res = i328 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8) or 
	 (QF14.x9 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8 and ((res = i329 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9) or 
	 (QF14.x10 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9 and ((res = i3210 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10) or 
	 (QF14.x11 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10 and ((res = i3211 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11) or 
	 (QF14.x12 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11 and ((res = i3212 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12) or 
	 (QF14.x13 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12 and ((res = i3213 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13) or 
	 (QF14.x14 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13 and ((res = i3214 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14) or 
	 (QF14.x15 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14 and ((res = i3215 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15) or 
	 (QF14.x16 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15 and ((res = i3216 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16) or 
	 (QF14.x17 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16 and ((res = i3217 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17) or 
	 (QF14.x18 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17 and ((res = i3218 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18) or 
	 (QF14.x19 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18 and ((res = i3219 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19) or 
	 (QF14.x20 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19 and ((res = i3220 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14-QF14.x15-QF14.x16-QF14.x17-QF14.x18-QF14.x19-QF14.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF24 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize24[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF24.x1 in s and ((res = i321 and no s-QF24.x1) or 
	 (QF24.x2 in s-QF24.x1 and ((res = i322 and no s-QF24.x1-QF24.x2) or 
	 (QF24.x3 in s-QF24.x1-QF24.x2 and ((res = i323 and no s-QF24.x1-QF24.x2-QF24.x3) or 
	 (QF24.x4 in s-QF24.x1-QF24.x2-QF24.x3 and ((res = i324 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4) or 
	 (QF24.x5 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4 and ((res = i325 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5) or 
	 (QF24.x6 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5 and ((res = i326 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6) or 
	 (QF24.x7 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6 and ((res = i327 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7) or 
	 (QF24.x8 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7 and ((res = i328 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8) or 
	 (QF24.x9 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8 and ((res = i329 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9) or 
	 (QF24.x10 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9 and ((res = i3210 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10) or 
	 (QF24.x11 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10 and ((res = i3211 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11) or 
	 (QF24.x12 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11 and ((res = i3212 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12) or 
	 (QF24.x13 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12 and ((res = i3213 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13) or 
	 (QF24.x14 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13 and ((res = i3214 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14) or 
	 (QF24.x15 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14 and ((res = i3215 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15) or 
	 (QF24.x16 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15 and ((res = i3216 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16) or 
	 (QF24.x17 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16 and ((res = i3217 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16-QF24.x17) or 
	 (QF24.x18 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16-QF24.x17 and ((res = i3218 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16-QF24.x17-QF24.x18) or 
	 (QF24.x19 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16-QF24.x17-QF24.x18 and ((res = i3219 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16-QF24.x17-QF24.x18-QF24.x19) or 
	 (QF24.x20 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16-QF24.x17-QF24.x18-QF24.x19 and ((res = i3220 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13-QF24.x14-QF24.x15-QF24.x16-QF24.x17-QF24.x18-QF24.x19-QF24.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF34 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize34[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF34.x1 in s and ((res = i321 and no s-QF34.x1) or 
	 (QF34.x2 in s-QF34.x1 and ((res = i322 and no s-QF34.x1-QF34.x2) or 
	 (QF34.x3 in s-QF34.x1-QF34.x2 and ((res = i323 and no s-QF34.x1-QF34.x2-QF34.x3) or 
	 (QF34.x4 in s-QF34.x1-QF34.x2-QF34.x3 and ((res = i324 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4) or 
	 (QF34.x5 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4 and ((res = i325 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5) or 
	 (QF34.x6 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5 and ((res = i326 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6) or 
	 (QF34.x7 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6 and ((res = i327 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7) or 
	 (QF34.x8 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7 and ((res = i328 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8) or 
	 (QF34.x9 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8 and ((res = i329 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9) or 
	 (QF34.x10 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9 and ((res = i3210 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10) or 
	 (QF34.x11 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10 and ((res = i3211 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11) or 
	 (QF34.x12 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11 and ((res = i3212 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12) or 
	 (QF34.x13 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12 and ((res = i3213 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13) or 
	 (QF34.x14 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13 and ((res = i3214 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14) or 
	 (QF34.x15 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14 and ((res = i3215 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15) or 
	 (QF34.x16 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15 and ((res = i3216 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16) or 
	 (QF34.x17 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16 and ((res = i3217 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16-QF34.x17) or 
	 (QF34.x18 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16-QF34.x17 and ((res = i3218 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16-QF34.x17-QF34.x18) or 
	 (QF34.x19 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16-QF34.x17-QF34.x18 and ((res = i3219 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16-QF34.x17-QF34.x18-QF34.x19) or 
	 (QF34.x20 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16-QF34.x17-QF34.x18-QF34.x19 and ((res = i3220 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13-QF34.x14-QF34.x15-QF34.x16-QF34.x17-QF34.x18-QF34.x19-QF34.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF15 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize15[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF15.x1 in s and ((res = i321 and no s-QF15.x1) or 
	 (QF15.x2 in s-QF15.x1 and ((res = i322 and no s-QF15.x1-QF15.x2) or 
	 (QF15.x3 in s-QF15.x1-QF15.x2 and ((res = i323 and no s-QF15.x1-QF15.x2-QF15.x3) or 
	 (QF15.x4 in s-QF15.x1-QF15.x2-QF15.x3 and ((res = i324 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4) or 
	 (QF15.x5 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4 and ((res = i325 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5) or 
	 (QF15.x6 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5 and ((res = i326 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6) or 
	 (QF15.x7 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6 and ((res = i327 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7) or 
	 (QF15.x8 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7 and ((res = i328 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8) or 
	 (QF15.x9 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8 and ((res = i329 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9) or 
	 (QF15.x10 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9 and ((res = i3210 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10) or 
	 (QF15.x11 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10 and ((res = i3211 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11) or 
	 (QF15.x12 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11 and ((res = i3212 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12) or 
	 (QF15.x13 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12 and ((res = i3213 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13) or 
	 (QF15.x14 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13 and ((res = i3214 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14) or 
	 (QF15.x15 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14 and ((res = i3215 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15) or 
	 (QF15.x16 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15 and ((res = i3216 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16) or 
	 (QF15.x17 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16 and ((res = i3217 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17) or 
	 (QF15.x18 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17 and ((res = i3218 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18) or 
	 (QF15.x19 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18 and ((res = i3219 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19) or 
	 (QF15.x20 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19 and ((res = i3220 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14-QF15.x15-QF15.x16-QF15.x17-QF15.x18-QF15.x19-QF15.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF25 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize25[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF25.x1 in s and ((res = i321 and no s-QF25.x1) or 
	 (QF25.x2 in s-QF25.x1 and ((res = i322 and no s-QF25.x1-QF25.x2) or 
	 (QF25.x3 in s-QF25.x1-QF25.x2 and ((res = i323 and no s-QF25.x1-QF25.x2-QF25.x3) or 
	 (QF25.x4 in s-QF25.x1-QF25.x2-QF25.x3 and ((res = i324 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4) or 
	 (QF25.x5 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4 and ((res = i325 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5) or 
	 (QF25.x6 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5 and ((res = i326 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6) or 
	 (QF25.x7 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6 and ((res = i327 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7) or 
	 (QF25.x8 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7 and ((res = i328 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8) or 
	 (QF25.x9 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8 and ((res = i329 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9) or 
	 (QF25.x10 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9 and ((res = i3210 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10) or 
	 (QF25.x11 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10 and ((res = i3211 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11) or 
	 (QF25.x12 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11 and ((res = i3212 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12) or 
	 (QF25.x13 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12 and ((res = i3213 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13) or 
	 (QF25.x14 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13 and ((res = i3214 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14) or 
	 (QF25.x15 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14 and ((res = i3215 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15) or 
	 (QF25.x16 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15 and ((res = i3216 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16) or 
	 (QF25.x17 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16 and ((res = i3217 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16-QF25.x17) or 
	 (QF25.x18 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16-QF25.x17 and ((res = i3218 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16-QF25.x17-QF25.x18) or 
	 (QF25.x19 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16-QF25.x17-QF25.x18 and ((res = i3219 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16-QF25.x17-QF25.x18-QF25.x19) or 
	 (QF25.x20 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16-QF25.x17-QF25.x18-QF25.x19 and ((res = i3220 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13-QF25.x14-QF25.x15-QF25.x16-QF25.x17-QF25.x18-QF25.x19-QF25.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF35 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize35[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF35.x1 in s and ((res = i321 and no s-QF35.x1) or 
	 (QF35.x2 in s-QF35.x1 and ((res = i322 and no s-QF35.x1-QF35.x2) or 
	 (QF35.x3 in s-QF35.x1-QF35.x2 and ((res = i323 and no s-QF35.x1-QF35.x2-QF35.x3) or 
	 (QF35.x4 in s-QF35.x1-QF35.x2-QF35.x3 and ((res = i324 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4) or 
	 (QF35.x5 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4 and ((res = i325 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5) or 
	 (QF35.x6 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5 and ((res = i326 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6) or 
	 (QF35.x7 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6 and ((res = i327 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7) or 
	 (QF35.x8 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7 and ((res = i328 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8) or 
	 (QF35.x9 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8 and ((res = i329 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9) or 
	 (QF35.x10 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9 and ((res = i3210 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10) or 
	 (QF35.x11 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10 and ((res = i3211 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11) or 
	 (QF35.x12 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11 and ((res = i3212 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12) or 
	 (QF35.x13 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12 and ((res = i3213 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13) or 
	 (QF35.x14 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13 and ((res = i3214 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14) or 
	 (QF35.x15 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14 and ((res = i3215 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15) or 
	 (QF35.x16 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15 and ((res = i3216 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16) or 
	 (QF35.x17 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16 and ((res = i3217 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16-QF35.x17) or 
	 (QF35.x18 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16-QF35.x17 and ((res = i3218 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16-QF35.x17-QF35.x18) or 
	 (QF35.x19 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16-QF35.x17-QF35.x18 and ((res = i3219 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16-QF35.x17-QF35.x18-QF35.x19) or 
	 (QF35.x20 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16-QF35.x17-QF35.x18-QF35.x19 and ((res = i3220 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13-QF35.x14-QF35.x15-QF35.x16-QF35.x17-QF35.x18-QF35.x19-QF35.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF16 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize16[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF16.x1 in s and ((res = i321 and no s-QF16.x1) or 
	 (QF16.x2 in s-QF16.x1 and ((res = i322 and no s-QF16.x1-QF16.x2) or 
	 (QF16.x3 in s-QF16.x1-QF16.x2 and ((res = i323 and no s-QF16.x1-QF16.x2-QF16.x3) or 
	 (QF16.x4 in s-QF16.x1-QF16.x2-QF16.x3 and ((res = i324 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4) or 
	 (QF16.x5 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4 and ((res = i325 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5) or 
	 (QF16.x6 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5 and ((res = i326 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6) or 
	 (QF16.x7 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6 and ((res = i327 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7) or 
	 (QF16.x8 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7 and ((res = i328 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8) or 
	 (QF16.x9 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8 and ((res = i329 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9) or 
	 (QF16.x10 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9 and ((res = i3210 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10) or 
	 (QF16.x11 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10 and ((res = i3211 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11) or 
	 (QF16.x12 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11 and ((res = i3212 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12) or 
	 (QF16.x13 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12 and ((res = i3213 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13) or 
	 (QF16.x14 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13 and ((res = i3214 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14) or 
	 (QF16.x15 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14 and ((res = i3215 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15) or 
	 (QF16.x16 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15 and ((res = i3216 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16) or 
	 (QF16.x17 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16 and ((res = i3217 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17) or 
	 (QF16.x18 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17 and ((res = i3218 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18) or 
	 (QF16.x19 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18 and ((res = i3219 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19) or 
	 (QF16.x20 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19 and ((res = i3220 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14-QF16.x15-QF16.x16-QF16.x17-QF16.x18-QF16.x19-QF16.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF26 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize26[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF26.x1 in s and ((res = i321 and no s-QF26.x1) or 
	 (QF26.x2 in s-QF26.x1 and ((res = i322 and no s-QF26.x1-QF26.x2) or 
	 (QF26.x3 in s-QF26.x1-QF26.x2 and ((res = i323 and no s-QF26.x1-QF26.x2-QF26.x3) or 
	 (QF26.x4 in s-QF26.x1-QF26.x2-QF26.x3 and ((res = i324 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4) or 
	 (QF26.x5 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4 and ((res = i325 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5) or 
	 (QF26.x6 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5 and ((res = i326 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6) or 
	 (QF26.x7 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6 and ((res = i327 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7) or 
	 (QF26.x8 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7 and ((res = i328 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8) or 
	 (QF26.x9 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8 and ((res = i329 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9) or 
	 (QF26.x10 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9 and ((res = i3210 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10) or 
	 (QF26.x11 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10 and ((res = i3211 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11) or 
	 (QF26.x12 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11 and ((res = i3212 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12) or 
	 (QF26.x13 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12 and ((res = i3213 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13) or 
	 (QF26.x14 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13 and ((res = i3214 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14) or 
	 (QF26.x15 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14 and ((res = i3215 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15) or 
	 (QF26.x16 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15 and ((res = i3216 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16) or 
	 (QF26.x17 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16 and ((res = i3217 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16-QF26.x17) or 
	 (QF26.x18 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16-QF26.x17 and ((res = i3218 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16-QF26.x17-QF26.x18) or 
	 (QF26.x19 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16-QF26.x17-QF26.x18 and ((res = i3219 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16-QF26.x17-QF26.x18-QF26.x19) or 
	 (QF26.x20 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16-QF26.x17-QF26.x18-QF26.x19 and ((res = i3220 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13-QF26.x14-QF26.x15-QF26.x16-QF26.x17-QF26.x18-QF26.x19-QF26.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF36 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize36[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF36.x1 in s and ((res = i321 and no s-QF36.x1) or 
	 (QF36.x2 in s-QF36.x1 and ((res = i322 and no s-QF36.x1-QF36.x2) or 
	 (QF36.x3 in s-QF36.x1-QF36.x2 and ((res = i323 and no s-QF36.x1-QF36.x2-QF36.x3) or 
	 (QF36.x4 in s-QF36.x1-QF36.x2-QF36.x3 and ((res = i324 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4) or 
	 (QF36.x5 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4 and ((res = i325 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5) or 
	 (QF36.x6 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5 and ((res = i326 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6) or 
	 (QF36.x7 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6 and ((res = i327 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7) or 
	 (QF36.x8 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7 and ((res = i328 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8) or 
	 (QF36.x9 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8 and ((res = i329 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9) or 
	 (QF36.x10 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9 and ((res = i3210 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10) or 
	 (QF36.x11 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10 and ((res = i3211 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11) or 
	 (QF36.x12 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11 and ((res = i3212 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12) or 
	 (QF36.x13 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12 and ((res = i3213 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13) or 
	 (QF36.x14 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13 and ((res = i3214 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14) or 
	 (QF36.x15 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14 and ((res = i3215 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15) or 
	 (QF36.x16 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15 and ((res = i3216 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16) or 
	 (QF36.x17 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16 and ((res = i3217 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16-QF36.x17) or 
	 (QF36.x18 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16-QF36.x17 and ((res = i3218 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16-QF36.x17-QF36.x18) or 
	 (QF36.x19 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16-QF36.x17-QF36.x18 and ((res = i3219 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16-QF36.x17-QF36.x18-QF36.x19) or 
	 (QF36.x20 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16-QF36.x17-QF36.x18-QF36.x19 and ((res = i3220 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13-QF36.x14-QF36.x15-QF36.x16-QF36.x17-QF36.x18-QF36.x19-QF36.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF17 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize17[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF17.x1 in s and ((res = i321 and no s-QF17.x1) or 
	 (QF17.x2 in s-QF17.x1 and ((res = i322 and no s-QF17.x1-QF17.x2) or 
	 (QF17.x3 in s-QF17.x1-QF17.x2 and ((res = i323 and no s-QF17.x1-QF17.x2-QF17.x3) or 
	 (QF17.x4 in s-QF17.x1-QF17.x2-QF17.x3 and ((res = i324 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4) or 
	 (QF17.x5 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4 and ((res = i325 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5) or 
	 (QF17.x6 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5 and ((res = i326 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6) or 
	 (QF17.x7 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6 and ((res = i327 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7) or 
	 (QF17.x8 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7 and ((res = i328 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8) or 
	 (QF17.x9 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8 and ((res = i329 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9) or 
	 (QF17.x10 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9 and ((res = i3210 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10) or 
	 (QF17.x11 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10 and ((res = i3211 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11) or 
	 (QF17.x12 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11 and ((res = i3212 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12) or 
	 (QF17.x13 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12 and ((res = i3213 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13) or 
	 (QF17.x14 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13 and ((res = i3214 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14) or 
	 (QF17.x15 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14 and ((res = i3215 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15) or 
	 (QF17.x16 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15 and ((res = i3216 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16) or 
	 (QF17.x17 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16 and ((res = i3217 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17) or 
	 (QF17.x18 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17 and ((res = i3218 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18) or 
	 (QF17.x19 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18 and ((res = i3219 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19) or 
	 (QF17.x20 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19 and ((res = i3220 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14-QF17.x15-QF17.x16-QF17.x17-QF17.x18-QF17.x19-QF17.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF27 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize27[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF27.x1 in s and ((res = i321 and no s-QF27.x1) or 
	 (QF27.x2 in s-QF27.x1 and ((res = i322 and no s-QF27.x1-QF27.x2) or 
	 (QF27.x3 in s-QF27.x1-QF27.x2 and ((res = i323 and no s-QF27.x1-QF27.x2-QF27.x3) or 
	 (QF27.x4 in s-QF27.x1-QF27.x2-QF27.x3 and ((res = i324 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4) or 
	 (QF27.x5 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4 and ((res = i325 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5) or 
	 (QF27.x6 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5 and ((res = i326 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6) or 
	 (QF27.x7 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6 and ((res = i327 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7) or 
	 (QF27.x8 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7 and ((res = i328 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8) or 
	 (QF27.x9 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8 and ((res = i329 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9) or 
	 (QF27.x10 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9 and ((res = i3210 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10) or 
	 (QF27.x11 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10 and ((res = i3211 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11) or 
	 (QF27.x12 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11 and ((res = i3212 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12) or 
	 (QF27.x13 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12 and ((res = i3213 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13) or 
	 (QF27.x14 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13 and ((res = i3214 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14) or 
	 (QF27.x15 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14 and ((res = i3215 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15) or 
	 (QF27.x16 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15 and ((res = i3216 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16) or 
	 (QF27.x17 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16 and ((res = i3217 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16-QF27.x17) or 
	 (QF27.x18 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16-QF27.x17 and ((res = i3218 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16-QF27.x17-QF27.x18) or 
	 (QF27.x19 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16-QF27.x17-QF27.x18 and ((res = i3219 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16-QF27.x17-QF27.x18-QF27.x19) or 
	 (QF27.x20 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16-QF27.x17-QF27.x18-QF27.x19 and ((res = i3220 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13-QF27.x14-QF27.x15-QF27.x16-QF27.x17-QF27.x18-QF27.x19-QF27.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF37 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize37[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF37.x1 in s and ((res = i321 and no s-QF37.x1) or 
	 (QF37.x2 in s-QF37.x1 and ((res = i322 and no s-QF37.x1-QF37.x2) or 
	 (QF37.x3 in s-QF37.x1-QF37.x2 and ((res = i323 and no s-QF37.x1-QF37.x2-QF37.x3) or 
	 (QF37.x4 in s-QF37.x1-QF37.x2-QF37.x3 and ((res = i324 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4) or 
	 (QF37.x5 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4 and ((res = i325 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5) or 
	 (QF37.x6 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5 and ((res = i326 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6) or 
	 (QF37.x7 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6 and ((res = i327 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7) or 
	 (QF37.x8 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7 and ((res = i328 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8) or 
	 (QF37.x9 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8 and ((res = i329 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9) or 
	 (QF37.x10 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9 and ((res = i3210 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10) or 
	 (QF37.x11 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10 and ((res = i3211 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11) or 
	 (QF37.x12 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11 and ((res = i3212 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12) or 
	 (QF37.x13 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12 and ((res = i3213 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13) or 
	 (QF37.x14 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13 and ((res = i3214 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14) or 
	 (QF37.x15 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14 and ((res = i3215 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15) or 
	 (QF37.x16 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15 and ((res = i3216 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16) or 
	 (QF37.x17 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16 and ((res = i3217 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16-QF37.x17) or 
	 (QF37.x18 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16-QF37.x17 and ((res = i3218 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16-QF37.x17-QF37.x18) or 
	 (QF37.x19 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16-QF37.x17-QF37.x18 and ((res = i3219 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16-QF37.x17-QF37.x18-QF37.x19) or 
	 (QF37.x20 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16-QF37.x17-QF37.x18-QF37.x19 and ((res = i3220 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13-QF37.x14-QF37.x15-QF37.x16-QF37.x17-QF37.x18-QF37.x19-QF37.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF18 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize18[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF18.x1 in s and ((res = i321 and no s-QF18.x1) or 
	 (QF18.x2 in s-QF18.x1 and ((res = i322 and no s-QF18.x1-QF18.x2) or 
	 (QF18.x3 in s-QF18.x1-QF18.x2 and ((res = i323 and no s-QF18.x1-QF18.x2-QF18.x3) or 
	 (QF18.x4 in s-QF18.x1-QF18.x2-QF18.x3 and ((res = i324 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4) or 
	 (QF18.x5 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4 and ((res = i325 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5) or 
	 (QF18.x6 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5 and ((res = i326 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6) or 
	 (QF18.x7 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6 and ((res = i327 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7) or 
	 (QF18.x8 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7 and ((res = i328 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8) or 
	 (QF18.x9 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8 and ((res = i329 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9) or 
	 (QF18.x10 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9 and ((res = i3210 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10) or 
	 (QF18.x11 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10 and ((res = i3211 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11) or 
	 (QF18.x12 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11 and ((res = i3212 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12) or 
	 (QF18.x13 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12 and ((res = i3213 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13) or 
	 (QF18.x14 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13 and ((res = i3214 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14) or 
	 (QF18.x15 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14 and ((res = i3215 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15) or 
	 (QF18.x16 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15 and ((res = i3216 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16) or 
	 (QF18.x17 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16 and ((res = i3217 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17) or 
	 (QF18.x18 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17 and ((res = i3218 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18) or 
	 (QF18.x19 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18 and ((res = i3219 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19) or 
	 (QF18.x20 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19 and ((res = i3220 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14-QF18.x15-QF18.x16-QF18.x17-QF18.x18-QF18.x19-QF18.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF28 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize28[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF28.x1 in s and ((res = i321 and no s-QF28.x1) or 
	 (QF28.x2 in s-QF28.x1 and ((res = i322 and no s-QF28.x1-QF28.x2) or 
	 (QF28.x3 in s-QF28.x1-QF28.x2 and ((res = i323 and no s-QF28.x1-QF28.x2-QF28.x3) or 
	 (QF28.x4 in s-QF28.x1-QF28.x2-QF28.x3 and ((res = i324 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4) or 
	 (QF28.x5 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4 and ((res = i325 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5) or 
	 (QF28.x6 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5 and ((res = i326 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6) or 
	 (QF28.x7 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6 and ((res = i327 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7) or 
	 (QF28.x8 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7 and ((res = i328 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8) or 
	 (QF28.x9 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8 and ((res = i329 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9) or 
	 (QF28.x10 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9 and ((res = i3210 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10) or 
	 (QF28.x11 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10 and ((res = i3211 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11) or 
	 (QF28.x12 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11 and ((res = i3212 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12) or 
	 (QF28.x13 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12 and ((res = i3213 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13) or 
	 (QF28.x14 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13 and ((res = i3214 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14) or 
	 (QF28.x15 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14 and ((res = i3215 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15) or 
	 (QF28.x16 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15 and ((res = i3216 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16) or 
	 (QF28.x17 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16 and ((res = i3217 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16-QF28.x17) or 
	 (QF28.x18 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16-QF28.x17 and ((res = i3218 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16-QF28.x17-QF28.x18) or 
	 (QF28.x19 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16-QF28.x17-QF28.x18 and ((res = i3219 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16-QF28.x17-QF28.x18-QF28.x19) or 
	 (QF28.x20 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16-QF28.x17-QF28.x18-QF28.x19 and ((res = i3220 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13-QF28.x14-QF28.x15-QF28.x16-QF28.x17-QF28.x18-QF28.x19-QF28.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF38 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize38[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF38.x1 in s and ((res = i321 and no s-QF38.x1) or 
	 (QF38.x2 in s-QF38.x1 and ((res = i322 and no s-QF38.x1-QF38.x2) or 
	 (QF38.x3 in s-QF38.x1-QF38.x2 and ((res = i323 and no s-QF38.x1-QF38.x2-QF38.x3) or 
	 (QF38.x4 in s-QF38.x1-QF38.x2-QF38.x3 and ((res = i324 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4) or 
	 (QF38.x5 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4 and ((res = i325 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5) or 
	 (QF38.x6 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5 and ((res = i326 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6) or 
	 (QF38.x7 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6 and ((res = i327 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7) or 
	 (QF38.x8 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7 and ((res = i328 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8) or 
	 (QF38.x9 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8 and ((res = i329 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9) or 
	 (QF38.x10 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9 and ((res = i3210 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10) or 
	 (QF38.x11 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10 and ((res = i3211 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11) or 
	 (QF38.x12 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11 and ((res = i3212 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12) or 
	 (QF38.x13 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12 and ((res = i3213 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13) or 
	 (QF38.x14 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13 and ((res = i3214 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14) or 
	 (QF38.x15 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14 and ((res = i3215 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15) or 
	 (QF38.x16 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15 and ((res = i3216 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16) or 
	 (QF38.x17 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16 and ((res = i3217 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16-QF38.x17) or 
	 (QF38.x18 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16-QF38.x17 and ((res = i3218 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16-QF38.x17-QF38.x18) or 
	 (QF38.x19 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16-QF38.x17-QF38.x18 and ((res = i3219 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16-QF38.x17-QF38.x18-QF38.x19) or 
	 (QF38.x20 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16-QF38.x17-QF38.x18-QF38.x19 and ((res = i3220 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13-QF38.x14-QF38.x15-QF38.x16-QF38.x17-QF38.x18-QF38.x19-QF38.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF19 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize19[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF19.x1 in s and ((res = i321 and no s-QF19.x1) or 
	 (QF19.x2 in s-QF19.x1 and ((res = i322 and no s-QF19.x1-QF19.x2) or 
	 (QF19.x3 in s-QF19.x1-QF19.x2 and ((res = i323 and no s-QF19.x1-QF19.x2-QF19.x3) or 
	 (QF19.x4 in s-QF19.x1-QF19.x2-QF19.x3 and ((res = i324 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4) or 
	 (QF19.x5 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4 and ((res = i325 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5) or 
	 (QF19.x6 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5 and ((res = i326 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6) or 
	 (QF19.x7 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6 and ((res = i327 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7) or 
	 (QF19.x8 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7 and ((res = i328 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8) or 
	 (QF19.x9 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8 and ((res = i329 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9) or 
	 (QF19.x10 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9 and ((res = i3210 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10) or 
	 (QF19.x11 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10 and ((res = i3211 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11) or 
	 (QF19.x12 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11 and ((res = i3212 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12) or 
	 (QF19.x13 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12 and ((res = i3213 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13) or 
	 (QF19.x14 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13 and ((res = i3214 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14) or 
	 (QF19.x15 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14 and ((res = i3215 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15) or 
	 (QF19.x16 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15 and ((res = i3216 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16) or 
	 (QF19.x17 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16 and ((res = i3217 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17) or 
	 (QF19.x18 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17 and ((res = i3218 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18) or 
	 (QF19.x19 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18 and ((res = i3219 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19) or 
	 (QF19.x20 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19 and ((res = i3220 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14-QF19.x15-QF19.x16-QF19.x17-QF19.x18-QF19.x19-QF19.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF29 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize29[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF29.x1 in s and ((res = i321 and no s-QF29.x1) or 
	 (QF29.x2 in s-QF29.x1 and ((res = i322 and no s-QF29.x1-QF29.x2) or 
	 (QF29.x3 in s-QF29.x1-QF29.x2 and ((res = i323 and no s-QF29.x1-QF29.x2-QF29.x3) or 
	 (QF29.x4 in s-QF29.x1-QF29.x2-QF29.x3 and ((res = i324 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4) or 
	 (QF29.x5 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4 and ((res = i325 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5) or 
	 (QF29.x6 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5 and ((res = i326 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6) or 
	 (QF29.x7 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6 and ((res = i327 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7) or 
	 (QF29.x8 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7 and ((res = i328 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8) or 
	 (QF29.x9 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8 and ((res = i329 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9) or 
	 (QF29.x10 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9 and ((res = i3210 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10) or 
	 (QF29.x11 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10 and ((res = i3211 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11) or 
	 (QF29.x12 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11 and ((res = i3212 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12) or 
	 (QF29.x13 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12 and ((res = i3213 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13) or 
	 (QF29.x14 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13 and ((res = i3214 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14) or 
	 (QF29.x15 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14 and ((res = i3215 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15) or 
	 (QF29.x16 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15 and ((res = i3216 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16) or 
	 (QF29.x17 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16 and ((res = i3217 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16-QF29.x17) or 
	 (QF29.x18 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16-QF29.x17 and ((res = i3218 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16-QF29.x17-QF29.x18) or 
	 (QF29.x19 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16-QF29.x17-QF29.x18 and ((res = i3219 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16-QF29.x17-QF29.x18-QF29.x19) or 
	 (QF29.x20 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16-QF29.x17-QF29.x18-QF29.x19 and ((res = i3220 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13-QF29.x14-QF29.x15-QF29.x16-QF29.x17-QF29.x18-QF29.x19-QF29.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF39 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize39[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF39.x1 in s and ((res = i321 and no s-QF39.x1) or 
	 (QF39.x2 in s-QF39.x1 and ((res = i322 and no s-QF39.x1-QF39.x2) or 
	 (QF39.x3 in s-QF39.x1-QF39.x2 and ((res = i323 and no s-QF39.x1-QF39.x2-QF39.x3) or 
	 (QF39.x4 in s-QF39.x1-QF39.x2-QF39.x3 and ((res = i324 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4) or 
	 (QF39.x5 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4 and ((res = i325 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5) or 
	 (QF39.x6 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5 and ((res = i326 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6) or 
	 (QF39.x7 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6 and ((res = i327 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7) or 
	 (QF39.x8 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7 and ((res = i328 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8) or 
	 (QF39.x9 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8 and ((res = i329 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9) or 
	 (QF39.x10 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9 and ((res = i3210 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10) or 
	 (QF39.x11 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10 and ((res = i3211 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11) or 
	 (QF39.x12 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11 and ((res = i3212 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12) or 
	 (QF39.x13 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12 and ((res = i3213 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13) or 
	 (QF39.x14 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13 and ((res = i3214 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14) or 
	 (QF39.x15 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14 and ((res = i3215 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15) or 
	 (QF39.x16 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15 and ((res = i3216 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16) or 
	 (QF39.x17 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16 and ((res = i3217 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16-QF39.x17) or 
	 (QF39.x18 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16-QF39.x17 and ((res = i3218 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16-QF39.x17-QF39.x18) or 
	 (QF39.x19 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16-QF39.x17-QF39.x18 and ((res = i3219 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16-QF39.x17-QF39.x18-QF39.x19) or 
	 (QF39.x20 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16-QF39.x17-QF39.x18-QF39.x19 and ((res = i3220 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13-QF39.x14-QF39.x15-QF39.x16-QF39.x17-QF39.x18-QF39.x19-QF39.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF110 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize110[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF110.x1 in s and ((res = i321 and no s-QF110.x1) or 
	 (QF110.x2 in s-QF110.x1 and ((res = i322 and no s-QF110.x1-QF110.x2) or 
	 (QF110.x3 in s-QF110.x1-QF110.x2 and ((res = i323 and no s-QF110.x1-QF110.x2-QF110.x3) or 
	 (QF110.x4 in s-QF110.x1-QF110.x2-QF110.x3 and ((res = i324 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4) or 
	 (QF110.x5 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4 and ((res = i325 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5) or 
	 (QF110.x6 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5 and ((res = i326 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6) or 
	 (QF110.x7 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6 and ((res = i327 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7) or 
	 (QF110.x8 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7 and ((res = i328 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8) or 
	 (QF110.x9 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8 and ((res = i329 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9) or 
	 (QF110.x10 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9 and ((res = i3210 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10) or 
	 (QF110.x11 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10 and ((res = i3211 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11) or 
	 (QF110.x12 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11 and ((res = i3212 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12) or 
	 (QF110.x13 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12 and ((res = i3213 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13) or 
	 (QF110.x14 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13 and ((res = i3214 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14) or 
	 (QF110.x15 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14 and ((res = i3215 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15) or 
	 (QF110.x16 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15 and ((res = i3216 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16) or 
	 (QF110.x17 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16 and ((res = i3217 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17) or 
	 (QF110.x18 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17 and ((res = i3218 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18) or 
	 (QF110.x19 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18 and ((res = i3219 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19) or 
	 (QF110.x20 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19 and ((res = i3220 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14-QF110.x15-QF110.x16-QF110.x17-QF110.x18-QF110.x19-QF110.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF210 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize210[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF210.x1 in s and ((res = i321 and no s-QF210.x1) or 
	 (QF210.x2 in s-QF210.x1 and ((res = i322 and no s-QF210.x1-QF210.x2) or 
	 (QF210.x3 in s-QF210.x1-QF210.x2 and ((res = i323 and no s-QF210.x1-QF210.x2-QF210.x3) or 
	 (QF210.x4 in s-QF210.x1-QF210.x2-QF210.x3 and ((res = i324 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4) or 
	 (QF210.x5 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4 and ((res = i325 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5) or 
	 (QF210.x6 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5 and ((res = i326 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6) or 
	 (QF210.x7 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6 and ((res = i327 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7) or 
	 (QF210.x8 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7 and ((res = i328 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8) or 
	 (QF210.x9 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8 and ((res = i329 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9) or 
	 (QF210.x10 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9 and ((res = i3210 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10) or 
	 (QF210.x11 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10 and ((res = i3211 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11) or 
	 (QF210.x12 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11 and ((res = i3212 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12) or 
	 (QF210.x13 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12 and ((res = i3213 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13) or 
	 (QF210.x14 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13 and ((res = i3214 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14) or 
	 (QF210.x15 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14 and ((res = i3215 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15) or 
	 (QF210.x16 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15 and ((res = i3216 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16) or 
	 (QF210.x17 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16 and ((res = i3217 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16-QF210.x17) or 
	 (QF210.x18 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16-QF210.x17 and ((res = i3218 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16-QF210.x17-QF210.x18) or 
	 (QF210.x19 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16-QF210.x17-QF210.x18 and ((res = i3219 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16-QF210.x17-QF210.x18-QF210.x19) or 
	 (QF210.x20 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16-QF210.x17-QF210.x18-QF210.x19 and ((res = i3220 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13-QF210.x14-QF210.x15-QF210.x16-QF210.x17-QF210.x18-QF210.x19-QF210.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF310 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize310[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF310.x1 in s and ((res = i321 and no s-QF310.x1) or 
	 (QF310.x2 in s-QF310.x1 and ((res = i322 and no s-QF310.x1-QF310.x2) or 
	 (QF310.x3 in s-QF310.x1-QF310.x2 and ((res = i323 and no s-QF310.x1-QF310.x2-QF310.x3) or 
	 (QF310.x4 in s-QF310.x1-QF310.x2-QF310.x3 and ((res = i324 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4) or 
	 (QF310.x5 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4 and ((res = i325 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5) or 
	 (QF310.x6 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5 and ((res = i326 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6) or 
	 (QF310.x7 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6 and ((res = i327 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7) or 
	 (QF310.x8 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7 and ((res = i328 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8) or 
	 (QF310.x9 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8 and ((res = i329 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9) or 
	 (QF310.x10 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9 and ((res = i3210 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10) or 
	 (QF310.x11 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10 and ((res = i3211 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11) or 
	 (QF310.x12 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11 and ((res = i3212 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12) or 
	 (QF310.x13 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12 and ((res = i3213 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13) or 
	 (QF310.x14 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13 and ((res = i3214 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14) or 
	 (QF310.x15 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14 and ((res = i3215 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15) or 
	 (QF310.x16 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15 and ((res = i3216 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16) or 
	 (QF310.x17 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16 and ((res = i3217 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16-QF310.x17) or 
	 (QF310.x18 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16-QF310.x17 and ((res = i3218 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16-QF310.x17-QF310.x18) or 
	 (QF310.x19 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16-QF310.x17-QF310.x18 and ((res = i3219 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16-QF310.x17-QF310.x18-QF310.x19) or 
	 (QF310.x20 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16-QF310.x17-QF310.x18-QF310.x19 and ((res = i3220 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13-QF310.x14-QF310.x15-QF310.x16-QF310.x17-QF310.x18-QF310.x19-QF310.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF111 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize111[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF111.x1 in s and ((res = i321 and no s-QF111.x1) or 
	 (QF111.x2 in s-QF111.x1 and ((res = i322 and no s-QF111.x1-QF111.x2) or 
	 (QF111.x3 in s-QF111.x1-QF111.x2 and ((res = i323 and no s-QF111.x1-QF111.x2-QF111.x3) or 
	 (QF111.x4 in s-QF111.x1-QF111.x2-QF111.x3 and ((res = i324 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4) or 
	 (QF111.x5 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4 and ((res = i325 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5) or 
	 (QF111.x6 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5 and ((res = i326 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6) or 
	 (QF111.x7 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6 and ((res = i327 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7) or 
	 (QF111.x8 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7 and ((res = i328 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8) or 
	 (QF111.x9 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8 and ((res = i329 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9) or 
	 (QF111.x10 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9 and ((res = i3210 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10) or 
	 (QF111.x11 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10 and ((res = i3211 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11) or 
	 (QF111.x12 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11 and ((res = i3212 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12) or 
	 (QF111.x13 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12 and ((res = i3213 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13) or 
	 (QF111.x14 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13 and ((res = i3214 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14) or 
	 (QF111.x15 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14 and ((res = i3215 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15) or 
	 (QF111.x16 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15 and ((res = i3216 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16) or 
	 (QF111.x17 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16 and ((res = i3217 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17) or 
	 (QF111.x18 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17 and ((res = i3218 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18) or 
	 (QF111.x19 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18 and ((res = i3219 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19) or 
	 (QF111.x20 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19 and ((res = i3220 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14-QF111.x15-QF111.x16-QF111.x17-QF111.x18-QF111.x19-QF111.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF211 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize211[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF211.x1 in s and ((res = i321 and no s-QF211.x1) or 
	 (QF211.x2 in s-QF211.x1 and ((res = i322 and no s-QF211.x1-QF211.x2) or 
	 (QF211.x3 in s-QF211.x1-QF211.x2 and ((res = i323 and no s-QF211.x1-QF211.x2-QF211.x3) or 
	 (QF211.x4 in s-QF211.x1-QF211.x2-QF211.x3 and ((res = i324 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4) or 
	 (QF211.x5 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4 and ((res = i325 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5) or 
	 (QF211.x6 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5 and ((res = i326 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6) or 
	 (QF211.x7 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6 and ((res = i327 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7) or 
	 (QF211.x8 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7 and ((res = i328 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8) or 
	 (QF211.x9 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8 and ((res = i329 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9) or 
	 (QF211.x10 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9 and ((res = i3210 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10) or 
	 (QF211.x11 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10 and ((res = i3211 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11) or 
	 (QF211.x12 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11 and ((res = i3212 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12) or 
	 (QF211.x13 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12 and ((res = i3213 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13) or 
	 (QF211.x14 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13 and ((res = i3214 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14) or 
	 (QF211.x15 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14 and ((res = i3215 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15) or 
	 (QF211.x16 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15 and ((res = i3216 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16) or 
	 (QF211.x17 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16 and ((res = i3217 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16-QF211.x17) or 
	 (QF211.x18 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16-QF211.x17 and ((res = i3218 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16-QF211.x17-QF211.x18) or 
	 (QF211.x19 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16-QF211.x17-QF211.x18 and ((res = i3219 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16-QF211.x17-QF211.x18-QF211.x19) or 
	 (QF211.x20 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16-QF211.x17-QF211.x18-QF211.x19 and ((res = i3220 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13-QF211.x14-QF211.x15-QF211.x16-QF211.x17-QF211.x18-QF211.x19-QF211.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF311 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize311[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF311.x1 in s and ((res = i321 and no s-QF311.x1) or 
	 (QF311.x2 in s-QF311.x1 and ((res = i322 and no s-QF311.x1-QF311.x2) or 
	 (QF311.x3 in s-QF311.x1-QF311.x2 and ((res = i323 and no s-QF311.x1-QF311.x2-QF311.x3) or 
	 (QF311.x4 in s-QF311.x1-QF311.x2-QF311.x3 and ((res = i324 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4) or 
	 (QF311.x5 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4 and ((res = i325 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5) or 
	 (QF311.x6 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5 and ((res = i326 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6) or 
	 (QF311.x7 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6 and ((res = i327 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7) or 
	 (QF311.x8 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7 and ((res = i328 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8) or 
	 (QF311.x9 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8 and ((res = i329 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9) or 
	 (QF311.x10 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9 and ((res = i3210 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10) or 
	 (QF311.x11 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10 and ((res = i3211 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11) or 
	 (QF311.x12 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11 and ((res = i3212 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12) or 
	 (QF311.x13 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12 and ((res = i3213 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13) or 
	 (QF311.x14 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13 and ((res = i3214 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14) or 
	 (QF311.x15 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14 and ((res = i3215 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15) or 
	 (QF311.x16 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15 and ((res = i3216 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16) or 
	 (QF311.x17 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16 and ((res = i3217 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16-QF311.x17) or 
	 (QF311.x18 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16-QF311.x17 and ((res = i3218 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16-QF311.x17-QF311.x18) or 
	 (QF311.x19 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16-QF311.x17-QF311.x18 and ((res = i3219 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16-QF311.x17-QF311.x18-QF311.x19) or 
	 (QF311.x20 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16-QF311.x17-QF311.x18-QF311.x19 and ((res = i3220 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13-QF311.x14-QF311.x15-QF311.x16-QF311.x17-QF311.x18-QF311.x19-QF311.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF112 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize112[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF112.x1 in s and ((res = i321 and no s-QF112.x1) or 
	 (QF112.x2 in s-QF112.x1 and ((res = i322 and no s-QF112.x1-QF112.x2) or 
	 (QF112.x3 in s-QF112.x1-QF112.x2 and ((res = i323 and no s-QF112.x1-QF112.x2-QF112.x3) or 
	 (QF112.x4 in s-QF112.x1-QF112.x2-QF112.x3 and ((res = i324 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4) or 
	 (QF112.x5 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4 and ((res = i325 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5) or 
	 (QF112.x6 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5 and ((res = i326 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6) or 
	 (QF112.x7 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6 and ((res = i327 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7) or 
	 (QF112.x8 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7 and ((res = i328 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8) or 
	 (QF112.x9 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8 and ((res = i329 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9) or 
	 (QF112.x10 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9 and ((res = i3210 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10) or 
	 (QF112.x11 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10 and ((res = i3211 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11) or 
	 (QF112.x12 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11 and ((res = i3212 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12) or 
	 (QF112.x13 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12 and ((res = i3213 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13) or 
	 (QF112.x14 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13 and ((res = i3214 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14) or 
	 (QF112.x15 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14 and ((res = i3215 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15) or 
	 (QF112.x16 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15 and ((res = i3216 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16) or 
	 (QF112.x17 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16 and ((res = i3217 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17) or 
	 (QF112.x18 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17 and ((res = i3218 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18) or 
	 (QF112.x19 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18 and ((res = i3219 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19) or 
	 (QF112.x20 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19 and ((res = i3220 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14-QF112.x15-QF112.x16-QF112.x17-QF112.x18-QF112.x19-QF112.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF212 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize212[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF212.x1 in s and ((res = i321 and no s-QF212.x1) or 
	 (QF212.x2 in s-QF212.x1 and ((res = i322 and no s-QF212.x1-QF212.x2) or 
	 (QF212.x3 in s-QF212.x1-QF212.x2 and ((res = i323 and no s-QF212.x1-QF212.x2-QF212.x3) or 
	 (QF212.x4 in s-QF212.x1-QF212.x2-QF212.x3 and ((res = i324 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4) or 
	 (QF212.x5 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4 and ((res = i325 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5) or 
	 (QF212.x6 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5 and ((res = i326 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6) or 
	 (QF212.x7 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6 and ((res = i327 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7) or 
	 (QF212.x8 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7 and ((res = i328 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8) or 
	 (QF212.x9 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8 and ((res = i329 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9) or 
	 (QF212.x10 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9 and ((res = i3210 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10) or 
	 (QF212.x11 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10 and ((res = i3211 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11) or 
	 (QF212.x12 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11 and ((res = i3212 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12) or 
	 (QF212.x13 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12 and ((res = i3213 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13) or 
	 (QF212.x14 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13 and ((res = i3214 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14) or 
	 (QF212.x15 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14 and ((res = i3215 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15) or 
	 (QF212.x16 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15 and ((res = i3216 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16) or 
	 (QF212.x17 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16 and ((res = i3217 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16-QF212.x17) or 
	 (QF212.x18 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16-QF212.x17 and ((res = i3218 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16-QF212.x17-QF212.x18) or 
	 (QF212.x19 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16-QF212.x17-QF212.x18 and ((res = i3219 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16-QF212.x17-QF212.x18-QF212.x19) or 
	 (QF212.x20 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16-QF212.x17-QF212.x18-QF212.x19 and ((res = i3220 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13-QF212.x14-QF212.x15-QF212.x16-QF212.x17-QF212.x18-QF212.x19-QF212.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF312 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize312[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF312.x1 in s and ((res = i321 and no s-QF312.x1) or 
	 (QF312.x2 in s-QF312.x1 and ((res = i322 and no s-QF312.x1-QF312.x2) or 
	 (QF312.x3 in s-QF312.x1-QF312.x2 and ((res = i323 and no s-QF312.x1-QF312.x2-QF312.x3) or 
	 (QF312.x4 in s-QF312.x1-QF312.x2-QF312.x3 and ((res = i324 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4) or 
	 (QF312.x5 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4 and ((res = i325 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5) or 
	 (QF312.x6 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5 and ((res = i326 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6) or 
	 (QF312.x7 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6 and ((res = i327 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7) or 
	 (QF312.x8 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7 and ((res = i328 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8) or 
	 (QF312.x9 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8 and ((res = i329 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9) or 
	 (QF312.x10 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9 and ((res = i3210 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10) or 
	 (QF312.x11 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10 and ((res = i3211 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11) or 
	 (QF312.x12 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11 and ((res = i3212 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12) or 
	 (QF312.x13 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12 and ((res = i3213 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13) or 
	 (QF312.x14 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13 and ((res = i3214 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14) or 
	 (QF312.x15 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14 and ((res = i3215 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15) or 
	 (QF312.x16 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15 and ((res = i3216 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16) or 
	 (QF312.x17 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16 and ((res = i3217 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16-QF312.x17) or 
	 (QF312.x18 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16-QF312.x17 and ((res = i3218 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16-QF312.x17-QF312.x18) or 
	 (QF312.x19 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16-QF312.x17-QF312.x18 and ((res = i3219 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16-QF312.x17-QF312.x18-QF312.x19) or 
	 (QF312.x20 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16-QF312.x17-QF312.x18-QF312.x19 and ((res = i3220 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13-QF312.x14-QF312.x15-QF312.x16-QF312.x17-QF312.x18-QF312.x19-QF312.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF113 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize113[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF113.x1 in s and ((res = i321 and no s-QF113.x1) or 
	 (QF113.x2 in s-QF113.x1 and ((res = i322 and no s-QF113.x1-QF113.x2) or 
	 (QF113.x3 in s-QF113.x1-QF113.x2 and ((res = i323 and no s-QF113.x1-QF113.x2-QF113.x3) or 
	 (QF113.x4 in s-QF113.x1-QF113.x2-QF113.x3 and ((res = i324 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4) or 
	 (QF113.x5 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4 and ((res = i325 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5) or 
	 (QF113.x6 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5 and ((res = i326 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6) or 
	 (QF113.x7 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6 and ((res = i327 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7) or 
	 (QF113.x8 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7 and ((res = i328 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8) or 
	 (QF113.x9 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8 and ((res = i329 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9) or 
	 (QF113.x10 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9 and ((res = i3210 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10) or 
	 (QF113.x11 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10 and ((res = i3211 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11) or 
	 (QF113.x12 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11 and ((res = i3212 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12) or 
	 (QF113.x13 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12 and ((res = i3213 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13) or 
	 (QF113.x14 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13 and ((res = i3214 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14) or 
	 (QF113.x15 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14 and ((res = i3215 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15) or 
	 (QF113.x16 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15 and ((res = i3216 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16) or 
	 (QF113.x17 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16 and ((res = i3217 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17) or 
	 (QF113.x18 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17 and ((res = i3218 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18) or 
	 (QF113.x19 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18 and ((res = i3219 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19) or 
	 (QF113.x20 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19 and ((res = i3220 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14-QF113.x15-QF113.x16-QF113.x17-QF113.x18-QF113.x19-QF113.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF213 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize213[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF213.x1 in s and ((res = i321 and no s-QF213.x1) or 
	 (QF213.x2 in s-QF213.x1 and ((res = i322 and no s-QF213.x1-QF213.x2) or 
	 (QF213.x3 in s-QF213.x1-QF213.x2 and ((res = i323 and no s-QF213.x1-QF213.x2-QF213.x3) or 
	 (QF213.x4 in s-QF213.x1-QF213.x2-QF213.x3 and ((res = i324 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4) or 
	 (QF213.x5 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4 and ((res = i325 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5) or 
	 (QF213.x6 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5 and ((res = i326 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6) or 
	 (QF213.x7 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6 and ((res = i327 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7) or 
	 (QF213.x8 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7 and ((res = i328 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8) or 
	 (QF213.x9 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8 and ((res = i329 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9) or 
	 (QF213.x10 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9 and ((res = i3210 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10) or 
	 (QF213.x11 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10 and ((res = i3211 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11) or 
	 (QF213.x12 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11 and ((res = i3212 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12) or 
	 (QF213.x13 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12 and ((res = i3213 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13) or 
	 (QF213.x14 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13 and ((res = i3214 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14) or 
	 (QF213.x15 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14 and ((res = i3215 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15) or 
	 (QF213.x16 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15 and ((res = i3216 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16) or 
	 (QF213.x17 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16 and ((res = i3217 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16-QF213.x17) or 
	 (QF213.x18 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16-QF213.x17 and ((res = i3218 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16-QF213.x17-QF213.x18) or 
	 (QF213.x19 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16-QF213.x17-QF213.x18 and ((res = i3219 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16-QF213.x17-QF213.x18-QF213.x19) or 
	 (QF213.x20 in s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16-QF213.x17-QF213.x18-QF213.x19 and ((res = i3220 and no s-QF213.x1-QF213.x2-QF213.x3-QF213.x4-QF213.x5-QF213.x6-QF213.x7-QF213.x8-QF213.x9-QF213.x10-QF213.x11-QF213.x12-QF213.x13-QF213.x14-QF213.x15-QF213.x16-QF213.x17-QF213.x18-QF213.x19-QF213.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF313 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize313[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF313.x1 in s and ((res = i321 and no s-QF313.x1) or 
	 (QF313.x2 in s-QF313.x1 and ((res = i322 and no s-QF313.x1-QF313.x2) or 
	 (QF313.x3 in s-QF313.x1-QF313.x2 and ((res = i323 and no s-QF313.x1-QF313.x2-QF313.x3) or 
	 (QF313.x4 in s-QF313.x1-QF313.x2-QF313.x3 and ((res = i324 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4) or 
	 (QF313.x5 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4 and ((res = i325 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5) or 
	 (QF313.x6 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5 and ((res = i326 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6) or 
	 (QF313.x7 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6 and ((res = i327 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7) or 
	 (QF313.x8 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7 and ((res = i328 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8) or 
	 (QF313.x9 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8 and ((res = i329 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9) or 
	 (QF313.x10 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9 and ((res = i3210 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10) or 
	 (QF313.x11 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10 and ((res = i3211 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11) or 
	 (QF313.x12 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11 and ((res = i3212 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12) or 
	 (QF313.x13 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12 and ((res = i3213 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13) or 
	 (QF313.x14 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13 and ((res = i3214 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14) or 
	 (QF313.x15 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14 and ((res = i3215 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15) or 
	 (QF313.x16 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15 and ((res = i3216 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16) or 
	 (QF313.x17 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16 and ((res = i3217 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16-QF313.x17) or 
	 (QF313.x18 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16-QF313.x17 and ((res = i3218 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16-QF313.x17-QF313.x18) or 
	 (QF313.x19 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16-QF313.x17-QF313.x18 and ((res = i3219 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16-QF313.x17-QF313.x18-QF313.x19) or 
	 (QF313.x20 in s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16-QF313.x17-QF313.x18-QF313.x19 and ((res = i3220 and no s-QF313.x1-QF313.x2-QF313.x3-QF313.x4-QF313.x5-QF313.x6-QF313.x7-QF313.x8-QF313.x9-QF313.x10-QF313.x11-QF313.x12-QF313.x13-QF313.x14-QF313.x15-QF313.x16-QF313.x17-QF313.x18-QF313.x19-QF313.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF114 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize114[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF114.x1 in s and ((res = i321 and no s-QF114.x1) or 
	 (QF114.x2 in s-QF114.x1 and ((res = i322 and no s-QF114.x1-QF114.x2) or 
	 (QF114.x3 in s-QF114.x1-QF114.x2 and ((res = i323 and no s-QF114.x1-QF114.x2-QF114.x3) or 
	 (QF114.x4 in s-QF114.x1-QF114.x2-QF114.x3 and ((res = i324 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4) or 
	 (QF114.x5 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4 and ((res = i325 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5) or 
	 (QF114.x6 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5 and ((res = i326 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6) or 
	 (QF114.x7 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6 and ((res = i327 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7) or 
	 (QF114.x8 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7 and ((res = i328 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8) or 
	 (QF114.x9 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8 and ((res = i329 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9) or 
	 (QF114.x10 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9 and ((res = i3210 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10) or 
	 (QF114.x11 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10 and ((res = i3211 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11) or 
	 (QF114.x12 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11 and ((res = i3212 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12) or 
	 (QF114.x13 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12 and ((res = i3213 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13) or 
	 (QF114.x14 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13 and ((res = i3214 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14) or 
	 (QF114.x15 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14 and ((res = i3215 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15) or 
	 (QF114.x16 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15 and ((res = i3216 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16) or 
	 (QF114.x17 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16 and ((res = i3217 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17) or 
	 (QF114.x18 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17 and ((res = i3218 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18) or 
	 (QF114.x19 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18 and ((res = i3219 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19) or 
	 (QF114.x20 in s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19 and ((res = i3220 and no s-QF114.x1-QF114.x2-QF114.x3-QF114.x4-QF114.x5-QF114.x6-QF114.x7-QF114.x8-QF114.x9-QF114.x10-QF114.x11-QF114.x12-QF114.x13-QF114.x14-QF114.x15-QF114.x16-QF114.x17-QF114.x18-QF114.x19-QF114.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF214 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize214[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF214.x1 in s and ((res = i321 and no s-QF214.x1) or 
	 (QF214.x2 in s-QF214.x1 and ((res = i322 and no s-QF214.x1-QF214.x2) or 
	 (QF214.x3 in s-QF214.x1-QF214.x2 and ((res = i323 and no s-QF214.x1-QF214.x2-QF214.x3) or 
	 (QF214.x4 in s-QF214.x1-QF214.x2-QF214.x3 and ((res = i324 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4) or 
	 (QF214.x5 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4 and ((res = i325 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5) or 
	 (QF214.x6 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5 and ((res = i326 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6) or 
	 (QF214.x7 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6 and ((res = i327 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7) or 
	 (QF214.x8 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7 and ((res = i328 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8) or 
	 (QF214.x9 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8 and ((res = i329 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9) or 
	 (QF214.x10 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9 and ((res = i3210 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10) or 
	 (QF214.x11 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10 and ((res = i3211 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11) or 
	 (QF214.x12 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11 and ((res = i3212 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12) or 
	 (QF214.x13 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12 and ((res = i3213 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13) or 
	 (QF214.x14 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13 and ((res = i3214 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14) or 
	 (QF214.x15 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14 and ((res = i3215 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15) or 
	 (QF214.x16 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15 and ((res = i3216 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16) or 
	 (QF214.x17 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16 and ((res = i3217 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16-QF214.x17) or 
	 (QF214.x18 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16-QF214.x17 and ((res = i3218 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16-QF214.x17-QF214.x18) or 
	 (QF214.x19 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16-QF214.x17-QF214.x18 and ((res = i3219 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16-QF214.x17-QF214.x18-QF214.x19) or 
	 (QF214.x20 in s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16-QF214.x17-QF214.x18-QF214.x19 and ((res = i3220 and no s-QF214.x1-QF214.x2-QF214.x3-QF214.x4-QF214.x5-QF214.x6-QF214.x7-QF214.x8-QF214.x9-QF214.x10-QF214.x11-QF214.x12-QF214.x13-QF214.x14-QF214.x15-QF214.x16-QF214.x17-QF214.x18-QF214.x19-QF214.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF314 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize314[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF314.x1 in s and ((res = i321 and no s-QF314.x1) or 
	 (QF314.x2 in s-QF314.x1 and ((res = i322 and no s-QF314.x1-QF314.x2) or 
	 (QF314.x3 in s-QF314.x1-QF314.x2 and ((res = i323 and no s-QF314.x1-QF314.x2-QF314.x3) or 
	 (QF314.x4 in s-QF314.x1-QF314.x2-QF314.x3 and ((res = i324 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4) or 
	 (QF314.x5 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4 and ((res = i325 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5) or 
	 (QF314.x6 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5 and ((res = i326 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6) or 
	 (QF314.x7 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6 and ((res = i327 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7) or 
	 (QF314.x8 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7 and ((res = i328 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8) or 
	 (QF314.x9 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8 and ((res = i329 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9) or 
	 (QF314.x10 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9 and ((res = i3210 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10) or 
	 (QF314.x11 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10 and ((res = i3211 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11) or 
	 (QF314.x12 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11 and ((res = i3212 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12) or 
	 (QF314.x13 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12 and ((res = i3213 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13) or 
	 (QF314.x14 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13 and ((res = i3214 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14) or 
	 (QF314.x15 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14 and ((res = i3215 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15) or 
	 (QF314.x16 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15 and ((res = i3216 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16) or 
	 (QF314.x17 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16 and ((res = i3217 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16-QF314.x17) or 
	 (QF314.x18 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16-QF314.x17 and ((res = i3218 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16-QF314.x17-QF314.x18) or 
	 (QF314.x19 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16-QF314.x17-QF314.x18 and ((res = i3219 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16-QF314.x17-QF314.x18-QF314.x19) or 
	 (QF314.x20 in s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16-QF314.x17-QF314.x18-QF314.x19 and ((res = i3220 and no s-QF314.x1-QF314.x2-QF314.x3-QF314.x4-QF314.x5-QF314.x6-QF314.x7-QF314.x8-QF314.x9-QF314.x10-QF314.x11-QF314.x12-QF314.x13-QF314.x14-QF314.x15-QF314.x16-QF314.x17-QF314.x18-QF314.x19-QF314.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF115 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize115[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF115.x1 in s and ((res = i321 and no s-QF115.x1) or 
	 (QF115.x2 in s-QF115.x1 and ((res = i322 and no s-QF115.x1-QF115.x2) or 
	 (QF115.x3 in s-QF115.x1-QF115.x2 and ((res = i323 and no s-QF115.x1-QF115.x2-QF115.x3) or 
	 (QF115.x4 in s-QF115.x1-QF115.x2-QF115.x3 and ((res = i324 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4) or 
	 (QF115.x5 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4 and ((res = i325 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5) or 
	 (QF115.x6 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5 and ((res = i326 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6) or 
	 (QF115.x7 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6 and ((res = i327 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7) or 
	 (QF115.x8 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7 and ((res = i328 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8) or 
	 (QF115.x9 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8 and ((res = i329 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9) or 
	 (QF115.x10 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9 and ((res = i3210 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10) or 
	 (QF115.x11 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10 and ((res = i3211 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11) or 
	 (QF115.x12 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11 and ((res = i3212 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12) or 
	 (QF115.x13 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12 and ((res = i3213 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13) or 
	 (QF115.x14 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13 and ((res = i3214 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14) or 
	 (QF115.x15 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14 and ((res = i3215 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15) or 
	 (QF115.x16 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15 and ((res = i3216 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16) or 
	 (QF115.x17 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16 and ((res = i3217 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17) or 
	 (QF115.x18 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17 and ((res = i3218 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18) or 
	 (QF115.x19 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18 and ((res = i3219 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19) or 
	 (QF115.x20 in s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19 and ((res = i3220 and no s-QF115.x1-QF115.x2-QF115.x3-QF115.x4-QF115.x5-QF115.x6-QF115.x7-QF115.x8-QF115.x9-QF115.x10-QF115.x11-QF115.x12-QF115.x13-QF115.x14-QF115.x15-QF115.x16-QF115.x17-QF115.x18-QF115.x19-QF115.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF215 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize215[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF215.x1 in s and ((res = i321 and no s-QF215.x1) or 
	 (QF215.x2 in s-QF215.x1 and ((res = i322 and no s-QF215.x1-QF215.x2) or 
	 (QF215.x3 in s-QF215.x1-QF215.x2 and ((res = i323 and no s-QF215.x1-QF215.x2-QF215.x3) or 
	 (QF215.x4 in s-QF215.x1-QF215.x2-QF215.x3 and ((res = i324 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4) or 
	 (QF215.x5 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4 and ((res = i325 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5) or 
	 (QF215.x6 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5 and ((res = i326 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6) or 
	 (QF215.x7 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6 and ((res = i327 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7) or 
	 (QF215.x8 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7 and ((res = i328 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8) or 
	 (QF215.x9 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8 and ((res = i329 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9) or 
	 (QF215.x10 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9 and ((res = i3210 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10) or 
	 (QF215.x11 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10 and ((res = i3211 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11) or 
	 (QF215.x12 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11 and ((res = i3212 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12) or 
	 (QF215.x13 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12 and ((res = i3213 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13) or 
	 (QF215.x14 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13 and ((res = i3214 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14) or 
	 (QF215.x15 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14 and ((res = i3215 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15) or 
	 (QF215.x16 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15 and ((res = i3216 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16) or 
	 (QF215.x17 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16 and ((res = i3217 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16-QF215.x17) or 
	 (QF215.x18 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16-QF215.x17 and ((res = i3218 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16-QF215.x17-QF215.x18) or 
	 (QF215.x19 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16-QF215.x17-QF215.x18 and ((res = i3219 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16-QF215.x17-QF215.x18-QF215.x19) or 
	 (QF215.x20 in s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16-QF215.x17-QF215.x18-QF215.x19 and ((res = i3220 and no s-QF215.x1-QF215.x2-QF215.x3-QF215.x4-QF215.x5-QF215.x6-QF215.x7-QF215.x8-QF215.x9-QF215.x10-QF215.x11-QF215.x12-QF215.x13-QF215.x14-QF215.x15-QF215.x16-QF215.x17-QF215.x18-QF215.x19-QF215.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF315 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize315[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF315.x1 in s and ((res = i321 and no s-QF315.x1) or 
	 (QF315.x2 in s-QF315.x1 and ((res = i322 and no s-QF315.x1-QF315.x2) or 
	 (QF315.x3 in s-QF315.x1-QF315.x2 and ((res = i323 and no s-QF315.x1-QF315.x2-QF315.x3) or 
	 (QF315.x4 in s-QF315.x1-QF315.x2-QF315.x3 and ((res = i324 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4) or 
	 (QF315.x5 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4 and ((res = i325 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5) or 
	 (QF315.x6 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5 and ((res = i326 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6) or 
	 (QF315.x7 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6 and ((res = i327 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7) or 
	 (QF315.x8 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7 and ((res = i328 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8) or 
	 (QF315.x9 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8 and ((res = i329 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9) or 
	 (QF315.x10 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9 and ((res = i3210 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10) or 
	 (QF315.x11 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10 and ((res = i3211 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11) or 
	 (QF315.x12 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11 and ((res = i3212 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12) or 
	 (QF315.x13 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12 and ((res = i3213 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13) or 
	 (QF315.x14 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13 and ((res = i3214 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14) or 
	 (QF315.x15 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14 and ((res = i3215 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15) or 
	 (QF315.x16 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15 and ((res = i3216 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16) or 
	 (QF315.x17 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16 and ((res = i3217 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16-QF315.x17) or 
	 (QF315.x18 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16-QF315.x17 and ((res = i3218 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16-QF315.x17-QF315.x18) or 
	 (QF315.x19 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16-QF315.x17-QF315.x18 and ((res = i3219 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16-QF315.x17-QF315.x18-QF315.x19) or 
	 (QF315.x20 in s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16-QF315.x17-QF315.x18-QF315.x19 and ((res = i3220 and no s-QF315.x1-QF315.x2-QF315.x3-QF315.x4-QF315.x5-QF315.x6-QF315.x7-QF315.x8-QF315.x9-QF315.x10-QF315.x11-QF315.x12-QF315.x13-QF315.x14-QF315.x15-QF315.x16-QF315.x17-QF315.x18-QF315.x19-QF315.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF116 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize116[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF116.x1 in s and ((res = i321 and no s-QF116.x1) or 
	 (QF116.x2 in s-QF116.x1 and ((res = i322 and no s-QF116.x1-QF116.x2) or 
	 (QF116.x3 in s-QF116.x1-QF116.x2 and ((res = i323 and no s-QF116.x1-QF116.x2-QF116.x3) or 
	 (QF116.x4 in s-QF116.x1-QF116.x2-QF116.x3 and ((res = i324 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4) or 
	 (QF116.x5 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4 and ((res = i325 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5) or 
	 (QF116.x6 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5 and ((res = i326 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6) or 
	 (QF116.x7 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6 and ((res = i327 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7) or 
	 (QF116.x8 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7 and ((res = i328 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8) or 
	 (QF116.x9 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8 and ((res = i329 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9) or 
	 (QF116.x10 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9 and ((res = i3210 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10) or 
	 (QF116.x11 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10 and ((res = i3211 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11) or 
	 (QF116.x12 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11 and ((res = i3212 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12) or 
	 (QF116.x13 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12 and ((res = i3213 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13) or 
	 (QF116.x14 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13 and ((res = i3214 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14) or 
	 (QF116.x15 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14 and ((res = i3215 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15) or 
	 (QF116.x16 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15 and ((res = i3216 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16) or 
	 (QF116.x17 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16 and ((res = i3217 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17) or 
	 (QF116.x18 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17 and ((res = i3218 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18) or 
	 (QF116.x19 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18 and ((res = i3219 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19) or 
	 (QF116.x20 in s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19 and ((res = i3220 and no s-QF116.x1-QF116.x2-QF116.x3-QF116.x4-QF116.x5-QF116.x6-QF116.x7-QF116.x8-QF116.x9-QF116.x10-QF116.x11-QF116.x12-QF116.x13-QF116.x14-QF116.x15-QF116.x16-QF116.x17-QF116.x18-QF116.x19-QF116.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF216 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize216[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF216.x1 in s and ((res = i321 and no s-QF216.x1) or 
	 (QF216.x2 in s-QF216.x1 and ((res = i322 and no s-QF216.x1-QF216.x2) or 
	 (QF216.x3 in s-QF216.x1-QF216.x2 and ((res = i323 and no s-QF216.x1-QF216.x2-QF216.x3) or 
	 (QF216.x4 in s-QF216.x1-QF216.x2-QF216.x3 and ((res = i324 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4) or 
	 (QF216.x5 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4 and ((res = i325 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5) or 
	 (QF216.x6 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5 and ((res = i326 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6) or 
	 (QF216.x7 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6 and ((res = i327 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7) or 
	 (QF216.x8 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7 and ((res = i328 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8) or 
	 (QF216.x9 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8 and ((res = i329 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9) or 
	 (QF216.x10 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9 and ((res = i3210 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10) or 
	 (QF216.x11 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10 and ((res = i3211 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11) or 
	 (QF216.x12 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11 and ((res = i3212 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12) or 
	 (QF216.x13 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12 and ((res = i3213 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13) or 
	 (QF216.x14 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13 and ((res = i3214 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14) or 
	 (QF216.x15 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14 and ((res = i3215 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15) or 
	 (QF216.x16 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15 and ((res = i3216 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16) or 
	 (QF216.x17 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16 and ((res = i3217 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16-QF216.x17) or 
	 (QF216.x18 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16-QF216.x17 and ((res = i3218 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16-QF216.x17-QF216.x18) or 
	 (QF216.x19 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16-QF216.x17-QF216.x18 and ((res = i3219 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16-QF216.x17-QF216.x18-QF216.x19) or 
	 (QF216.x20 in s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16-QF216.x17-QF216.x18-QF216.x19 and ((res = i3220 and no s-QF216.x1-QF216.x2-QF216.x3-QF216.x4-QF216.x5-QF216.x6-QF216.x7-QF216.x8-QF216.x9-QF216.x10-QF216.x11-QF216.x12-QF216.x13-QF216.x14-QF216.x15-QF216.x16-QF216.x17-QF216.x18-QF216.x19-QF216.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF316 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize316[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF316.x1 in s and ((res = i321 and no s-QF316.x1) or 
	 (QF316.x2 in s-QF316.x1 and ((res = i322 and no s-QF316.x1-QF316.x2) or 
	 (QF316.x3 in s-QF316.x1-QF316.x2 and ((res = i323 and no s-QF316.x1-QF316.x2-QF316.x3) or 
	 (QF316.x4 in s-QF316.x1-QF316.x2-QF316.x3 and ((res = i324 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4) or 
	 (QF316.x5 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4 and ((res = i325 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5) or 
	 (QF316.x6 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5 and ((res = i326 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6) or 
	 (QF316.x7 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6 and ((res = i327 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7) or 
	 (QF316.x8 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7 and ((res = i328 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8) or 
	 (QF316.x9 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8 and ((res = i329 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9) or 
	 (QF316.x10 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9 and ((res = i3210 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10) or 
	 (QF316.x11 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10 and ((res = i3211 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11) or 
	 (QF316.x12 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11 and ((res = i3212 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12) or 
	 (QF316.x13 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12 and ((res = i3213 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13) or 
	 (QF316.x14 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13 and ((res = i3214 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14) or 
	 (QF316.x15 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14 and ((res = i3215 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15) or 
	 (QF316.x16 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15 and ((res = i3216 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16) or 
	 (QF316.x17 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16 and ((res = i3217 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16-QF316.x17) or 
	 (QF316.x18 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16-QF316.x17 and ((res = i3218 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16-QF316.x17-QF316.x18) or 
	 (QF316.x19 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16-QF316.x17-QF316.x18 and ((res = i3219 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16-QF316.x17-QF316.x18-QF316.x19) or 
	 (QF316.x20 in s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16-QF316.x17-QF316.x18-QF316.x19 and ((res = i3220 and no s-QF316.x1-QF316.x2-QF316.x3-QF316.x4-QF316.x5-QF316.x6-QF316.x7-QF316.x8-QF316.x9-QF316.x10-QF316.x11-QF316.x12-QF316.x13-QF316.x14-QF316.x15-QF316.x16-QF316.x17-QF316.x18-QF316.x19-QF316.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF117 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize117[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF117.x1 in s and ((res = i321 and no s-QF117.x1) or 
	 (QF117.x2 in s-QF117.x1 and ((res = i322 and no s-QF117.x1-QF117.x2) or 
	 (QF117.x3 in s-QF117.x1-QF117.x2 and ((res = i323 and no s-QF117.x1-QF117.x2-QF117.x3) or 
	 (QF117.x4 in s-QF117.x1-QF117.x2-QF117.x3 and ((res = i324 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4) or 
	 (QF117.x5 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4 and ((res = i325 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5) or 
	 (QF117.x6 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5 and ((res = i326 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6) or 
	 (QF117.x7 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6 and ((res = i327 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7) or 
	 (QF117.x8 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7 and ((res = i328 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8) or 
	 (QF117.x9 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8 and ((res = i329 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9) or 
	 (QF117.x10 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9 and ((res = i3210 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10) or 
	 (QF117.x11 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10 and ((res = i3211 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11) or 
	 (QF117.x12 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11 and ((res = i3212 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12) or 
	 (QF117.x13 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12 and ((res = i3213 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13) or 
	 (QF117.x14 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13 and ((res = i3214 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14) or 
	 (QF117.x15 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14 and ((res = i3215 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15) or 
	 (QF117.x16 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15 and ((res = i3216 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16) or 
	 (QF117.x17 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16 and ((res = i3217 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17) or 
	 (QF117.x18 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17 and ((res = i3218 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18) or 
	 (QF117.x19 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18 and ((res = i3219 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19) or 
	 (QF117.x20 in s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19 and ((res = i3220 and no s-QF117.x1-QF117.x2-QF117.x3-QF117.x4-QF117.x5-QF117.x6-QF117.x7-QF117.x8-QF117.x9-QF117.x10-QF117.x11-QF117.x12-QF117.x13-QF117.x14-QF117.x15-QF117.x16-QF117.x17-QF117.x18-QF117.x19-QF117.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF217 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize217[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF217.x1 in s and ((res = i321 and no s-QF217.x1) or 
	 (QF217.x2 in s-QF217.x1 and ((res = i322 and no s-QF217.x1-QF217.x2) or 
	 (QF217.x3 in s-QF217.x1-QF217.x2 and ((res = i323 and no s-QF217.x1-QF217.x2-QF217.x3) or 
	 (QF217.x4 in s-QF217.x1-QF217.x2-QF217.x3 and ((res = i324 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4) or 
	 (QF217.x5 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4 and ((res = i325 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5) or 
	 (QF217.x6 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5 and ((res = i326 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6) or 
	 (QF217.x7 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6 and ((res = i327 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7) or 
	 (QF217.x8 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7 and ((res = i328 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8) or 
	 (QF217.x9 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8 and ((res = i329 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9) or 
	 (QF217.x10 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9 and ((res = i3210 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10) or 
	 (QF217.x11 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10 and ((res = i3211 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11) or 
	 (QF217.x12 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11 and ((res = i3212 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12) or 
	 (QF217.x13 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12 and ((res = i3213 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13) or 
	 (QF217.x14 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13 and ((res = i3214 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14) or 
	 (QF217.x15 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14 and ((res = i3215 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15) or 
	 (QF217.x16 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15 and ((res = i3216 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16) or 
	 (QF217.x17 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16 and ((res = i3217 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16-QF217.x17) or 
	 (QF217.x18 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16-QF217.x17 and ((res = i3218 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16-QF217.x17-QF217.x18) or 
	 (QF217.x19 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16-QF217.x17-QF217.x18 and ((res = i3219 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16-QF217.x17-QF217.x18-QF217.x19) or 
	 (QF217.x20 in s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16-QF217.x17-QF217.x18-QF217.x19 and ((res = i3220 and no s-QF217.x1-QF217.x2-QF217.x3-QF217.x4-QF217.x5-QF217.x6-QF217.x7-QF217.x8-QF217.x9-QF217.x10-QF217.x11-QF217.x12-QF217.x13-QF217.x14-QF217.x15-QF217.x16-QF217.x17-QF217.x18-QF217.x19-QF217.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF317 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize317[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF317.x1 in s and ((res = i321 and no s-QF317.x1) or 
	 (QF317.x2 in s-QF317.x1 and ((res = i322 and no s-QF317.x1-QF317.x2) or 
	 (QF317.x3 in s-QF317.x1-QF317.x2 and ((res = i323 and no s-QF317.x1-QF317.x2-QF317.x3) or 
	 (QF317.x4 in s-QF317.x1-QF317.x2-QF317.x3 and ((res = i324 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4) or 
	 (QF317.x5 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4 and ((res = i325 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5) or 
	 (QF317.x6 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5 and ((res = i326 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6) or 
	 (QF317.x7 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6 and ((res = i327 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7) or 
	 (QF317.x8 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7 and ((res = i328 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8) or 
	 (QF317.x9 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8 and ((res = i329 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9) or 
	 (QF317.x10 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9 and ((res = i3210 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10) or 
	 (QF317.x11 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10 and ((res = i3211 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11) or 
	 (QF317.x12 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11 and ((res = i3212 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12) or 
	 (QF317.x13 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12 and ((res = i3213 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13) or 
	 (QF317.x14 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13 and ((res = i3214 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14) or 
	 (QF317.x15 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14 and ((res = i3215 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15) or 
	 (QF317.x16 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15 and ((res = i3216 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16) or 
	 (QF317.x17 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16 and ((res = i3217 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16-QF317.x17) or 
	 (QF317.x18 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16-QF317.x17 and ((res = i3218 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16-QF317.x17-QF317.x18) or 
	 (QF317.x19 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16-QF317.x17-QF317.x18 and ((res = i3219 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16-QF317.x17-QF317.x18-QF317.x19) or 
	 (QF317.x20 in s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16-QF317.x17-QF317.x18-QF317.x19 and ((res = i3220 and no s-QF317.x1-QF317.x2-QF317.x3-QF317.x4-QF317.x5-QF317.x6-QF317.x7-QF317.x8-QF317.x9-QF317.x10-QF317.x11-QF317.x12-QF317.x13-QF317.x14-QF317.x15-QF317.x16-QF317.x17-QF317.x18-QF317.x19-QF317.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF118 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize118[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF118.x1 in s and ((res = i321 and no s-QF118.x1) or 
	 (QF118.x2 in s-QF118.x1 and ((res = i322 and no s-QF118.x1-QF118.x2) or 
	 (QF118.x3 in s-QF118.x1-QF118.x2 and ((res = i323 and no s-QF118.x1-QF118.x2-QF118.x3) or 
	 (QF118.x4 in s-QF118.x1-QF118.x2-QF118.x3 and ((res = i324 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4) or 
	 (QF118.x5 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4 and ((res = i325 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5) or 
	 (QF118.x6 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5 and ((res = i326 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6) or 
	 (QF118.x7 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6 and ((res = i327 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7) or 
	 (QF118.x8 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7 and ((res = i328 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8) or 
	 (QF118.x9 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8 and ((res = i329 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9) or 
	 (QF118.x10 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9 and ((res = i3210 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10) or 
	 (QF118.x11 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10 and ((res = i3211 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11) or 
	 (QF118.x12 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11 and ((res = i3212 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12) or 
	 (QF118.x13 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12 and ((res = i3213 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13) or 
	 (QF118.x14 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13 and ((res = i3214 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14) or 
	 (QF118.x15 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14 and ((res = i3215 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15) or 
	 (QF118.x16 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15 and ((res = i3216 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16) or 
	 (QF118.x17 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16 and ((res = i3217 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17) or 
	 (QF118.x18 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17 and ((res = i3218 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18) or 
	 (QF118.x19 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18 and ((res = i3219 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19) or 
	 (QF118.x20 in s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19 and ((res = i3220 and no s-QF118.x1-QF118.x2-QF118.x3-QF118.x4-QF118.x5-QF118.x6-QF118.x7-QF118.x8-QF118.x9-QF118.x10-QF118.x11-QF118.x12-QF118.x13-QF118.x14-QF118.x15-QF118.x16-QF118.x17-QF118.x18-QF118.x19-QF118.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF218 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize218[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF218.x1 in s and ((res = i321 and no s-QF218.x1) or 
	 (QF218.x2 in s-QF218.x1 and ((res = i322 and no s-QF218.x1-QF218.x2) or 
	 (QF218.x3 in s-QF218.x1-QF218.x2 and ((res = i323 and no s-QF218.x1-QF218.x2-QF218.x3) or 
	 (QF218.x4 in s-QF218.x1-QF218.x2-QF218.x3 and ((res = i324 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4) or 
	 (QF218.x5 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4 and ((res = i325 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5) or 
	 (QF218.x6 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5 and ((res = i326 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6) or 
	 (QF218.x7 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6 and ((res = i327 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7) or 
	 (QF218.x8 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7 and ((res = i328 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8) or 
	 (QF218.x9 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8 and ((res = i329 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9) or 
	 (QF218.x10 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9 and ((res = i3210 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10) or 
	 (QF218.x11 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10 and ((res = i3211 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11) or 
	 (QF218.x12 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11 and ((res = i3212 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12) or 
	 (QF218.x13 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12 and ((res = i3213 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13) or 
	 (QF218.x14 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13 and ((res = i3214 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14) or 
	 (QF218.x15 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14 and ((res = i3215 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15) or 
	 (QF218.x16 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15 and ((res = i3216 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16) or 
	 (QF218.x17 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16 and ((res = i3217 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16-QF218.x17) or 
	 (QF218.x18 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16-QF218.x17 and ((res = i3218 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16-QF218.x17-QF218.x18) or 
	 (QF218.x19 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16-QF218.x17-QF218.x18 and ((res = i3219 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16-QF218.x17-QF218.x18-QF218.x19) or 
	 (QF218.x20 in s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16-QF218.x17-QF218.x18-QF218.x19 and ((res = i3220 and no s-QF218.x1-QF218.x2-QF218.x3-QF218.x4-QF218.x5-QF218.x6-QF218.x7-QF218.x8-QF218.x9-QF218.x10-QF218.x11-QF218.x12-QF218.x13-QF218.x14-QF218.x15-QF218.x16-QF218.x17-QF218.x18-QF218.x19-QF218.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF318 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize318[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF318.x1 in s and ((res = i321 and no s-QF318.x1) or 
	 (QF318.x2 in s-QF318.x1 and ((res = i322 and no s-QF318.x1-QF318.x2) or 
	 (QF318.x3 in s-QF318.x1-QF318.x2 and ((res = i323 and no s-QF318.x1-QF318.x2-QF318.x3) or 
	 (QF318.x4 in s-QF318.x1-QF318.x2-QF318.x3 and ((res = i324 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4) or 
	 (QF318.x5 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4 and ((res = i325 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5) or 
	 (QF318.x6 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5 and ((res = i326 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6) or 
	 (QF318.x7 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6 and ((res = i327 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7) or 
	 (QF318.x8 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7 and ((res = i328 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8) or 
	 (QF318.x9 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8 and ((res = i329 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9) or 
	 (QF318.x10 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9 and ((res = i3210 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10) or 
	 (QF318.x11 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10 and ((res = i3211 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11) or 
	 (QF318.x12 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11 and ((res = i3212 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12) or 
	 (QF318.x13 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12 and ((res = i3213 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13) or 
	 (QF318.x14 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13 and ((res = i3214 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14) or 
	 (QF318.x15 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14 and ((res = i3215 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15) or 
	 (QF318.x16 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15 and ((res = i3216 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16) or 
	 (QF318.x17 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16 and ((res = i3217 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16-QF318.x17) or 
	 (QF318.x18 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16-QF318.x17 and ((res = i3218 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16-QF318.x17-QF318.x18) or 
	 (QF318.x19 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16-QF318.x17-QF318.x18 and ((res = i3219 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16-QF318.x17-QF318.x18-QF318.x19) or 
	 (QF318.x20 in s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16-QF318.x17-QF318.x18-QF318.x19 and ((res = i3220 and no s-QF318.x1-QF318.x2-QF318.x3-QF318.x4-QF318.x5-QF318.x6-QF318.x7-QF318.x8-QF318.x9-QF318.x10-QF318.x11-QF318.x12-QF318.x13-QF318.x14-QF318.x15-QF318.x16-QF318.x17-QF318.x18-QF318.x19-QF318.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF119 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize119[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF119.x1 in s and ((res = i321 and no s-QF119.x1) or 
	 (QF119.x2 in s-QF119.x1 and ((res = i322 and no s-QF119.x1-QF119.x2) or 
	 (QF119.x3 in s-QF119.x1-QF119.x2 and ((res = i323 and no s-QF119.x1-QF119.x2-QF119.x3) or 
	 (QF119.x4 in s-QF119.x1-QF119.x2-QF119.x3 and ((res = i324 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4) or 
	 (QF119.x5 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4 and ((res = i325 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5) or 
	 (QF119.x6 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5 and ((res = i326 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6) or 
	 (QF119.x7 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6 and ((res = i327 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7) or 
	 (QF119.x8 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7 and ((res = i328 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8) or 
	 (QF119.x9 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8 and ((res = i329 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9) or 
	 (QF119.x10 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9 and ((res = i3210 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10) or 
	 (QF119.x11 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10 and ((res = i3211 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11) or 
	 (QF119.x12 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11 and ((res = i3212 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12) or 
	 (QF119.x13 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12 and ((res = i3213 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13) or 
	 (QF119.x14 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13 and ((res = i3214 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14) or 
	 (QF119.x15 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14 and ((res = i3215 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15) or 
	 (QF119.x16 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15 and ((res = i3216 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16) or 
	 (QF119.x17 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16 and ((res = i3217 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17) or 
	 (QF119.x18 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17 and ((res = i3218 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18) or 
	 (QF119.x19 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18 and ((res = i3219 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19) or 
	 (QF119.x20 in s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19 and ((res = i3220 and no s-QF119.x1-QF119.x2-QF119.x3-QF119.x4-QF119.x5-QF119.x6-QF119.x7-QF119.x8-QF119.x9-QF119.x10-QF119.x11-QF119.x12-QF119.x13-QF119.x14-QF119.x15-QF119.x16-QF119.x17-QF119.x18-QF119.x19-QF119.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF219 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize219[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF219.x1 in s and ((res = i321 and no s-QF219.x1) or 
	 (QF219.x2 in s-QF219.x1 and ((res = i322 and no s-QF219.x1-QF219.x2) or 
	 (QF219.x3 in s-QF219.x1-QF219.x2 and ((res = i323 and no s-QF219.x1-QF219.x2-QF219.x3) or 
	 (QF219.x4 in s-QF219.x1-QF219.x2-QF219.x3 and ((res = i324 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4) or 
	 (QF219.x5 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4 and ((res = i325 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5) or 
	 (QF219.x6 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5 and ((res = i326 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6) or 
	 (QF219.x7 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6 and ((res = i327 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7) or 
	 (QF219.x8 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7 and ((res = i328 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8) or 
	 (QF219.x9 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8 and ((res = i329 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9) or 
	 (QF219.x10 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9 and ((res = i3210 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10) or 
	 (QF219.x11 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10 and ((res = i3211 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11) or 
	 (QF219.x12 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11 and ((res = i3212 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12) or 
	 (QF219.x13 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12 and ((res = i3213 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13) or 
	 (QF219.x14 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13 and ((res = i3214 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14) or 
	 (QF219.x15 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14 and ((res = i3215 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15) or 
	 (QF219.x16 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15 and ((res = i3216 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16) or 
	 (QF219.x17 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16 and ((res = i3217 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16-QF219.x17) or 
	 (QF219.x18 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16-QF219.x17 and ((res = i3218 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16-QF219.x17-QF219.x18) or 
	 (QF219.x19 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16-QF219.x17-QF219.x18 and ((res = i3219 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16-QF219.x17-QF219.x18-QF219.x19) or 
	 (QF219.x20 in s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16-QF219.x17-QF219.x18-QF219.x19 and ((res = i3220 and no s-QF219.x1-QF219.x2-QF219.x3-QF219.x4-QF219.x5-QF219.x6-QF219.x7-QF219.x8-QF219.x9-QF219.x10-QF219.x11-QF219.x12-QF219.x13-QF219.x14-QF219.x15-QF219.x16-QF219.x17-QF219.x18-QF219.x19-QF219.x20)
	))))))))))))))))))))))))))))))))))))))))
}
one sig QF319 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode,x14:BinHeapIntVarNode,x15:BinHeapIntVarNode,x16:BinHeapIntVarNode,x17:BinHeapIntVarNode,x18:BinHeapIntVarNode,x19:BinHeapIntVarNode,x20:BinHeapIntVarNode }

pred mysize319[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF319.x1 in s and ((res = i321 and no s-QF319.x1) or 
	 (QF319.x2 in s-QF319.x1 and ((res = i322 and no s-QF319.x1-QF319.x2) or 
	 (QF319.x3 in s-QF319.x1-QF319.x2 and ((res = i323 and no s-QF319.x1-QF319.x2-QF319.x3) or 
	 (QF319.x4 in s-QF319.x1-QF319.x2-QF319.x3 and ((res = i324 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4) or 
	 (QF319.x5 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4 and ((res = i325 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5) or 
	 (QF319.x6 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5 and ((res = i326 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6) or 
	 (QF319.x7 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6 and ((res = i327 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7) or 
	 (QF319.x8 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7 and ((res = i328 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8) or 
	 (QF319.x9 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8 and ((res = i329 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9) or 
	 (QF319.x10 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9 and ((res = i3210 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10) or 
	 (QF319.x11 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10 and ((res = i3211 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11) or 
	 (QF319.x12 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11 and ((res = i3212 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12) or 
	 (QF319.x13 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12 and ((res = i3213 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13) or 
	 (QF319.x14 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13 and ((res = i3214 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14) or 
	 (QF319.x15 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14 and ((res = i3215 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15) or 
	 (QF319.x16 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15 and ((res = i3216 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16) or 
	 (QF319.x17 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16 and ((res = i3217 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16-QF319.x17) or 
	 (QF319.x18 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16-QF319.x17 and ((res = i3218 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16-QF319.x17-QF319.x18) or 
	 (QF319.x19 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16-QF319.x17-QF319.x18 and ((res = i3219 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16-QF319.x17-QF319.x18-QF319.x19) or 
	 (QF319.x20 in s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16-QF319.x17-QF319.x18-QF319.x19 and ((res = i3220 and no s-QF319.x1-QF319.x2-QF319.x3-QF319.x4-QF319.x5-QF319.x6-QF319.x7-QF319.x8-QF319.x9-QF319.x10-QF319.x11-QF319.x12-QF319.x13-QF319.x14-QF319.x15-QF319.x16-QF319.x17-QF319.x18-QF319.x19-QF319.x20)
	))))))))))))))))))))))))))))))))))))))))
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 BinHeapIntVar, exactly 20 BinHeapIntVarNode, 1 int, exactly 21 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) {
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
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) {
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
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) {
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
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) {
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
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N6->(N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N7->(N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N8->(N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N9->(N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N10->(N11+N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N11->(N12+N13+N14+N15+N16+N17+N18+N19)
   +
   N12->(N13+N14+N15+N16+N17+N18+N19)
   +
   N13->(N14+N15+N16+N17+N18+N19)
   +
   N14->(N15+N16+N17+N18+N19)
   +
   N15->(N16+N17+N18+N19)
   +
   N16->(N17+N18+N19)
   +
   N17->(N18+N19)
   +
   N18->(N19)
 )
}




