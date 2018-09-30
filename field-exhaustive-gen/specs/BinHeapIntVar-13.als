module binheapintvar

open Integer5

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


fun FReach[] : set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
	(QF.thiz_0).(QF.head_0).*(QF.fsibling_0 + QF.fchild_0) - null
}


one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12 extends BinHeapIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329,i3210,i3211,i3212,i3213 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true in b00
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true in b02
}



fact { QF.fsibling_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->null+N9->N10+N9->N11+N9->N12+N9->null+N10->N11+N10->N12+N10->null+N11->N12+N11->null+N12->null }
fact { QF.fchild_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->null+N9->N10+N9->N11+N9->N12+N9->null+N10->N11+N10->N12+N10->null+N11->N12+N11->null+N12->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->null+N9->N10+N9->N11+N9->N12+N9->null+N10->N11+N10->N12+N10->null+N11->N12+N11->null+N12->null }
fact { QF.bsibling_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12 }
fact { QF.bchild_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12 }


fact {
	(QF.element_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->null
}


fact {
	(QF.degree_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->null
}


fact {
	(QF.size_0) in BinHeapIntVar->i320+BinHeapIntVar->i321+BinHeapIntVar->i322+BinHeapIntVar->i323+BinHeapIntVar->i324+BinHeapIntVar->i325+BinHeapIntVar->i326+BinHeapIntVar->i327+BinHeapIntVar->i328+BinHeapIntVar->i329+BinHeapIntVar->i3210+BinHeapIntVar->i3211+BinHeapIntVar->i3212+BinHeapIntVar->i3213
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
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
	  (m = N12 and size = i3213)
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

}
}
one sig QF10 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF10.x13 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12 and ((res = i3213 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13)
	))))))))))))))))))))))))))
}
one sig QF20 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF20.x13 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12 and ((res = i3213 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5-QF20.x6-QF20.x7-QF20.x8-QF20.x9-QF20.x10-QF20.x11-QF20.x12-QF20.x13)
	))))))))))))))))))))))))))
}
one sig QF30 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF30.x13 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12 and ((res = i3213 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5-QF30.x6-QF30.x7-QF30.x8-QF30.x9-QF30.x10-QF30.x11-QF30.x12-QF30.x13)
	))))))))))))))))))))))))))
}
one sig QF11 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF11.x13 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12 and ((res = i3213 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13)
	))))))))))))))))))))))))))
}
one sig QF21 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF21.x13 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12 and ((res = i3213 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5-QF21.x6-QF21.x7-QF21.x8-QF21.x9-QF21.x10-QF21.x11-QF21.x12-QF21.x13)
	))))))))))))))))))))))))))
}
one sig QF31 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF31.x13 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12 and ((res = i3213 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5-QF31.x6-QF31.x7-QF31.x8-QF31.x9-QF31.x10-QF31.x11-QF31.x12-QF31.x13)
	))))))))))))))))))))))))))
}
one sig QF12 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF12.x13 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12 and ((res = i3213 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13)
	))))))))))))))))))))))))))
}
one sig QF22 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF22.x13 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12 and ((res = i3213 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5-QF22.x6-QF22.x7-QF22.x8-QF22.x9-QF22.x10-QF22.x11-QF22.x12-QF22.x13)
	))))))))))))))))))))))))))
}
one sig QF32 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF32.x13 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12 and ((res = i3213 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5-QF32.x6-QF32.x7-QF32.x8-QF32.x9-QF32.x10-QF32.x11-QF32.x12-QF32.x13)
	))))))))))))))))))))))))))
}
one sig QF13 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF13.x13 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12 and ((res = i3213 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13)
	))))))))))))))))))))))))))
}
one sig QF23 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF23.x13 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12 and ((res = i3213 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5-QF23.x6-QF23.x7-QF23.x8-QF23.x9-QF23.x10-QF23.x11-QF23.x12-QF23.x13)
	))))))))))))))))))))))))))
}
one sig QF33 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF33.x13 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12 and ((res = i3213 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5-QF33.x6-QF33.x7-QF33.x8-QF33.x9-QF33.x10-QF33.x11-QF33.x12-QF33.x13)
	))))))))))))))))))))))))))
}
one sig QF14 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF14.x13 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12 and ((res = i3213 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13)
	))))))))))))))))))))))))))
}
one sig QF24 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF24.x13 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12 and ((res = i3213 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5-QF24.x6-QF24.x7-QF24.x8-QF24.x9-QF24.x10-QF24.x11-QF24.x12-QF24.x13)
	))))))))))))))))))))))))))
}
one sig QF34 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF34.x13 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12 and ((res = i3213 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5-QF34.x6-QF34.x7-QF34.x8-QF34.x9-QF34.x10-QF34.x11-QF34.x12-QF34.x13)
	))))))))))))))))))))))))))
}
one sig QF15 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF15.x13 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12 and ((res = i3213 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13)
	))))))))))))))))))))))))))
}
one sig QF25 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF25.x13 in s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12 and ((res = i3213 and no s-QF25.x1-QF25.x2-QF25.x3-QF25.x4-QF25.x5-QF25.x6-QF25.x7-QF25.x8-QF25.x9-QF25.x10-QF25.x11-QF25.x12-QF25.x13)
	))))))))))))))))))))))))))
}
one sig QF35 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF35.x13 in s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12 and ((res = i3213 and no s-QF35.x1-QF35.x2-QF35.x3-QF35.x4-QF35.x5-QF35.x6-QF35.x7-QF35.x8-QF35.x9-QF35.x10-QF35.x11-QF35.x12-QF35.x13)
	))))))))))))))))))))))))))
}
one sig QF16 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF16.x13 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12 and ((res = i3213 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13)
	))))))))))))))))))))))))))
}
one sig QF26 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF26.x13 in s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12 and ((res = i3213 and no s-QF26.x1-QF26.x2-QF26.x3-QF26.x4-QF26.x5-QF26.x6-QF26.x7-QF26.x8-QF26.x9-QF26.x10-QF26.x11-QF26.x12-QF26.x13)
	))))))))))))))))))))))))))
}
one sig QF36 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF36.x13 in s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12 and ((res = i3213 and no s-QF36.x1-QF36.x2-QF36.x3-QF36.x4-QF36.x5-QF36.x6-QF36.x7-QF36.x8-QF36.x9-QF36.x10-QF36.x11-QF36.x12-QF36.x13)
	))))))))))))))))))))))))))
}
one sig QF17 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF17.x13 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12 and ((res = i3213 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13)
	))))))))))))))))))))))))))
}
one sig QF27 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF27.x13 in s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12 and ((res = i3213 and no s-QF27.x1-QF27.x2-QF27.x3-QF27.x4-QF27.x5-QF27.x6-QF27.x7-QF27.x8-QF27.x9-QF27.x10-QF27.x11-QF27.x12-QF27.x13)
	))))))))))))))))))))))))))
}
one sig QF37 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF37.x13 in s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12 and ((res = i3213 and no s-QF37.x1-QF37.x2-QF37.x3-QF37.x4-QF37.x5-QF37.x6-QF37.x7-QF37.x8-QF37.x9-QF37.x10-QF37.x11-QF37.x12-QF37.x13)
	))))))))))))))))))))))))))
}
one sig QF18 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF18.x13 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12 and ((res = i3213 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13)
	))))))))))))))))))))))))))
}
one sig QF28 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF28.x13 in s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12 and ((res = i3213 and no s-QF28.x1-QF28.x2-QF28.x3-QF28.x4-QF28.x5-QF28.x6-QF28.x7-QF28.x8-QF28.x9-QF28.x10-QF28.x11-QF28.x12-QF28.x13)
	))))))))))))))))))))))))))
}
one sig QF38 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF38.x13 in s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12 and ((res = i3213 and no s-QF38.x1-QF38.x2-QF38.x3-QF38.x4-QF38.x5-QF38.x6-QF38.x7-QF38.x8-QF38.x9-QF38.x10-QF38.x11-QF38.x12-QF38.x13)
	))))))))))))))))))))))))))
}
one sig QF19 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF19.x13 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12 and ((res = i3213 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13)
	))))))))))))))))))))))))))
}
one sig QF29 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF29.x13 in s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12 and ((res = i3213 and no s-QF29.x1-QF29.x2-QF29.x3-QF29.x4-QF29.x5-QF29.x6-QF29.x7-QF29.x8-QF29.x9-QF29.x10-QF29.x11-QF29.x12-QF29.x13)
	))))))))))))))))))))))))))
}
one sig QF39 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF39.x13 in s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12 and ((res = i3213 and no s-QF39.x1-QF39.x2-QF39.x3-QF39.x4-QF39.x5-QF39.x6-QF39.x7-QF39.x8-QF39.x9-QF39.x10-QF39.x11-QF39.x12-QF39.x13)
	))))))))))))))))))))))))))
}
one sig QF110 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF110.x13 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12 and ((res = i3213 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13)
	))))))))))))))))))))))))))
}
one sig QF210 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF210.x13 in s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12 and ((res = i3213 and no s-QF210.x1-QF210.x2-QF210.x3-QF210.x4-QF210.x5-QF210.x6-QF210.x7-QF210.x8-QF210.x9-QF210.x10-QF210.x11-QF210.x12-QF210.x13)
	))))))))))))))))))))))))))
}
one sig QF310 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF310.x13 in s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12 and ((res = i3213 and no s-QF310.x1-QF310.x2-QF310.x3-QF310.x4-QF310.x5-QF310.x6-QF310.x7-QF310.x8-QF310.x9-QF310.x10-QF310.x11-QF310.x12-QF310.x13)
	))))))))))))))))))))))))))
}
one sig QF111 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF111.x13 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12 and ((res = i3213 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13)
	))))))))))))))))))))))))))
}
one sig QF211 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF211.x13 in s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12 and ((res = i3213 and no s-QF211.x1-QF211.x2-QF211.x3-QF211.x4-QF211.x5-QF211.x6-QF211.x7-QF211.x8-QF211.x9-QF211.x10-QF211.x11-QF211.x12-QF211.x13)
	))))))))))))))))))))))))))
}
one sig QF311 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF311.x13 in s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12 and ((res = i3213 and no s-QF311.x1-QF311.x2-QF311.x3-QF311.x4-QF311.x5-QF311.x6-QF311.x7-QF311.x8-QF311.x9-QF311.x10-QF311.x11-QF311.x12-QF311.x13)
	))))))))))))))))))))))))))
}
one sig QF112 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF112.x13 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12 and ((res = i3213 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13)
	))))))))))))))))))))))))))
}
one sig QF212 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF212.x13 in s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12 and ((res = i3213 and no s-QF212.x1-QF212.x2-QF212.x3-QF212.x4-QF212.x5-QF212.x6-QF212.x7-QF212.x8-QF212.x9-QF212.x10-QF212.x11-QF212.x12-QF212.x13)
	))))))))))))))))))))))))))
}
one sig QF312 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode,x6:BinHeapIntVarNode,x7:BinHeapIntVarNode,x8:BinHeapIntVarNode,x9:BinHeapIntVarNode,x10:BinHeapIntVarNode,x11:BinHeapIntVarNode,x12:BinHeapIntVarNode,x13:BinHeapIntVarNode }

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
	 (QF312.x13 in s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12 and ((res = i3213 and no s-QF312.x1-QF312.x2-QF312.x3-QF312.x4-QF312.x5-QF312.x6-QF312.x7-QF312.x8-QF312.x9-QF312.x10-QF312.x11-QF312.x12-QF312.x13)
	))))))))))))))))))))))))))
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 BinHeapIntVar, exactly 13 BinHeapIntVarNode, 1 int, exactly 14 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
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
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
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
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
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
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
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
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12)
   +
   N6->(N7+N8+N9+N10+N11+N12)
   +
   N7->(N8+N9+N10+N11+N12)
   +
   N8->(N9+N10+N11+N12)
   +
   N9->(N10+N11+N12)
   +
   N10->(N11+N12)
   +
   N11->(N12)
 )
}




