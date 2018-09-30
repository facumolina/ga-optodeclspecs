module binheapintvar

open Integer4

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


fun FReach[] : set (N0+N1+N2+N3+N4) {
	(QF.thiz_0).(QF.head_0).*(QF.fsibling_0 + QF.fchild_0) - null
}


one sig N0,N1,N2,N3,N4 extends BinHeapIntVarNode {}


one sig i320,i321,i322,i323,i324,i325 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true in b00
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true in b02
}



fact { QF.fsibling_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->null+N1->N2+N1->N3+N1->N4+N1->null+N2->N3+N2->N4+N2->null+N3->N4+N3->null+N4->null }
fact { QF.fchild_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->null+N1->N2+N1->N3+N1->N4+N1->null+N2->N3+N2->N4+N2->null+N3->N4+N3->null+N4->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->null+N1->N2+N1->N3+N1->N4+N1->null+N2->N3+N2->N4+N2->null+N3->N4+N3->null+N4->null }
fact { QF.bsibling_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4 }
fact { QF.bchild_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4 }


fact {
	(QF.element_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->null
}


fact {
	(QF.degree_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->null
}


fact {
	(QF.size_0) in BinHeapIntVar->i320+BinHeapIntVar->i321+BinHeapIntVar->i322+BinHeapIntVar->i323+BinHeapIntVar->i324+BinHeapIntVar->i325
}




fun node_max[es: set (N0+N1+N2+N3+N4)] : lone (N0+N1+N2+N3+N4) {
 es - es.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
 )
}


fact {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (no m and size = i320) or 
	  (m = N0 and size = i321) or
	  (m = N1 and size = i322) or
	  (m = N2 and size = i323) or
	  (m = N3 and size = i324) or
	  (m = N4 and size = i325)
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

}
}
one sig QF10 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize10[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF10.x1 in s and ((res = i321 and no s-QF10.x1) or 
	 (QF10.x2 in s-QF10.x1 and ((res = i322 and no s-QF10.x1-QF10.x2) or 
	 (QF10.x3 in s-QF10.x1-QF10.x2 and ((res = i323 and no s-QF10.x1-QF10.x2-QF10.x3) or 
	 (QF10.x4 in s-QF10.x1-QF10.x2-QF10.x3 and ((res = i324 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4) or 
	 (QF10.x5 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4 and ((res = i325 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5)
	))))))))))
}
one sig QF20 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize20[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF20.x1 in s and ((res = i321 and no s-QF20.x1) or 
	 (QF20.x2 in s-QF20.x1 and ((res = i322 and no s-QF20.x1-QF20.x2) or 
	 (QF20.x3 in s-QF20.x1-QF20.x2 and ((res = i323 and no s-QF20.x1-QF20.x2-QF20.x3) or 
	 (QF20.x4 in s-QF20.x1-QF20.x2-QF20.x3 and ((res = i324 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4) or 
	 (QF20.x5 in s-QF20.x1-QF20.x2-QF20.x3-QF20.x4 and ((res = i325 and no s-QF20.x1-QF20.x2-QF20.x3-QF20.x4-QF20.x5)
	))))))))))
}
one sig QF30 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize30[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF30.x1 in s and ((res = i321 and no s-QF30.x1) or 
	 (QF30.x2 in s-QF30.x1 and ((res = i322 and no s-QF30.x1-QF30.x2) or 
	 (QF30.x3 in s-QF30.x1-QF30.x2 and ((res = i323 and no s-QF30.x1-QF30.x2-QF30.x3) or 
	 (QF30.x4 in s-QF30.x1-QF30.x2-QF30.x3 and ((res = i324 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4) or 
	 (QF30.x5 in s-QF30.x1-QF30.x2-QF30.x3-QF30.x4 and ((res = i325 and no s-QF30.x1-QF30.x2-QF30.x3-QF30.x4-QF30.x5)
	))))))))))
}
one sig QF11 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize11[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF11.x1 in s and ((res = i321 and no s-QF11.x1) or 
	 (QF11.x2 in s-QF11.x1 and ((res = i322 and no s-QF11.x1-QF11.x2) or 
	 (QF11.x3 in s-QF11.x1-QF11.x2 and ((res = i323 and no s-QF11.x1-QF11.x2-QF11.x3) or 
	 (QF11.x4 in s-QF11.x1-QF11.x2-QF11.x3 and ((res = i324 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4) or 
	 (QF11.x5 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4 and ((res = i325 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5)
	))))))))))
}
one sig QF21 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize21[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF21.x1 in s and ((res = i321 and no s-QF21.x1) or 
	 (QF21.x2 in s-QF21.x1 and ((res = i322 and no s-QF21.x1-QF21.x2) or 
	 (QF21.x3 in s-QF21.x1-QF21.x2 and ((res = i323 and no s-QF21.x1-QF21.x2-QF21.x3) or 
	 (QF21.x4 in s-QF21.x1-QF21.x2-QF21.x3 and ((res = i324 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4) or 
	 (QF21.x5 in s-QF21.x1-QF21.x2-QF21.x3-QF21.x4 and ((res = i325 and no s-QF21.x1-QF21.x2-QF21.x3-QF21.x4-QF21.x5)
	))))))))))
}
one sig QF31 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize31[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF31.x1 in s and ((res = i321 and no s-QF31.x1) or 
	 (QF31.x2 in s-QF31.x1 and ((res = i322 and no s-QF31.x1-QF31.x2) or 
	 (QF31.x3 in s-QF31.x1-QF31.x2 and ((res = i323 and no s-QF31.x1-QF31.x2-QF31.x3) or 
	 (QF31.x4 in s-QF31.x1-QF31.x2-QF31.x3 and ((res = i324 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4) or 
	 (QF31.x5 in s-QF31.x1-QF31.x2-QF31.x3-QF31.x4 and ((res = i325 and no s-QF31.x1-QF31.x2-QF31.x3-QF31.x4-QF31.x5)
	))))))))))
}
one sig QF12 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize12[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF12.x1 in s and ((res = i321 and no s-QF12.x1) or 
	 (QF12.x2 in s-QF12.x1 and ((res = i322 and no s-QF12.x1-QF12.x2) or 
	 (QF12.x3 in s-QF12.x1-QF12.x2 and ((res = i323 and no s-QF12.x1-QF12.x2-QF12.x3) or 
	 (QF12.x4 in s-QF12.x1-QF12.x2-QF12.x3 and ((res = i324 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4) or 
	 (QF12.x5 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4 and ((res = i325 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5)
	))))))))))
}
one sig QF22 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize22[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF22.x1 in s and ((res = i321 and no s-QF22.x1) or 
	 (QF22.x2 in s-QF22.x1 and ((res = i322 and no s-QF22.x1-QF22.x2) or 
	 (QF22.x3 in s-QF22.x1-QF22.x2 and ((res = i323 and no s-QF22.x1-QF22.x2-QF22.x3) or 
	 (QF22.x4 in s-QF22.x1-QF22.x2-QF22.x3 and ((res = i324 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4) or 
	 (QF22.x5 in s-QF22.x1-QF22.x2-QF22.x3-QF22.x4 and ((res = i325 and no s-QF22.x1-QF22.x2-QF22.x3-QF22.x4-QF22.x5)
	))))))))))
}
one sig QF32 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize32[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF32.x1 in s and ((res = i321 and no s-QF32.x1) or 
	 (QF32.x2 in s-QF32.x1 and ((res = i322 and no s-QF32.x1-QF32.x2) or 
	 (QF32.x3 in s-QF32.x1-QF32.x2 and ((res = i323 and no s-QF32.x1-QF32.x2-QF32.x3) or 
	 (QF32.x4 in s-QF32.x1-QF32.x2-QF32.x3 and ((res = i324 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4) or 
	 (QF32.x5 in s-QF32.x1-QF32.x2-QF32.x3-QF32.x4 and ((res = i325 and no s-QF32.x1-QF32.x2-QF32.x3-QF32.x4-QF32.x5)
	))))))))))
}
one sig QF13 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize13[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF13.x1 in s and ((res = i321 and no s-QF13.x1) or 
	 (QF13.x2 in s-QF13.x1 and ((res = i322 and no s-QF13.x1-QF13.x2) or 
	 (QF13.x3 in s-QF13.x1-QF13.x2 and ((res = i323 and no s-QF13.x1-QF13.x2-QF13.x3) or 
	 (QF13.x4 in s-QF13.x1-QF13.x2-QF13.x3 and ((res = i324 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4) or 
	 (QF13.x5 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4 and ((res = i325 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5)
	))))))))))
}
one sig QF23 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize23[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF23.x1 in s and ((res = i321 and no s-QF23.x1) or 
	 (QF23.x2 in s-QF23.x1 and ((res = i322 and no s-QF23.x1-QF23.x2) or 
	 (QF23.x3 in s-QF23.x1-QF23.x2 and ((res = i323 and no s-QF23.x1-QF23.x2-QF23.x3) or 
	 (QF23.x4 in s-QF23.x1-QF23.x2-QF23.x3 and ((res = i324 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4) or 
	 (QF23.x5 in s-QF23.x1-QF23.x2-QF23.x3-QF23.x4 and ((res = i325 and no s-QF23.x1-QF23.x2-QF23.x3-QF23.x4-QF23.x5)
	))))))))))
}
one sig QF33 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize33[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF33.x1 in s and ((res = i321 and no s-QF33.x1) or 
	 (QF33.x2 in s-QF33.x1 and ((res = i322 and no s-QF33.x1-QF33.x2) or 
	 (QF33.x3 in s-QF33.x1-QF33.x2 and ((res = i323 and no s-QF33.x1-QF33.x2-QF33.x3) or 
	 (QF33.x4 in s-QF33.x1-QF33.x2-QF33.x3 and ((res = i324 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4) or 
	 (QF33.x5 in s-QF33.x1-QF33.x2-QF33.x3-QF33.x4 and ((res = i325 and no s-QF33.x1-QF33.x2-QF33.x3-QF33.x4-QF33.x5)
	))))))))))
}
one sig QF14 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize14[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF14.x1 in s and ((res = i321 and no s-QF14.x1) or 
	 (QF14.x2 in s-QF14.x1 and ((res = i322 and no s-QF14.x1-QF14.x2) or 
	 (QF14.x3 in s-QF14.x1-QF14.x2 and ((res = i323 and no s-QF14.x1-QF14.x2-QF14.x3) or 
	 (QF14.x4 in s-QF14.x1-QF14.x2-QF14.x3 and ((res = i324 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4) or 
	 (QF14.x5 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4 and ((res = i325 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5)
	))))))))))
}
one sig QF24 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize24[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF24.x1 in s and ((res = i321 and no s-QF24.x1) or 
	 (QF24.x2 in s-QF24.x1 and ((res = i322 and no s-QF24.x1-QF24.x2) or 
	 (QF24.x3 in s-QF24.x1-QF24.x2 and ((res = i323 and no s-QF24.x1-QF24.x2-QF24.x3) or 
	 (QF24.x4 in s-QF24.x1-QF24.x2-QF24.x3 and ((res = i324 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4) or 
	 (QF24.x5 in s-QF24.x1-QF24.x2-QF24.x3-QF24.x4 and ((res = i325 and no s-QF24.x1-QF24.x2-QF24.x3-QF24.x4-QF24.x5)
	))))))))))
}
one sig QF34 { x1:BinHeapIntVarNode,x2:BinHeapIntVarNode,x3:BinHeapIntVarNode,x4:BinHeapIntVarNode,x5:BinHeapIntVarNode }

pred mysize34[s: set BinHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
	 (res = i320 and no s) or 
	 (QF34.x1 in s and ((res = i321 and no s-QF34.x1) or 
	 (QF34.x2 in s-QF34.x1 and ((res = i322 and no s-QF34.x1-QF34.x2) or 
	 (QF34.x3 in s-QF34.x1-QF34.x2 and ((res = i323 and no s-QF34.x1-QF34.x2-QF34.x3) or 
	 (QF34.x4 in s-QF34.x1-QF34.x2-QF34.x3 and ((res = i324 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4) or 
	 (QF34.x5 in s-QF34.x1-QF34.x2-QF34.x3-QF34.x4 and ((res = i325 and no s-QF34.x1-QF34.x2-QF34.x3-QF34.x4-QF34.x5)
	))))))))))
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 BinHeapIntVar, exactly 5 BinHeapIntVarNode, 1 int, exactly 6 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4) -> lone (N0+N1+N2+N3+N4) {
 N0->N1
 +
 N1->N2
 +
 N2->N3
 +
 N3->N4
}


fun node_prevs[e: N0+N1+N2+N3+N4] :set (N0+N1+N2+N3+N4) {
 e.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4] :set (N0+N1+N2+N3+N4) {
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
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4) -> set (N0+N1+N2+N3+N4) {
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
}


fun node_min[es: set (N0+N1+N2+N3+N4)] : lone (N0+N1+N2+N3+N4) {
 es - es.(
   N0->(N1+N2+N3+N4)
   +
   N1->(N2+N3+N4)
   +
   N2->(N3+N4)
   +
   N3->(N4)
 )
}




