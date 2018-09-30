module fibheapintvar 

open Integer5

one sig null {}

one sig FibHeapIntVar {}

abstract sig FibHeapIntVarNode {}

one sig Mark {}

one sig QF {
  thiz_0 :    one FibHeapIntVar,
  nodes_0 :   FibHeapIntVar -> one (FibHeapIntVarNode + null),
  size_0 :    FibHeapIntVar -> one JavaPrimitiveIntegerValue,
  degree_0 :  FibHeapIntVarNode -> one JavaPrimitiveIntegerValue,

  fleft_0 :   FibHeapIntVarNode -> lone (FibHeapIntVarNode + null),
  bleft_0 :   FibHeapIntVarNode -> lone (FibHeapIntVarNode),

  fright_0 :  FibHeapIntVarNode -> lone (FibHeapIntVarNode + null),
  bright_0 :  FibHeapIntVarNode -> lone (FibHeapIntVarNode),

  fchild_0 :  FibHeapIntVarNode -> lone (FibHeapIntVarNode+null),
  bchild_0 :  FibHeapIntVarNode -> lone (FibHeapIntVarNode),

  fparent_0 : FibHeapIntVarNode -> lone (FibHeapIntVarNode+null),
  bparent_0 : FibHeapIntVarNode -> lone (FibHeapIntVarNode),

  mark_0 :    FibHeapIntVarNode -> one Mark,
  key_0 :     FibHeapIntVarNode -> one (JavaPrimitiveIntegerValue+null)
}

pred repOK [] {
  let thiz    = QF.thiz_0,
      nodes   = QF.nodes_0,
      degree  = QF.degree_0, 
      left    = QF.fleft_0 + QF.bleft_0,
      right   = QF.fright_0 + QF.bright_0,
      child   = QF.fchild_0 + QF.bchild_0,
      parent  = QF.fparent_0 + QF.bparent_0,
      mark    = QF.mark_0,
      key     = QF.key_0 | 
	
    
  (all n : FibHeapIntVarNode | n in thiz.nodes.*(child + right) implies
    (
      n.key != null
      and n !in (n.*right - n).child.*(child + right)
      and (n in thiz.nodes.*right implies (n.parent = null and pred_java_primitive_integer_value_lte[thiz.nodes.key, n.key]))
      and n.right != null
      and n.left != null
      and n.right.left = n	
      and n.left.right = n
      and (n. child = null => n.degree = i320)
//      and n.degree = #(n.child.*right - null)
      and ( all m : FibHeapIntVarNode | m in n.child.*(child + right) implies pred_java_primitive_integer_value_lte[n.key, m.key] )
          and ( n.child != null implies n.(child.*right).parent = n)
//          and ( n.child != null implies ( all o: n.child.*right | o.parent = n ))
    )
   )
   
}


fact {
  repOK[]
}


fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
}




fun globalMin[s : set (FibHeapIntVarNode + FibHeapIntVar)] : lone (FibHeapIntVarNode + FibHeapIntVar) {
	s - s.^(FibHeapIntVar->N0 + node_next[])
}

fun minP[n : FibHeapIntVarNode] : FibHeapIntVarNode {
	globalMin[(QF.fleft_0 + QF.fright_0 + QF.fchild_0 + QF.fparent_0 + QF.nodes_0).n ]
}

fun FReachSB[] : set univ {
  (QF.thiz_0).(QF.nodes_0).*(QF.fchild_0 + QF.fright_0 + QF.fleft_0 + QF.fparent_0) - null
}

fact { 
  let 	
    thiz    = QF.thiz_0,
    size    = QF.size_0, 
    nodes   = QF.nodes_0,
    degree  = QF.degree_0, 
    fleft   = QF.fleft_0,
    bleft   = QF.bleft_0,
    fright  = QF.fright_0,
    bright  = QF.bright_0,
    fchild  = QF.fchild_0,
    bchild  = QF.bchild_0,
    fparent = QF.fparent_0,
    bparent = QF.bparent_0,
    mark    = QF.mark_0,
    key			= QF.key_0 | 

 no ((fleft.univ) & (bleft.univ)) and     
 FibHeapIntVarNode = fleft.univ + bleft.univ and  

 no ((fright.univ) & (bright.univ)) and   
 FibHeapIntVarNode = fright.univ + bright.univ and

 no ((fchild.univ) & (bchild.univ)) and   
 FibHeapIntVarNode = fchild.univ + bchild.univ and

 no ((fparent.univ) & (bparent.univ)) and   
 FibHeapIntVarNode = fparent.univ + bparent.univ

}



/*
fact orderFibHeapIntVarNodeFibHeapIntVarParentCondition_c{
  all disj o1, o2 : FibHeapIntVarNode | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReachSB[] and some a and some b and
        a = b and a in FibHeapIntVar and o1 = a.(QF.nodes_0) and 
        o2 = a.(QF.minNode_0)) implies o2 = o1.node_next[]}
*/

fact orderFibHeapIntVarNodeCondition_c{
( all disj o1, o2, o3 : FibHeapIntVarNode |
  let a = minP[o1] | let b = minP[o2] | let c = minP[o3] |
  ( o1+o2+o3 in FReachSB[] and
    some a and some b and some c and a = b and b=c and a in FibHeapIntVarNode and
    o1 = a.(QF.fleft_0) and
    o2 = a.(QF.fchild_0) and
    o3 = a.(QF.fright_0)
  ) implies  (o2 = o1.node_next[] and o3 = o2.node_next[])
)
&&
( all disj o1, o2 : FibHeapIntVarNode |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReachSB[] 
		and	some a and some b and a = b and a in FibHeapIntVarNode
		and (no o3 : FibHeapIntVarNode | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and	o1 = a.(QF.fleft_0)
	) implies o2 = o1.node_next[]
)
&&
( all disj o1, o2 : FibHeapIntVarNode |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReachSB[] 
		and	some a and some b and a = b and a in FibHeapIntVarNode
		and (no o3 : FibHeapIntVarNode | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and o1 != a.(QF.fleft_0) and o2 != a.(QF.fleft_0) and o1 = a.(QF.fchild_0)
	) implies o2 = o1.node_next[]
)
}

fact orderFibHeapIntVarNodeCondition_d { 
  all disj o1, o2 : FibHeapIntVarNode | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReachSB[] and some a and some b and 
        a!=b and a+b in FibHeapIntVarNode and a in node_prevs[b]) 
           implies o1 in node_prevs[o2]
} 

fact orderFibHeapIntVarNodeCondition_e {
  all disj o1, o2 : FibHeapIntVarNode | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReachSB[] and some a and some b and 
        a in FibHeapIntVar and b in FibHeapIntVarNode) 
           implies o1 in node_prevs[o2]
}

fact compactFibHeapIntVarNode { 
  all o : FibHeapIntVarNode | o in FReachSB[] 
    implies node_prevs[o] in FReachSB[]
} 

fact fixUnreachable {
       all n : FibHeapIntVarNode | n !in (QF.thiz_0).(QF.nodes_0).*(QF.fleft_0 + QF.fright_0 + QF.fchild_0 + QF.fparent_0) implies 

                       (        n.(QF.degree_0) = i320 and
                               n.(QF.fleft_0) = null and
                               no n.(QF.bleft_0) and
                               n.(QF.fright_0) = null and
                               no n.(QF.bright_0) and
                               n.(QF.fchild_0) = null and
                               no n.(QF.bchild_0) and
                               n.(QF.fparent_0) = null and
                               no n.(QF.bparent_0) and
                               n.(QF.mark_0) = Mark and
                               n.(QF.key_0) = i320
                       )
}



fun FReach[] : set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) {
  (QF.thiz_0).(QF.nodes_0).*(QF.fchild_0 + QF.fright_0) - null
}
one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13 extends FibHeapIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329,i3210,i3211,i3212,i3213,i3214 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false+i3213->false+i3214->true in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false+i3213->true+i3214->false in b00
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false+i3213->false+i3214->false in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true+i3213->true+i3214->true in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true+i3213->true+i3214->true in b02
}



fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->null+N10->N11+N10->N12+N10->N13+N10->null+N11->N12+N11->N13+N11->null+N12->N13+N12->null+N13->null }
fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->null+N10->N11+N10->N12+N10->N13+N10->null+N11->N12+N11->N13+N11->null+N12->N13+N12->null+N13->null }
fact { QF.fchild_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->null+N10->N11+N10->N12+N10->N13+N10->null+N11->N12+N11->N13+N11->null+N12->N13+N12->null+N13->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->null+N10->N11+N10->N12+N10->N13+N10->null+N11->N12+N11->N13+N11->null+N12->N13+N12->null+N13->null }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13 }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13 }
fact { QF.bchild_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->null
}


fact {
	(QF.degree_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->null
}


fact {
	(QF.size_0) in FibHeapIntVar->i320+FibHeapIntVar->i321+FibHeapIntVar->i322+FibHeapIntVar->i323+FibHeapIntVar->i324+FibHeapIntVar->i325+FibHeapIntVar->i326+FibHeapIntVar->i327+FibHeapIntVar->i328+FibHeapIntVar->i329+FibHeapIntVar->i3210+FibHeapIntVar->i3211+FibHeapIntVar->i3212+FibHeapIntVar->i3213+FibHeapIntVar->i3214
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) {
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
	  (m = N13 and size = i3214)
}
fact {
let thiz    = QF.thiz_0, 
    nodes   = QF.nodes_0,
    degree  = QF.degree_0,
    right   = QF.fright_0 + QF.bright_0,
    child   = QF.fchild_0+QF.bchild_0
{

N0 in thiz.nodes.*(child + right) => (N0.child!=null => mysize10[(N0.child.*right - null),N0.degree])

N1 in thiz.nodes.*(child + right) => (N1.child!=null => mysize11[(N1.child.*right - null),N1.degree])

N2 in thiz.nodes.*(child + right) => (N2.child!=null => mysize12[(N2.child.*right - null),N2.degree])

N3 in thiz.nodes.*(child + right) => (N3.child!=null => mysize13[(N3.child.*right - null),N3.degree])

N4 in thiz.nodes.*(child + right) => (N4.child!=null => mysize14[(N4.child.*right - null),N4.degree])

N5 in thiz.nodes.*(child + right) => (N5.child!=null => mysize15[(N5.child.*right - null),N5.degree])

N6 in thiz.nodes.*(child + right) => (N6.child!=null => mysize16[(N6.child.*right - null),N6.degree])

N7 in thiz.nodes.*(child + right) => (N7.child!=null => mysize17[(N7.child.*right - null),N7.degree])

N8 in thiz.nodes.*(child + right) => (N8.child!=null => mysize18[(N8.child.*right - null),N8.degree])

N9 in thiz.nodes.*(child + right) => (N9.child!=null => mysize19[(N9.child.*right - null),N9.degree])

N10 in thiz.nodes.*(child + right) => (N10.child!=null => mysize110[(N10.child.*right - null),N10.degree])

N11 in thiz.nodes.*(child + right) => (N11.child!=null => mysize111[(N11.child.*right - null),N11.degree])

N12 in thiz.nodes.*(child + right) => (N12.child!=null => mysize112[(N12.child.*right - null),N12.degree])

N13 in thiz.nodes.*(child + right) => (N13.child!=null => mysize113[(N13.child.*right - null),N13.degree])

}
}
one sig QF10 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize10[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF10.x14 in s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13 and ((res = i3214 and no s-QF10.x1-QF10.x2-QF10.x3-QF10.x4-QF10.x5-QF10.x6-QF10.x7-QF10.x8-QF10.x9-QF10.x10-QF10.x11-QF10.x12-QF10.x13-QF10.x14)
	))))))))))))))))))))))))))))
}
one sig QF11 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize11[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF11.x14 in s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13 and ((res = i3214 and no s-QF11.x1-QF11.x2-QF11.x3-QF11.x4-QF11.x5-QF11.x6-QF11.x7-QF11.x8-QF11.x9-QF11.x10-QF11.x11-QF11.x12-QF11.x13-QF11.x14)
	))))))))))))))))))))))))))))
}
one sig QF12 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize12[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF12.x14 in s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13 and ((res = i3214 and no s-QF12.x1-QF12.x2-QF12.x3-QF12.x4-QF12.x5-QF12.x6-QF12.x7-QF12.x8-QF12.x9-QF12.x10-QF12.x11-QF12.x12-QF12.x13-QF12.x14)
	))))))))))))))))))))))))))))
}
one sig QF13 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize13[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF13.x14 in s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13 and ((res = i3214 and no s-QF13.x1-QF13.x2-QF13.x3-QF13.x4-QF13.x5-QF13.x6-QF13.x7-QF13.x8-QF13.x9-QF13.x10-QF13.x11-QF13.x12-QF13.x13-QF13.x14)
	))))))))))))))))))))))))))))
}
one sig QF14 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize14[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF14.x14 in s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13 and ((res = i3214 and no s-QF14.x1-QF14.x2-QF14.x3-QF14.x4-QF14.x5-QF14.x6-QF14.x7-QF14.x8-QF14.x9-QF14.x10-QF14.x11-QF14.x12-QF14.x13-QF14.x14)
	))))))))))))))))))))))))))))
}
one sig QF15 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize15[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF15.x14 in s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13 and ((res = i3214 and no s-QF15.x1-QF15.x2-QF15.x3-QF15.x4-QF15.x5-QF15.x6-QF15.x7-QF15.x8-QF15.x9-QF15.x10-QF15.x11-QF15.x12-QF15.x13-QF15.x14)
	))))))))))))))))))))))))))))
}
one sig QF16 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize16[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF16.x14 in s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13 and ((res = i3214 and no s-QF16.x1-QF16.x2-QF16.x3-QF16.x4-QF16.x5-QF16.x6-QF16.x7-QF16.x8-QF16.x9-QF16.x10-QF16.x11-QF16.x12-QF16.x13-QF16.x14)
	))))))))))))))))))))))))))))
}
one sig QF17 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize17[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF17.x14 in s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13 and ((res = i3214 and no s-QF17.x1-QF17.x2-QF17.x3-QF17.x4-QF17.x5-QF17.x6-QF17.x7-QF17.x8-QF17.x9-QF17.x10-QF17.x11-QF17.x12-QF17.x13-QF17.x14)
	))))))))))))))))))))))))))))
}
one sig QF18 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize18[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF18.x14 in s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13 and ((res = i3214 and no s-QF18.x1-QF18.x2-QF18.x3-QF18.x4-QF18.x5-QF18.x6-QF18.x7-QF18.x8-QF18.x9-QF18.x10-QF18.x11-QF18.x12-QF18.x13-QF18.x14)
	))))))))))))))))))))))))))))
}
one sig QF19 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize19[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF19.x14 in s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13 and ((res = i3214 and no s-QF19.x1-QF19.x2-QF19.x3-QF19.x4-QF19.x5-QF19.x6-QF19.x7-QF19.x8-QF19.x9-QF19.x10-QF19.x11-QF19.x12-QF19.x13-QF19.x14)
	))))))))))))))))))))))))))))
}
one sig QF110 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize110[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF110.x14 in s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13 and ((res = i3214 and no s-QF110.x1-QF110.x2-QF110.x3-QF110.x4-QF110.x5-QF110.x6-QF110.x7-QF110.x8-QF110.x9-QF110.x10-QF110.x11-QF110.x12-QF110.x13-QF110.x14)
	))))))))))))))))))))))))))))
}
one sig QF111 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize111[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF111.x14 in s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13 and ((res = i3214 and no s-QF111.x1-QF111.x2-QF111.x3-QF111.x4-QF111.x5-QF111.x6-QF111.x7-QF111.x8-QF111.x9-QF111.x10-QF111.x11-QF111.x12-QF111.x13-QF111.x14)
	))))))))))))))))))))))))))))
}
one sig QF112 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize112[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF112.x14 in s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13 and ((res = i3214 and no s-QF112.x1-QF112.x2-QF112.x3-QF112.x4-QF112.x5-QF112.x6-QF112.x7-QF112.x8-QF112.x9-QF112.x10-QF112.x11-QF112.x12-QF112.x13-QF112.x14)
	))))))))))))))))))))))))))))
}
one sig QF113 { x1:FibHeapIntVarNode,x2:FibHeapIntVarNode,x3:FibHeapIntVarNode,x4:FibHeapIntVarNode,x5:FibHeapIntVarNode,x6:FibHeapIntVarNode,x7:FibHeapIntVarNode,x8:FibHeapIntVarNode,x9:FibHeapIntVarNode,x10:FibHeapIntVarNode,x11:FibHeapIntVarNode,x12:FibHeapIntVarNode,x13:FibHeapIntVarNode,x14:FibHeapIntVarNode }

pred mysize113[s: set FibHeapIntVarNode, res: JavaPrimitiveIntegerValue] {
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
	 (QF113.x14 in s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13 and ((res = i3214 and no s-QF113.x1-QF113.x2-QF113.x3-QF113.x4-QF113.x5-QF113.x6-QF113.x7-QF113.x8-QF113.x9-QF113.x10-QF113.x11-QF113.x12-QF113.x13-QF113.x14)
	))))))))))))))))))))))))))))
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 FibHeapIntVar, exactly 14 FibHeapIntVarNode, 1 int, exactly 15 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) {
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
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) {
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
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) {
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
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) {
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
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N6->(N7+N8+N9+N10+N11+N12+N13)
   +
   N7->(N8+N9+N10+N11+N12+N13)
   +
   N8->(N9+N10+N11+N12+N13)
   +
   N9->(N10+N11+N12+N13)
   +
   N10->(N11+N12+N13)
   +
   N11->(N12+N13)
   +
   N12->(N13)
 )
}




